/*
 * Copyright 2014–2017 SlamData Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package quasar.regression

import slamdata.Predef._
import quasar.RenderTree.ops._
import quasar.contrib.argonaut._
import quasar.fp._

import scala.None
import scala.Predef.$conforms

import argonaut._, Argonaut._
import matryoshka._
import org.specs2.execute._
import org.specs2.matcher._
import scalaz.{Failure => _, _}, Scalaz._
import scalaz.stream._
import quasar.ScalazSpecs2Instances

sealed abstract class Predicate {
  def apply[F[_]: Catchable: Monad](
    expected: Vector[Json],
    actual: Process[F, Json],
    fieldOrder: OrderSignificance,
    resultOrder: OrderSignificance
  ): F[Result]
}

object Predicate extends ScalazSpecs2Instances {
  import MustMatchers._
  import StandardResults._
  import DecodeResult.{ok => jok, fail => jfail}

  def doesntMatch[S <: Option[Json]](actual: Json, expected: Json): String = {
    val diff = actual.render.diff(expected.render).shows
    s"Actual result does not match expected value. \n\n Diff: \n $diff \n\n"
  }

  def matchJson(expected: Option[Json]): Matcher[Option[Json]] = new Matcher[Option[Json]] {
    def apply[S <: Option[Json]](s: Expectable[S]) = {
      (expected, s.value) match {
        case (Some(expected), Some(actual)) =>
          (actual.obj |@| expected.obj) { (actualObj, expectedObj) =>
            if (actualObj.toList == expectedObj.toList)
              success(s"matches $expected", s)
            else if (actualObj == expectedObj)
              failure(s"$actual matches $expected, but order differs", s)
            else failure(doesntMatch(actual, expected), s)
          } getOrElse result(actual == expected, s"matches $expected", doesntMatch(actual, expected), s)
        case (Some(v), None)  => failure(s"ran out before expected; missing: ${v}", s)
        case (None, Some(v))  => failure(s"had more than expected: ${v}", s)
        case (None, None)     => success(s"matches (empty)", s)
        case _                => failure(s"scalac is weird", s)
      }
    }
  }

  /** Must contain ALL the elements. */
  final case object AtLeast extends Predicate {
    def apply[F[_]: Catchable: Monad](
      expected0: Vector[Json],
      actual0: Process[F, Json],
      fieldOrder: OrderSignificance,
      resultOrder: OrderSignificance
    ): F[Result] = resultOrder match {
      case OrderPreserved =>
        // FIXME: This case is the same as `Exactly`, but shouldn’t be.
        val actual   = actual0.map(Some(_))
        val expected = Process.emitAll(expected0).map(Some(_))

        (actual tee expected)(tee.zipAll(None, None))
          .flatMap {
            case (a, e) if jsonMatches(a, e) =>
              Process.halt
            case (a, e) if (a == e && fieldOrder ≟ OrderIgnored) =>
              Process.halt
            case (a, e) =>
              Process.emit(a must matchJson(e) : Result)
          }
          .runLog.map(_.foldMap()(Result.ResultMonoid))
      case OrderIgnored =>
        actual0.scan((expected0.toSet, Set.empty[Json])) {
          case ((expected, wrongOrder), e) =>
            expected.find(_ == e) match {
              case Some(e1) if jsonMatches(e1, e) =>
                (expected.filterNot(_ == e), wrongOrder)
              case Some(_) =>
                (expected.filterNot(_ == e), wrongOrder + e)
              case None =>
                (expected, wrongOrder)
            }
        }
          .runLast
          .map {
            case Some((exp, wrongOrder)) =>
              (exp aka "unmatched expected values" must beEmpty) and
                (wrongOrder aka "matched but field order differs" must beEmpty)
                .unless(fieldOrder ≟ OrderIgnored): Result
            case None =>
              failure
          }
    }
  }

  /** Must ALL and ONLY the elements. */
  final case object Exactly extends Predicate {
    def apply[F[_]: Catchable: Monad](
      expected0: Vector[Json],
      actual0: Process[F, Json],
      fieldOrder: OrderSignificance,
      resultOrder: OrderSignificance
    ): F[Result] = resultOrder match {
      case OrderPreserved =>
        val actual   = actual0.map(Some(_))
        val expected = Process.emitAll(expected0).map(Some(_))

        (actual tee expected)(tee.zipAll(None, None))
          .flatMap {
            case (a, e) if jsonMatches(a, e) =>
              Process.halt
            case (a, e) if (a == e && fieldOrder ≟ OrderIgnored) =>
              Process.halt
            case (a, e) =>
              Process.emit(a must matchJson(e) : Result)
          }
          .runLog.map(_.foldMap()(Result.ResultMonoid))
      case OrderIgnored =>
        actual0.scan((expected0, Vector.empty[Json], None: Option[Json])) {
          case ((expected, wrongOrder, extra), e) =>
            expected.indexOf(e) match {
              case -1 =>
                (expected, wrongOrder, extra.orElse(e.some))
              case k if jsonMatches(expected(k), e) =>
                (deleteAt(k, expected), wrongOrder, extra)
              case k =>
                (deleteAt(k, expected), wrongOrder :+ e, extra)
            }
        }
          .runLast
          .map {
            case Some((exp, wrongOrder, extra)) =>
              (extra must beNone.setMessage("unexpected value " + ~extra.map(_.toString))) and
                (wrongOrder aka "matched but field order differs" must beEmpty)
                .unless(fieldOrder ≟ OrderIgnored) and
                (exp aka "unmatched expected values" must beEmpty): Result
            case None =>
              failure
          }
    }

    // Removes the element at `idx` from `as`.
    private def deleteAt[A](idx: Int, as: Vector[A]): Vector[A] =
      as.patch(idx, Nil, 1)
  }

  /** Must START WITH the elements, in order. */
  final case object Initial extends Predicate {
    def apply[F[_]: Catchable: Monad](
      expected0: Vector[Json],
      actual0: Process[F, Json],
      fieldOrder: OrderSignificance,
      resultOrder: OrderSignificance
    ): F[Result] = resultOrder match {
      case OrderPreserved =>
        val actual   = actual0.map(Some(_))
        val expected = Process.emitAll(expected0).map(Some(_))

        (actual tee expected)(tee.zipAll(None, None))
          .flatMap {
            case (a, None) =>
              Process.halt
            case (a, e) if (jsonMatches(a, e)) =>
              Process.halt
            case (a, e) if (a == e && fieldOrder ≟ OrderIgnored) =>
              Process.halt
            case (a, e) =>
              Process.emit(a must matchJson(e) : Result)
          }
          .runLog.map(_.foldMap()(Result.ResultMonoid))
      case OrderIgnored =>
        AtLeast(expected0, actual0, fieldOrder, resultOrder)
    }
  }

  /** Must NOT contain ANY of the elements. */
  final case object DoesNotContain extends Predicate {
    def apply[F[_]: Catchable: Monad](
      expected0: Vector[Json],
      actual: Process[F, Json],
      fieldOrder: OrderSignificance,
      resultOrder: OrderSignificance
    ): F[Result] = {
      val expected = expected0.toSet

      if (expected.isEmpty)
        actual.drain.run.as(failure)
      else
        actual.scan(expected) { case (exp, e) =>
          // NB: want to ignore field-order here
          exp.filterNot(_ == e)
        }
        .dropWhile(_.size ≟ expected.size)
        .take(1)
        .map(unseen => expected.filterNot(unseen contains _) aka "prohibited values" must beEmpty : Result)
        .runLastOr(success)
    }
  }

  private def jsonMatches(j1: Json, j2: Json): Boolean =
    (j1.obj.map(_.toList) |@| j2.obj.map(_.toList))(_ == _) getOrElse (j1 == j2)

  private def jsonMatches(j1: Option[Json], j2: Option[Json]): Boolean =
    (j1 |@| j2)(jsonMatches) getOrElse false

  implicit val PredicateDecodeJson: DecodeJson[Predicate] =
    DecodeJson(c => c.as[String].flatMap {
      case "atLeast"        => jok(AtLeast)
      case "exactly"        => jok(Exactly)
      case "doesNotContain" => jok(DoesNotContain)
      case "initial"        => jok(Initial)
      case str              => jfail("Expected one of: atLeast, exactly, doesNotContain, initial, but found: " + str, c.history)
    })
}
