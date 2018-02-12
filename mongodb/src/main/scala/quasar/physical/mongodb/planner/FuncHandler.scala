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

package quasar.physical.mongodb.planner

import slamdata.Predef._
import quasar.physical.mongodb.{Bson, BsonCodec, BsonVersion}
import quasar.physical.mongodb.expression._
import quasar.qscript.{MapFuncsDerived => D,  _}, MapFuncsCore._
import quasar.qscript.rewrites.{Coalesce => _}

import matryoshka._
import matryoshka.data._
import matryoshka.implicits._
import matryoshka.patterns._
import scalaz.{Divide => _, Split => _, _}, Scalaz._
import simulacrum.typeclass

@typeclass trait FuncHandler[IN[_]] {

  def handleOpsCore[EX[_]: Functor](v: BsonVersion)
    (implicit e32: ExprOpCoreF :<: EX)
      : IN ~> OptionFree[EX, ?]

  def handleOps3_4[EX[_]: Functor](v: BsonVersion)
    (implicit e32: ExprOpCoreF :<: EX, e34: ExprOp3_4F :<: EX)
      : IN ~> OptionFree[EX, ?]

  def handleOps3_4_4[EX[_]: Functor](v: BsonVersion)
    (implicit e32: ExprOpCoreF :<: EX, e34: ExprOp3_4F :<: EX, e344: ExprOp3_4_4F :<: EX)
      : IN ~> OptionFree[EX, ?]

  def handle3_2(v: BsonVersion)
     : IN ~> OptionFree[Expr3_2, ?] =
    λ[IN ~> OptionFree[Expr3_2, ?]]{f =>
      val h = handleOpsCore[Expr3_2](v)
      h(f)
    }

  def handle3_4(v: BsonVersion)
     : IN ~> OptionFree[Expr3_4, ?] =
    λ[IN ~> OptionFree[Expr3_4, ?]]{f =>
      val h34 = handleOps3_4[Expr3_4](v)
      val h = handleOpsCore[Expr3_4](v)
      h34(f) orElse h(f)
    }

  def handle3_4_4(v: BsonVersion)
     : IN ~> OptionFree[Expr3_4_4, ?] =
    λ[IN ~> OptionFree[Expr3_4_4, ?]]{f =>
      val h344 = handleOps3_4_4[Expr3_4_4](v)
      val h34 = handleOps3_4[Expr3_4_4](v)
      val h = handleOpsCore[Expr3_4_4](v)
      h344(f) orElse h34(f) orElse h(f)
    }
}

object FuncHandler {

  implicit def mapFuncCore[T[_[_]]: BirecursiveT]: FuncHandler[MapFuncCore[T, ?]] =
    new FuncHandler[MapFuncCore[T, ?]] {

      def handleOpsCore[EX[_]: Functor]
        (v: BsonVersion)
        (implicit e32: ExprOpCoreF :<: EX)
          : MapFuncCore[T, ?] ~> OptionFree[EX, ?] =
        new (MapFuncCore[T, ?] ~> OptionFree[EX, ?]) {

          implicit def hole[D](d: D): Free[EX, D] = Free.pure(d)

          def apply[A](mfc: MapFuncCore[T, A]): OptionFree[EX, A] = {

            val fp = new ExprOpCoreF.fixpoint[Free[EX, A], EX](Free.roll)
            import fp._
            import FormatSpecifier._

            def partial(mfc: MapFuncCore[T, A]): OptionFree[EX, A] = mfc.some collect {
              case Undefined()           => $literal(Bson.Undefined)
              case Add(a1, a2)           => $add(a1, a2)
              case Multiply(a1, a2)      => $multiply(a1, a2)
              case Subtract(a1, a2)      => $subtract(a1, a2)
              case Divide(a1, a2)        =>
                // NB: It’s apparently intential that division by zero crashes
                //     the query in MongoDB. See
                //     https://jira.mongodb.org/browse/SERVER-29410
                // TODO: It would be nice if we would be able to generate simply
                //       $divide(a1, a2) for $literal denominators, but the type
                //       of a2 is generic so we can't check it here.
                $cond($eq(a2, $literal(Bson.Int32(0))),
                  $cond($eq(a1, $literal(Bson.Int32(0))),
                    $literal(Bson.Dec(Double.NaN)),
                    $cond($gt(a1, $literal(Bson.Int32(0))),
                      $literal(Bson.Dec(Double.PositiveInfinity)),
                      $literal(Bson.Dec(Double.NegativeInfinity)))),
                  $divide(a1, a2))
              case Modulo(a1, a2)        => $mod(a1, a2)
              case Negate(a1)            => $multiply($literal(Bson.Int32(-1)), a1)
              case MapFuncsCore.Eq(a1, a2)   => $eq(a1, a2)
              case Neq(a1, a2)           => $neq(a1, a2)
              case Lt(a1, a2)            => $lt(a1, a2)
              case Lte(a1, a2)           => $lte(a1, a2)
              case Gt(a1, a2)            => $gt(a1, a2)
              case Gte(a1, a2)           => $gte(a1, a2)

              // FIXME: this is valid for strings only

              case Lower(a1)             => $toLower(a1)
              case Upper(a1)             => $toUpper(a1)
              case Substring(a1, a2, a3) => $substr(a1, a2, a3)
              case Cond(a1, a2, a3)      => $cond(a1, a2, a3)

              case Or(a1, a2)            => $or(a1, a2)
              case And(a1, a2)           => $and(a1, a2)
              case Not(a1)               => $not(a1)

              case Null(a1) =>
                $cond($eq(a1, $literal(Bson.Text("null"))),
                  $literal(Bson.Null),
                  $literal(Bson.Undefined))

              case Bool(a1) =>
                $cond($eq(a1, $literal(Bson.Text("true"))),
                  $literal(Bson.Bool(true)),
                  $cond($eq(a1, $literal(Bson.Text("false"))),
                    $literal(Bson.Bool(false)),
                    $literal(Bson.Undefined)))

              case ExtractCentury(a1) =>
                $trunc($divide($add($year(a1), $literal(Bson.Int32(99))), $literal(Bson.Int32(100))))
              case ExtractDayOfMonth(a1) => $dayOfMonth(a1)
              case ExtractDecade(a1) => $trunc($divide($year(a1), $literal(Bson.Int32(10))))
              case ExtractDayOfWeek(a1) => $subtract($dayOfWeek(a1), $literal(Bson.Int32(1)))
              case ExtractDayOfYear(a1) => $dayOfYear(a1)
              case ExtractEpoch(a1) =>
                $divide(
                  $subtract(a1, $literal(Bson.Date(0))),
                  $literal(Bson.Int32(1000)))
              case ExtractHour(a1) => $hour(a1)
              case ExtractIsoDayOfWeek(a1) =>
                $cond($eq($dayOfWeek(a1), $literal(Bson.Int32(1))),
                  $literal(Bson.Int32(7)),
                  $subtract($dayOfWeek(a1), $literal(Bson.Int32(1))))
              // TODO: case ExtractIsoYear(a1) =>
              case ExtractMicroseconds(a1) =>
                $multiply(
                  $add(
                    $multiply($second(a1), $literal(Bson.Int32(1000))),
                    $millisecond(a1)),
                  $literal(Bson.Int32(1000)))
              case ExtractMillennium(a1) =>
                $trunc($divide($add($year(a1), $literal(Bson.Int32(999))), $literal(Bson.Int32(1000))))
              case ExtractMilliseconds(a1) =>
                $add(
                  $multiply($second(a1), $literal(Bson.Int32(1000))),
                  $millisecond(a1))
              case ExtractMinute(a1) => $minute(a1)
              case ExtractMonth(a1) => $month(a1)
              case ExtractQuarter(a1) =>
                $trunc(
                  $add(
                    $divide(
                      $subtract($month(a1), $literal(Bson.Int32(1))),
                      $literal(Bson.Int32(3))),
                    $literal(Bson.Int32(1))))
              case ExtractSecond(a1) =>
                $add($second(a1), $divide($millisecond(a1), $literal(Bson.Int32(1000))))
              case ExtractWeek(a1) => $week(a1)
              case ExtractYear(a1) => $year(a1)

              case ToTimestamp(a1) =>
               $add($literal(Bson.Date(0)), a1)

              case Between(a1, a2, a3)   => $and($lte(a2, a1), $lte(a1, a3))
              case TimeOfDay(a1) =>
                $dateToString(Hour :: ":" :: Minute :: ":" :: Second :: "." :: Millisecond :: FormatString.empty, a1)
              case Power(a1, a2) => $pow(a1, a2)
              case ProjectIndex(a1, a2) => $arrayElemAt(a1, a2)
              case MakeArray(a1) => $arrayLit(List(a1))
              case ConcatArrays(a1, a2) =>
                $let(ListMap(DocVar.Name("a1") -> a1, DocVar.Name("a2") -> a2),
                  $cond($and($isArray($field("$a1")), $isArray($field("$a2"))),
                    $concatArrays(List($field("$a1"), $field("$a2"))),
                    $concat($field("$a1"), $field("$a2"))))
              case TypeOf(a1) => mkTypeOf(a1, $isArray)
            }

            partial(mfc) orElse (mfc match {
              case Constant(v1)  => v1.cataM(BsonCodec.fromEJson(v)).toOption.map($literal(_))
              case _             => None
            })
          }
        }

      def handleOps3_4[EX[_]: Functor](v: BsonVersion)
        (implicit e32: ExprOpCoreF :<: EX, e34: ExprOp3_4F :<: EX)
          : MapFuncCore[T, ?] ~> OptionFree[EX, ?] =
        new (MapFuncCore[T, ?] ~> OptionFree[EX, ?]){
          implicit def hole[D](d: D): Free[EX, D] = Free.pure(d)

          def apply[A](mfc: MapFuncCore[T, A]): OptionFree[EX, A] = {
            val fp32  = new ExprOpCoreF.fixpoint[Free[EX, A], EX](Free.roll)
            val fp34  = new ExprOp3_4F.fixpoint[Free[EX, A], EX](Free.roll)

            import fp32._, fp34._

            mfc.some collect {
              case Split(a1, a2) => $split(a1, a2)
              case Substring(a1, a2, a3) =>
                $cond($or(
                    $lt(a2, $literal(Bson.Int32(0))),
                    $gt(a2, $strLenCP(a1))),
                  $literal(Bson.Text("")),
                  $cond(
                    $lt(a3, $literal(Bson.Int32(0))),
                    $substrCP(a1, a2, $strLenCP(a1)),
                    $substrCP(a1, a2, a3)))
              case Length(a1) => $strLenCP(a1)
            }
          }
        }

      def handleOps3_4_4[EX[_]: Functor](v: BsonVersion)
        (implicit e32: ExprOpCoreF :<: EX, e34: ExprOp3_4F :<: EX, e344: ExprOp3_4_4F :<: EX)
          : MapFuncCore[T, ?] ~> OptionFree[EX, ?] =
        new (MapFuncCore[T, ?] ~> OptionFree[EX, ?]){

          def apply[A](mfc: MapFuncCore[T, A]): OptionFree[EX, A] = None
        }

    }

  def mapFuncDerived[T[_[_]]: CorecursiveT]
      : FuncHandler[MapFuncDerived[T, ?]] =
    new FuncHandler[MapFuncDerived[T, ?]] {
      def emptyDerived[T[_[_]], F[_]]: MapFuncDerived[T, ?] ~> OptionFree[F, ?] =
         λ[MapFuncDerived[T, ?] ~> OptionFree[F, ?]] { _ => None }

      def handleOpsCore[EX[_]: Functor](v: BsonVersion)
        (implicit e32: ExprOpCoreF :<: EX)
          : MapFuncDerived[T, ?] ~> OptionFree[EX, ?] =
        new (MapFuncDerived[T, ?] ~> OptionFree[EX, ?]){
          implicit def hole[D](d: D): Free[EX, D] = Free.pure(d)

          def apply[A](fa: MapFuncDerived[T, A]): OptionFree[EX, A] = {
            val fp = new ExprOpCoreF.fixpoint[Free[EX, A], EX](Free.roll)
            import fp._

            fa.some collect {
              case D.Abs(a1)       => $abs(a1)
              case D.Ceil(a1)      => $ceil(a1)
              case D.Floor(a1)     => $floor(a1)
              case D.Trunc(a1)     => $trunc(a1)
            }
          }
        }

      def handleOps3_4[EX[_]: Functor](v: BsonVersion)
        (implicit e32: ExprOpCoreF :<: EX, e34: ExprOp3_4F :<: EX)
          : MapFuncDerived[T, ?] ~> OptionFree[EX, ?] =
        emptyDerived

      def handleOps3_4_4[EX[_]: Functor](v: BsonVersion)
        (implicit e32: ExprOpCoreF :<: EX, e34: ExprOp3_4F :<: EX, e344: ExprOp3_4_4F :<: EX)
          : MapFuncDerived[T, ?] ~> OptionFree[EX, ?] =
        emptyDerived
    }

  implicit def mapFuncDerivedUnhandled[T[_[_]]: CorecursiveT]
    (implicit core: FuncHandler[MapFuncCore[T, ?]])
      : FuncHandler[MapFuncDerived[T, ?]] =
    new FuncHandler[MapFuncDerived[T, ?]] {
      val derived = mapFuncDerived

      private def handleUnhandled[F[_]]
        (derived: MapFuncDerived[T, ?] ~> OptionFree[F, ?], core: MapFuncCore[T, ?] ~> OptionFree[F, ?])
          : MapFuncDerived[T, ?] ~> OptionFree[F, ?] =
            new (MapFuncDerived[T, ?] ~> OptionFree[F, ?]) {
              def apply[A](f: MapFuncDerived[T, A]): OptionFree[F, A] = {
                val alg: AlgebraM[Option, CoEnv[A, MapFuncCore[T,?], ?], Free[F,A]] =
                  _.run.fold[OptionFree[F, A]](x => Free.point(x).some, core(_).map(_.join))
                derived(f)
                  .orElse(Free.roll(ExpandMapFunc.mapFuncDerived[T, MapFuncCore[T, ?]].expand(f)).cataM(alg))
            }
          }

      def handleOpsCore[EX[_]: Functor](v: BsonVersion)
        (implicit e32: ExprOpCoreF :<: EX)
          : MapFuncDerived[T, ?] ~> OptionFree[EX, ?] =
        handleUnhandled(derived.handleOpsCore(v), core.handleOpsCore(v))

      def handleOps3_4[EX[_]: Functor](v: BsonVersion)
        (implicit e32: ExprOpCoreF :<: EX, e34: ExprOp3_4F :<: EX)
          : MapFuncDerived[T, ?] ~> OptionFree[EX, ?] = {

        val hCore = λ[MapFuncCore[T, ?] ~> OptionFree[EX, ?]]{f =>
          val h34 = core.handleOps3_4[EX](v)
          val h = core.handleOpsCore[EX](v)
          h34(f) orElse h(f)
        }
        handleUnhandled(derived.handleOps3_4(v), hCore)
      }

      def handleOps3_4_4[EX[_]: Functor](v: BsonVersion)
        (implicit e32: ExprOpCoreF :<: EX, e34: ExprOp3_4F :<: EX, e344: ExprOp3_4_4F :<: EX)
          : MapFuncDerived[T, ?] ~> OptionFree[EX, ?] = {

        val hCore = λ[MapFuncCore[T, ?] ~> OptionFree[EX, ?]]{f =>
          val h344 = core.handleOps3_4_4[EX](v)
          val h34 = core.handleOps3_4[EX](v)
          val h = core.handleOpsCore[EX](v)
          h344(f) orElse h34(f) orElse h(f)
        }
        handleUnhandled(derived.handleOps3_4_4(v), hCore)
      }
    }

  implicit def mapFuncCoproduct[F[_], G[_]]
      (implicit F: FuncHandler[F], G: FuncHandler[G])
      : FuncHandler[Coproduct[F, G, ?]] =
    new FuncHandler[Coproduct[F, G, ?]] {
      def handleOpsCore[EX[_]: Functor](v: BsonVersion)
        (implicit e32: ExprOpCoreF :<: EX)
          : Coproduct[F, G, ?] ~> OptionFree[EX, ?] =
        λ[Coproduct[F, G, ?] ~> OptionFree[EX, ?]](_.run.fold(
          F.handleOpsCore[EX](v).apply _,
          G.handleOpsCore[EX](v).apply _
        ))

      def handleOps3_4[EX[_]: Functor](v: BsonVersion)
        (implicit e32: ExprOpCoreF :<: EX, e34: ExprOp3_4F :<: EX)
          : Coproduct[F, G, ?] ~> OptionFree[EX, ?] =
        λ[Coproduct[F, G, ?] ~> OptionFree[EX, ?]](_.run.fold(
          F.handleOps3_4[EX](v).apply _,
          G.handleOps3_4[EX](v).apply _
        ))

      def handleOps3_4_4[EX[_]: Functor](v: BsonVersion)
        (implicit e32: ExprOpCoreF :<: EX, e34: ExprOp3_4F :<: EX, e344: ExprOp3_4_4F :<: EX)
          : Coproduct[F, G, ?] ~> OptionFree[EX, ?] =
        λ[Coproduct[F, G, ?] ~> OptionFree[EX, ?]](_.run.fold(
          F.handleOps3_4_4[EX](v).apply _,
          G.handleOps3_4_4[EX](v).apply _
        ))

    }

  def handle3_2[F[_]: FuncHandler](v: BsonVersion): F ~> OptionFree[Expr3_2, ?] =
    FuncHandler[F].handle3_2(v)

  def handle3_4[F[_]: FuncHandler](v: BsonVersion): F ~> OptionFree[Expr3_4, ?] =
    FuncHandler[F].handle3_4(v)

  def handle3_4_4[F[_]: FuncHandler](v: BsonVersion): F ~> OptionFree[Expr3_4_4, ?] =
    FuncHandler[F].handle3_4_4(v)
}
