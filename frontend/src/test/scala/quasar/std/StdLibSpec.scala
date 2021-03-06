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

package quasar.std

import slamdata.Predef._, BigDecimal.RoundingMode
import quasar.{Data, DataCodec, Qspec, Type}
import quasar.DateArbitrary._
import quasar.frontend.logicalplan._

import java.time._, ZoneOffset.UTC
import scala.collection.Traversable
import scala.math.abs
import scala.util.matching.Regex

import matryoshka.data.Fix
import matryoshka.implicits._
import org.specs2.execute.{Failure, Result}
import org.specs2.matcher.{Expectable, Matcher}
import org.specs2.specification.core.Fragment
import org.scalacheck.{Arbitrary, Gen}
import scalaz._, Scalaz._

/** Abstract spec for the standard library, intended to be implemented for each
  * library implementation, of which there are one or more per backend.
  */
abstract class StdLibSpec extends Qspec {
  def isPrintableAscii(c: Char): Boolean = c >= '\u0020' && c <= '\u007e'
  def isPrintableAscii(s: String): Boolean = s.forall(isPrintableAscii)

  def beCloseTo(expected: Data): Matcher[Data] = new Matcher[Data] {
    def isClose(x: BigDecimal, y: BigDecimal, err: Double): Boolean =
      x == y || ((x - y).abs/(y.abs max err)).toDouble < err

    def apply[S <: Data](s: Expectable[S]) = {
      val v = s.value
      (v, expected) match {
        case (Data.Number(x), Data.Number(exp)) =>
          result(isClose(x, exp, 1e-9),
            s"$x is a Number and matches $exp",
            s"$x is a Number but does not match $exp", s)
        case _ =>
          result(Equal[Data].equal(v, expected),
            s"$v matches $expected",
            s"$v does not match $expected", s)
      }
    }
  }

  def tests(runner: StdLibTestRunner): Fragment = {
    import runner._

    implicit val arbBigInt = Arbitrary[BigInt] { runner.intDomain }
    implicit val arbBigDecimal = Arbitrary[BigDecimal] { runner.decDomain }
    implicit val arbString = Arbitrary[String] { runner.stringDomain }
    implicit val arbDate = Arbitrary[LocalDate] { runner.dateDomain }
    implicit val arbData = Arbitrary[Data] {
      Gen.oneOf(
        runner.intDomain.map(Data.Int(_)),
        runner.decDomain.map(Data.Dec(_)),
        runner.stringDomain.map(Data.Str(_)))
    }

    def commute(
        prg: (Fix[LogicalPlan], Fix[LogicalPlan]) => Fix[LogicalPlan],
        arg1: Data, arg2: Data,
        expected: Data): Result =
      binary(prg, arg1, arg2, expected) and
        binary(prg, arg2, arg1, expected)

    "StringLib" >> {
      import StringLib._

      "Concat" >> {
        "any strings" >> prop { (str1: String, str2: String) =>
          binary(Concat(_, _).embed, Data.Str(str1), Data.Str(str2), Data.Str(str1 + str2))
        }
      }

      // NB: `Like` is simplified to `Search`

      "Search" >> {
        "find contents within string when case sensitive" >> {
          ternary(Search(_, _, _).embed, Data.Str("church"), Data.Str(".*ch.*"), Data.Bool(false), Data.Bool(true)) and
            ternary(Search(_, _, _).embed, Data.Str("China"), Data.Str("^Ch.*$"), Data.Bool(false), Data.Bool(true)) and
            ternary(Search(_, _, _).embed, Data.Str("matching"), Data.Str(".*ch.*"), Data.Bool(false), Data.Bool(true))
        }

        "reject a non-matching string when case sensitive" >> {
          ternary(Search(_, _, _).embed, Data.Str("church"), Data.Str("^bs.*$"), Data.Bool(false), Data.Bool(false)) and
            ternary(Search(_, _, _).embed, Data.Str("china"), Data.Str("^bs.*$"), Data.Bool(false), Data.Bool(false)) and
            ternary(Search(_, _, _).embed, Data.Str("matching"), Data.Str(".*bs.*"), Data.Bool(false), Data.Bool(false)) and
            ternary(Search(_, _, _).embed, Data.Str("matching"), Data.Str(".*CH.*"), Data.Bool(false), Data.Bool(false))
        }

        "find contents within string when case insensitive" >> {
          ternary(Search(_, _, _).embed, Data.Str("Church"), Data.Str(".*ch.*"), Data.Bool(true), Data.Bool(true)) and
            ternary(Search(_, _, _).embed, Data.Str("cHina"), Data.Str("^ch.*$"), Data.Bool(true), Data.Bool(true)) and
            ternary(Search(_, _, _).embed, Data.Str("matCHing"), Data.Str(".*ch.*"), Data.Bool(true), Data.Bool(true))
        }

        "reject a non-matching string when case insensitive" >> {
          ternary(Search(_, _, _).embed, Data.Str("Church"), Data.Str("^bs.*$"), Data.Bool(true), Data.Bool(false)) and
            ternary(Search(_, _, _).embed, Data.Str("cHina"), Data.Str("^bs.*$"), Data.Bool(true), Data.Bool(false)) and
            ternary(Search(_, _, _).embed, Data.Str("matCHing"), Data.Str(".*bs.*"), Data.Bool(true), Data.Bool(false))
        }
      }

      "Length" >> {
        "multibyte chars" >> {
          unary(Length(_).embed, Data.Str("€1"), Data.Int(2))
        }
        "any string" >> prop { (str: String) =>
          unary(Length(_).embed, Data.Str(str), Data.Int(str.length))
        }
      }

      "Lower" >> {
        "any string" >> prop { (str: String) =>
          unary(Lower(_).embed, Data.Str(str), Data.Str(str.toLowerCase))
        }
      }

      "Upper" >> {
        "any string" >> prop { (str: String) =>
          unary(Upper(_).embed, Data.Str(str), Data.Str(str.toUpperCase))
        }
      }

      "Substring" >> {
        "simple" >> {
          // NB: not consistent with PostgreSQL, which is 1-based for `start`
          ternary(Substring(_, _, _).embed, Data.Str("Thomas"), Data.Int(1), Data.Int(3), Data.Str("hom"))
        }

        "multibyte chars" >> {
          ternary(Substring(_, _, _).embed, Data.Str("cafétéria"), Data.Int(3), Data.Int(1), Data.Str("é"))
        }

        "empty string and any offsets" >> prop { (start0: Int, length0: Int) =>
          // restrict the range to something that will actually exercise the behavior
          val start = start0 % 1000
          val length = length0 % 1000
          ternary(Substring(_, _, _).embed, Data.Str(""), Data.Int(start), Data.Int(length), Data.Str(""))
        }

        "any string with entire range" >> prop { (str: String) =>
          ternary(Substring(_, _, _).embed, Data.Str(str), Data.Int(0), Data.Int(str.length), Data.Str(str))
        }

        "any string with 0 length" >> prop { (str: String, start0: Int) =>
          // restrict the range to something that will actually exercise the behavior
          val start = start0 % 1000
          ternary(Substring(_, _, _).embed, Data.Str(str), Data.Int(start), Data.Int(0), Data.Str(""))
        }

        "any string and offsets" >> prop { (str: String, start0: Int, length0: Int) =>
          // restrict the range to something that will actually exercise the behavior
          val start = start0 % 1000
          val length = length0 % 1000

          // NB: this is the MongoDB behavior, for lack of a better idea
          val expected = StringLib.safeSubstring(str, start, length)
          ternary(Substring(_, _, _).embed, Data.Str(str), Data.Int(start), Data.Int(length), Data.Str(expected))
        }
      }

      "Split" >> {
        "some string" >> {
          binary(Split(_, _).embed, Data.Str("some string"), Data.Str(" "), Data.Arr(List("some", "string").map(Data.Str(_))))
        }
        "some string by itself" >> {
          binary(Split(_, _).embed, Data.Str("some string"), Data.Str("some string"), Data.Arr(List("", "").map(Data.Str(_))))
        }
        "any string not containing delimiter" >> prop { (s: String, d: String) =>
          (!d.isEmpty && !s.contains(d)) ==>
            binary(Split(_, _).embed, Data.Str(s), Data.Str(d), Data.Arr(List(Data.Str(s))))
        }
        "any string with non-empty delimiter" >> prop { (s: String, d: String) =>
          !d.isEmpty ==>
            binary(Split(_, _).embed, Data.Str(s), Data.Str(d), Data.Arr(s.split(Regex.quote(d), -1).toList.map(Data.Str(_))))
        }
      }

      "Boolean" >> {
        "true" >> {
          unary(Boolean(_).embed, Data.Str("true"), Data.Bool(true))
        }

        "false" >> {
          unary(Boolean(_).embed, Data.Str("false"), Data.Bool(false))
        }

        // TODO: how to express "should execute and may produce any result"
      }

      "Integer" >> {
        "any BigInt in the domain" >> prop { (x: BigInt) =>
          unary(Integer(_).embed, Data.Str(x.toString), Data.Int(x))
        }

        // TODO: how to express "should execute and may produce any result"
      }

      "Decimal" >> {
        "any BigDecimal in the domain" >> prop { (x: BigDecimal) =>
          unary(Decimal(_).embed, Data.Str(x.toString), Data.Dec(x))
        }

        // TODO: how to express "should execute and may produce any result"
      }

      "Null" >> {
        "null" >> {
          unary(Null(_).embed, Data.Str("null"), Data.Null)
        }

        // TODO: how to express "should execute and may produce any result"
      }

      "ToString" >> {
        "string" >> prop { (str: String) =>
          unary(ToString(_).embed, Data.Str(str), Data.Str(str))
        }

        "null" >> {
          unary(ToString(_).embed, Data.Null, Data.Str("null"))
        }

        "true" >> {
          unary(ToString(_).embed, Data.Bool(true), Data.Str("true"))
        }

        "false" >> {
          unary(ToString(_).embed, Data.Bool(false), Data.Str("false"))
        }

        "int" >> prop { (x: BigInt) =>
          unary(ToString(_).embed, Data.Int(x), Data.Str(x.toString))
        }

        // TODO: re-parse and compare the resulting value approximately. It's
        // not reasonable to expect a perfect match on formatted values,
        // because of trailing zeros, round-off, and choive of notation.
        // "dec" >> prop { (x: BigDecimal) =>
        //   unary(ToString(_).embed, Data.Dec(x), Data.Str(x.toString))
        // }

        "timestamp" >> {
          def test(x: Instant) = unary(
            ToString(_).embed,
            Data.Timestamp(x),
            Data.Str(x.atZone(UTC).format(DataCodec.dateTimeFormatter)))

          "zero fractional seconds" >> test(Instant.EPOCH)

          "any" >> prop (test(_: Instant))
        }

        "date" >> prop { (x: LocalDate) =>
          unary(ToString(_).embed, Data.Date(x), Data.Str(x.toString))
        }

        "time" >> {
          def test(x: LocalTime) = unary(
            ToString(_).embed,
            Data.Time(x),
            Data.Str(x.format(DataCodec.timeFormatter)))

          "zero fractional seconds" >> test(LocalTime.NOON)

          "any" >> prop (test(_: LocalTime))
        }

        // TODO: Enable
        // "interval" >> prop { (x: Duration) =>
        //   unary(ToString(_).embed, Data.Interval(x), Data.Str(x.toString))
        // }
      }
    }

    "DateLib" >> {
      import DateLib._

      "ExtractCentury" >> {
        "0001-01-01" >> {
          unary(ExtractCentury(_).embed, Data.Date(LocalDate.parse("0001-01-01")), Data.Int(1))
        }

        "2000-01-01" >> {
          unary(ExtractCentury(_).embed, Data.Date(LocalDate.parse("2000-01-01")), Data.Int(20))
        }

        "2001-01-01" >> {
          unary(ExtractCentury(_).embed, Data.Date(LocalDate.parse("2001-01-01")), Data.Int(21))
        }

        "midnight 0001-01-01" >> {
          unary(ExtractCentury(_).embed, Data.Timestamp(Instant.parse("0001-01-01T00:00:00.000Z")), Data.Int(1))
        }

        "midnight 2000-01-01" >> {
          unary(ExtractCentury(_).embed, Data.Timestamp(Instant.parse("2000-01-01T00:00:00.000Z")), Data.Int(20))
        }

        "midnight 2001-01-01" >> {
          unary(ExtractCentury(_).embed, Data.Timestamp(Instant.parse("2001-01-01T00:00:00.000Z")), Data.Int(21))
        }
      }

      "ExtractDayOfMonth" >> {
        "2016-01-01" >> {
          unary(ExtractDayOfMonth(_).embed, Data.Date(LocalDate.parse("2016-01-01")), Data.Int(1))
        }

        "midnight 2016-01-01" >> {
          unary(ExtractDayOfMonth(_).embed, Data.Timestamp(Instant.parse("2016-01-01T00:00:00.000Z")), Data.Int(1))
        }

        "2016-02-29" >> {
          unary(ExtractDayOfMonth(_).embed, Data.Date(LocalDate.parse("2016-02-29")), Data.Int(29))
        }

        "midnight 2016-02-29" >> {
          unary(ExtractDayOfMonth(_).embed, Data.Timestamp(Instant.parse("2016-02-29T00:00:00.000Z")), Data.Int(29))
        }
      }

      "ExtractDecade" >> {
        "1999-12-31" >> {
          unary(ExtractDecade(_).embed, Data.Date(LocalDate.parse("1999-12-31")), Data.Int(199))
        }

        "midnight 1999-12-31" >> {
          unary(ExtractDecade(_).embed, Data.Timestamp(Instant.parse("1999-12-31T00:00:00.000Z")), Data.Int(199))
        }
      }

      "ExtractDayOfWeek" >> {
        "2016-09-28" >> {
          unary(ExtractDayOfWeek(_).embed, Data.Date(LocalDate.parse("2016-09-28")), Data.Int(3))
        }

        "midnight 2016-09-28" >> {
          unary(ExtractDayOfWeek(_).embed, Data.Timestamp(Instant.parse("2016-09-28T00:00:00.000Z")), Data.Int(3))
        }

        "2016-10-02" >> {
          unary(ExtractDayOfWeek(_).embed, Data.Date(LocalDate.parse("2016-10-02")), Data.Int(0))
        }

        "midnight 2016-10-02" >> {
          unary(ExtractDayOfWeek(_).embed, Data.Timestamp(Instant.parse("2016-10-02T00:00:00.000Z")), Data.Int(0))
        }

        "2016-10-08" >> {
          unary(ExtractDayOfWeek(_).embed, Data.Date(LocalDate.parse("2016-10-08")), Data.Int(6))
        }

        "noon 2016-10-08" >> {
          unary(ExtractDayOfWeek(_).embed, Data.Timestamp(Instant.parse("2016-10-08T12:00:00.000Z")), Data.Int(6))
        }
      }

      "ExtractDayOfYear" >> {
        "2016-03-01" >> {
          unary(ExtractDayOfYear(_).embed, Data.Date(LocalDate.parse("2016-03-01")), Data.Int(61))
        }

        "midnight 2016-03-01" >> {
          unary(ExtractDayOfYear(_).embed, Data.Timestamp(Instant.parse("2016-03-01T00:00:00.000Z")), Data.Int(61))
        }

        "2017-03-01" >> {
          unary(ExtractDayOfYear(_).embed, Data.Date(LocalDate.parse("2017-03-01")), Data.Int(60))
        }

        "midnight 2017-03-01" >> {
          unary(ExtractDayOfYear(_).embed, Data.Timestamp(Instant.parse("2017-03-01T00:00:00.000Z")), Data.Int(60))
        }
      }

      "ExtractEpoch" >> {
        "2016-09-29" >> {
          unary(ExtractEpoch(_).embed, Data.Date(LocalDate.parse("2016-09-29")), Data.Dec(1475107200.0))
        }

        "2016-09-29 12:34:56.789" >> {
          unary(ExtractEpoch(_).embed, Data.Timestamp(Instant.parse("2016-09-29T12:34:56.789Z")), Data.Dec(1475152496.789))
        }
      }

      "ExtractHour" >> {
        "2016-09-29" >> {
          unary(ExtractHour(_).embed, Data.Date(LocalDate.parse("2016-09-29")), Data.Int(0))
        }

        "midnight 2016-09-29" >> {
          unary(ExtractHour(_).embed, Data.Timestamp(Instant.parse("2016-03-01T00:00:00.000Z")), Data.Int(0))
        }

        "2016-09-29 12:34:56.789" >> {
          unary(ExtractHour(_).embed, Data.Timestamp(Instant.parse("2016-03-01T12:34:56.789Z")), Data.Int(12))
        }
      }

      "ExtractIsoDayOfWeek" >> {
        "2016-09-28" >> {
          unary(ExtractIsoDayOfWeek(_).embed, Data.Date(LocalDate.parse("2016-09-28")), Data.Int(3))
        }

        "midnight 2016-09-28" >> {
          unary(ExtractIsoDayOfWeek(_).embed, Data.Timestamp(Instant.parse("2016-09-28T00:00:00.000Z")), Data.Int(3))
        }

        "2016-10-02" >> {
          unary(ExtractIsoDayOfWeek(_).embed, Data.Date(LocalDate.parse("2016-10-02")), Data.Int(7))
        }

        "midnight 2016-10-02" >> {
          unary(ExtractIsoDayOfWeek(_).embed, Data.Timestamp(Instant.parse("2016-10-02T00:00:00.000Z")), Data.Int(7))
        }
      }

      "ExtractIsoYear" >> {
        "2006-01-01" >> {
          unary(ExtractIsoYear(_).embed, Data.Date(LocalDate.parse("2006-01-01")), Data.Int(2005))
        }

        "midnight 2006-01-01" >> {
          unary(ExtractIsoYear(_).embed, Data.Timestamp(Instant.parse("2006-01-01T00:00:00.000Z")), Data.Int(2005))
        }

        "2006-01-02" >> {
          unary(ExtractIsoYear(_).embed, Data.Date(LocalDate.parse("2006-01-02")), Data.Int(2006))
        }

        "midnight 2006-01-02" >> {
          unary(ExtractIsoYear(_).embed, Data.Timestamp(Instant.parse("2006-01-02T00:00:00.000Z")), Data.Int(2006))
        }
      }

      "ExtractMicroseconds" >> {
        "2016-09-29" >> {
          unary(ExtractMicroseconds(_).embed, Data.Date(LocalDate.parse("2016-09-29")), Data.Dec(0))
        }

        "midnight 2016-09-29" >> {
          unary(ExtractMicroseconds(_).embed, Data.Timestamp(Instant.parse("2016-03-01T00:00:00.000Z")), Data.Dec(0))
        }

        "2016-09-29 12:34:56.789" >> {
          unary(ExtractMicroseconds(_).embed, Data.Timestamp(Instant.parse("2016-03-01T12:34:56.789Z")), Data.Dec(56.789e6))
        }
      }


      "ExtractMillennium" >> {
        "0001-01-01" >> {
          unary(ExtractMillennium(_).embed, Data.Date(LocalDate.parse("0001-01-01")), Data.Int(1))
        }

        "2000-01-01" >> {
          unary(ExtractMillennium(_).embed, Data.Date(LocalDate.parse("2000-01-01")), Data.Int(2))
        }

        "2001-01-01" >> {
          unary(ExtractMillennium(_).embed, Data.Date(LocalDate.parse("2001-01-01")), Data.Int(3))
        }

        "midnight 0001-01-01" >> {
          unary(ExtractMillennium(_).embed, Data.Timestamp(Instant.parse("0001-01-01T00:00:00.000Z")), Data.Int(1))
        }

        "midnight 2000-01-01" >> {
          unary(ExtractMillennium(_).embed, Data.Timestamp(Instant.parse("2000-01-01T00:00:00.000Z")), Data.Int(2))
        }

        "midnight 2001-01-01" >> {
          unary(ExtractMillennium(_).embed, Data.Timestamp(Instant.parse("2001-01-01T00:00:00.000Z")), Data.Int(3))
        }
      }

      "ExtractMilliseconds" >> {
        "2016-09-29" >> {
          unary(ExtractMilliseconds(_).embed, Data.Date(LocalDate.parse("2016-09-29")), Data.Dec(0))
        }

        "midnight 2016-09-29" >> {
          unary(ExtractMilliseconds(_).embed, Data.Timestamp(Instant.parse("2016-03-01T00:00:00.000Z")), Data.Dec(0))
        }

        "2016-09-29 12:34:56.789" >> {
          unary(ExtractMilliseconds(_).embed, Data.Timestamp(Instant.parse("2016-03-01T12:34:56.789Z")), Data.Dec(56.789e3))
        }
      }

      "ExtractMinute" >> {
        "2016-09-29" >> {
          unary(ExtractMinute(_).embed, Data.Date(LocalDate.parse("2016-09-29")), Data.Int(0))
        }

        "midnight 2016-09-29" >> {
          unary(ExtractMinute(_).embed, Data.Timestamp(Instant.parse("2016-03-01T00:00:00.000Z")), Data.Int(0))
        }

        "2016-09-29 12:34:56.789" >> {
          unary(ExtractMinute(_).embed, Data.Timestamp(Instant.parse("2016-03-01T12:34:56.789Z")), Data.Int(34))
        }
      }

      "ExtractMonth" >> {
        "2016-01-01" >> {
          unary(ExtractMonth(_).embed, Data.Date(LocalDate.parse("2016-01-01")), Data.Int(1))
        }

        "midnight 2016-01-01" >> {
          unary(ExtractMonth(_).embed, Data.Timestamp(Instant.parse("2016-01-01T00:00:00.000Z")), Data.Int(1))
        }

        "2016-02-29" >> {
          unary(ExtractMonth(_).embed, Data.Date(LocalDate.parse("2016-02-29")), Data.Int(2))
        }

        "midnight 2016-02-29" >> {
          unary(ExtractMonth(_).embed, Data.Timestamp(Instant.parse("2016-02-29T00:00:00.000Z")), Data.Int(2))
        }
      }

      "ExtractQuarter" >> {
        "2016-10-03" >> {
          unary(ExtractQuarter(_).embed, Data.Date(LocalDate.parse("2016-10-03")), Data.Int(4))
        }

        "midnight 2016-10-03" >> {
          unary(ExtractQuarter(_).embed, Data.Timestamp(Instant.parse("2016-10-03T00:00:00.000Z")), Data.Int(4))
        }

        "2016-03-31 (leap year)" >> {
          unary(ExtractQuarter(_).embed, Data.Date(LocalDate.parse("2016-03-31")), Data.Int(1))
        }

        "midnight 2016-03-31 (leap year)" >> {
          unary(ExtractQuarter(_).embed, Data.Timestamp(Instant.parse("2016-03-31T00:00:00.000Z")), Data.Int(1))
        }

        "2016-04-01 (leap year)" >> {
          unary(ExtractQuarter(_).embed, Data.Date(LocalDate.parse("2016-04-01")), Data.Int(2))
        }

        "midnight 2016-04-01 (leap year)" >> {
          unary(ExtractQuarter(_).embed, Data.Timestamp(Instant.parse("2016-04-01T00:00:00.000Z")), Data.Int(2))
        }

        "2017-03-31" >> {
          unary(ExtractQuarter(_).embed, Data.Date(LocalDate.parse("2017-03-31")), Data.Int(1))
        }

        "midnight 2017-03-31" >> {
          unary(ExtractQuarter(_).embed, Data.Timestamp(Instant.parse("2017-03-31T00:00:00.000Z")), Data.Int(1))
        }

        "2017-04-01" >> {
          unary(ExtractQuarter(_).embed, Data.Date(LocalDate.parse("2017-04-01")), Data.Int(2))
        }

        "midnight 2017-04-01" >> {
          unary(ExtractQuarter(_).embed, Data.Timestamp(Instant.parse("2017-04-01T00:00:00.000Z")), Data.Int(2))
        }
      }

      "ExtractSecond" >> {
        "2016-09-29" >> {
          unary(ExtractSecond(_).embed, Data.Date(LocalDate.parse("2016-09-29")), Data.Dec(0))
        }

        "midnight 2016-09-29" >> {
          unary(ExtractSecond(_).embed, Data.Timestamp(Instant.parse("2016-03-01T00:00:00.000Z")), Data.Dec(0))
        }

        "2016-09-29 12:34:56.789" >> {
          unary(ExtractSecond(_).embed, Data.Timestamp(Instant.parse("2016-03-01T12:34:56.789Z")), Data.Dec(56.789))
        }
      }

      // TODO: ExtractTimezone
      // TODO: ExtractTimezoneHour
      // TODO: ExtractTimezoneMinute

      "ExtractWeek" >> {
        "2016-01-01" >> {
          unary(ExtractWeek(_).embed, Data.Date(LocalDate.parse("2016-01-01")), Data.Int(53))
        }

        "midnight 2016-01-01" >> {
          unary(ExtractWeek(_).embed, Data.Timestamp(Instant.parse("2016-01-01T00:00:00.000Z")), Data.Int(53))
        }

        "2001-02-16" >> {
          unary(ExtractWeek(_).embed, Data.Date(LocalDate.parse("2001-02-16")), Data.Int(7))
        }

        "midnight 2016-10-03" >> {
          unary(ExtractWeek(_).embed, Data.Timestamp(Instant.parse("2001-02-16T00:00:00.000Z")), Data.Int(7))
        }

        "2005-01-01" >> {
          unary(ExtractWeek(_).embed, Data.Date(LocalDate.parse("2005-01-01")), Data.Int(53))
        }

        "midnight 2005-01-01" >> {
          unary(ExtractWeek(_).embed, Data.Timestamp(Instant.parse("2005-01-01T00:00:00.000Z")), Data.Int(53))
        }
      }

      "ExtractYear" >> {
        "1999-12-31" >> {
          unary(ExtractYear(_).embed, Data.Date(LocalDate.parse("1999-12-31")), Data.Int(1999))
        }

        "midnight 1999-12-31" >> {
          unary(ExtractYear(_).embed, Data.Timestamp(Instant.parse("1999-12-31T00:00:00.000Z")), Data.Int(1999))
        }
      }

      "StartOfDay" >> {
        "timestamp" >> prop { (x: Instant) =>
          val t = x.atZone(UTC)

          truncZonedDateTime(TemporalPart.Day, t).fold(
            e => Failure(e.shows),
            tt => unary(
              StartOfDay(_).embed,
              Data.Timestamp(x),
              Data.Timestamp(tt.toInstant)))
        }

        "date" >> prop { (x: LocalDate) =>
          unary(
            StartOfDay(_).embed,
            Data.Date(x),
            Data.Timestamp(x.atStartOfDay(UTC).toInstant))
        }
      }

      "Now" >> {
        import MathLib.Subtract

        "now" >> prop { (_: Int) =>
          val now = Now[Fix[LogicalPlan]]

          nullary(Subtract(now.embed, now.embed).embed, Data.Interval(Duration.ZERO))
        }
      }

      "TemporalTrunc" >> {
        def truncZonedDateTimeTimestamp(p: TemporalPart, i: Instant): Result =
          truncZonedDateTime(p, i.atZone(UTC)).fold(
            e => Failure(e.shows),
            tt => unary(
              TemporalTrunc(p, _).embed,
              Data.Timestamp(i),
              Data.Timestamp(tt.toInstant)))

        "Q#1966" >>
          truncZonedDateTimeTimestamp(
            TemporalPart.Century,
            Instant.parse("2000-03-01T06:15:45.204Z"))

        "timestamp Century" >> prop { x: Instant =>
          truncZonedDateTimeTimestamp(TemporalPart.Century, x)
        }

        "timestamp Day" >> prop { x: Instant =>
          truncZonedDateTimeTimestamp(TemporalPart.Day, x)
        }

        "timestamp Decade" >> prop { x: Instant =>
          truncZonedDateTimeTimestamp(TemporalPart.Decade, x)
        }

        "timestamp Hour" >> prop { x: Instant =>
          truncZonedDateTimeTimestamp(TemporalPart.Hour, x)
        }

        "timestamp Microsecond" >> prop { x: Instant =>
          truncZonedDateTimeTimestamp(TemporalPart.Microsecond, x)
        }

        "timestamp Millennium" >> prop { x: Instant =>
          truncZonedDateTimeTimestamp(TemporalPart.Millennium, x)
        }

        "timestamp Millisecond" >> prop { x: Instant =>
          truncZonedDateTimeTimestamp(TemporalPart.Millisecond, x)
        }

        "timestamp Minute" >> prop { x: Instant =>
          truncZonedDateTimeTimestamp(TemporalPart.Minute, x)
        }

        "timestamp Month" >> prop { x: Instant =>
          truncZonedDateTimeTimestamp(TemporalPart.Month, x)
        }

        "timestamp Quarter" >> prop { x: Instant =>
          truncZonedDateTimeTimestamp(TemporalPart.Quarter, x)
        }

        "timestamp Second" >> prop { x: Instant =>
          truncZonedDateTimeTimestamp(TemporalPart.Second, x)
        }

        "timestamp Week" >> prop { x: Instant =>
          truncZonedDateTimeTimestamp(TemporalPart.Week, x)
        }

        "timestamp Year" >> prop { x: Instant =>
          truncZonedDateTimeTimestamp(TemporalPart.Year, x)
        }

        def truncZonedDateTimeDate(p: TemporalPart, d: LocalDate): Result =
          truncZonedDateTime(p, d.atStartOfDay(UTC)).fold(
            e => Failure(e.shows),
            tt => unary(
              TemporalTrunc(p, _).embed,
              Data.Date(d),
              Data.Date(tt.toLocalDate)))

        "date Century" >> prop { d: LocalDate =>
          truncZonedDateTimeDate(TemporalPart.Century, d)
        }

        "date Day" >> prop { d: LocalDate =>
          truncZonedDateTimeDate(TemporalPart.Day, d)
        }

        "date Decade" >> prop { d: LocalDate =>
          truncZonedDateTimeDate(TemporalPart.Decade, d)
        }

        "date Hour" >> prop { d: LocalDate =>
          truncZonedDateTimeDate(TemporalPart.Hour, d)
        }

        "date Microsecond" >> prop { d: LocalDate =>
          truncZonedDateTimeDate(TemporalPart.Microsecond, d)
        }

        "date Millennium" >> prop { d: LocalDate =>
          truncZonedDateTimeDate(TemporalPart.Millennium, d)
        }

        "date Millisecond" >> prop { d: LocalDate =>
          truncZonedDateTimeDate(TemporalPart.Millisecond, d)
        }

        "date Minute" >> prop { d: LocalDate =>
          truncZonedDateTimeDate(TemporalPart.Minute, d)
        }

        "date Month" >> prop { d: LocalDate =>
          truncZonedDateTimeDate(TemporalPart.Month, d)
        }

        "date Quarter" >> prop { d: LocalDate =>
          truncZonedDateTimeDate(TemporalPart.Quarter, d)
        }

        "date Second" >> prop { d: LocalDate =>
          truncZonedDateTimeDate(TemporalPart.Second, d)
        }

        "date Week" >> prop { d: LocalDate =>
          truncZonedDateTimeDate(TemporalPart.Week, d)
        }

        "date Year" >> prop { d: LocalDate =>
          truncZonedDateTimeDate(TemporalPart.Year, d)
        }

        def truncLocalTimeʹ(p: TemporalPart, t: LocalTime): Result =
          truncLocalTime(p, t).fold(
            e => Failure(e.shows),
            tt => unary(
              TemporalTrunc(p, _).embed,
              Data.Time(t),
              Data.Time(tt)))

        "time Century" >> prop { t: LocalTime =>
          truncLocalTimeʹ(TemporalPart.Century, t)
        }

        "time Day" >> prop { t: LocalTime =>
          truncLocalTimeʹ(TemporalPart.Day, t)
        }

        "time Decade" >> prop { t: LocalTime =>
          truncLocalTimeʹ(TemporalPart.Decade, t)
        }

        "time Hour" >> prop { t: LocalTime =>
          truncLocalTimeʹ(TemporalPart.Hour, t)
        }

        "time Microsecond" >> prop { t: LocalTime =>
          truncLocalTimeʹ(TemporalPart.Microsecond, t)
        }

        "time Millennium" >> prop { t: LocalTime =>
          truncLocalTimeʹ(TemporalPart.Millennium, t)
        }

        "time Millisecond" >> prop { t: LocalTime =>
          truncLocalTimeʹ(TemporalPart.Millisecond, t)
        }

        "time Minute" >> prop { t: LocalTime =>
          truncLocalTimeʹ(TemporalPart.Minute, t)
        }

        "time Month" >> prop { t: LocalTime =>
          truncLocalTimeʹ(TemporalPart.Month, t)
        }

        "time Quarter" >> prop { t: LocalTime =>
          truncLocalTimeʹ(TemporalPart.Quarter, t)
        }

        "time Second" >> prop { t: LocalTime =>
          truncLocalTimeʹ(TemporalPart.Second, t)
        }

        "time Week" >> prop { t: LocalTime =>
          truncLocalTimeʹ(TemporalPart.Week, t)
        }

        "time Year" >> prop { t: LocalTime =>
          truncLocalTimeʹ(TemporalPart.Year, t)
        }
      }

      "TimeOfDay" >> {
        "timestamp" >> {
          val now = Instant.now
          val expected = now.atZone(ZoneOffset.UTC).toLocalTime
          unary(TimeOfDay(_).embed, Data.Timestamp(now), Data.Time(expected))
        }
      }
    }

    "MathLib" >> {
      import MathLib._

      // NB: testing only (32-bit) ints, to avoid overflowing 64-bit longs
      // and the 53 bits of integer precision in a 64-bit double.

      // TODO: BigDecimals (which can under/overflow)
      // TODO: mixed BigInt/BigDecimal (which can explode)

      "Add" >> {
        "any ints" >> prop { (x: Int, y: Int) =>
          binary(Add(_, _).embed, Data.Int(x), Data.Int(y), Data.Int(x.toLong + y.toLong))
        }

        "any doubles" >> prop { (x: Double, y: Double) =>
          binary(Add(_, _).embed, Data.Dec(x), Data.Dec(y), Data.Dec(x + y))
        }

        "mixed int/double" >> prop { (x: Int, y: Double) =>
          commute(Add(_, _).embed, Data.Int(x), Data.Dec(y), Data.Dec(x + y))
        }

        // TODO: Timestamp + Interval, Date + Interval, Time + Interval
      }

      "Multiply" >> {
        "any ints" >> prop { (x: Int, y: Int) =>
          binary(Multiply(_, _).embed, Data.Int(x), Data.Int(y), Data.Int(x.toLong * y.toLong))
        }

        // TODO: figure out what domain can be tested here (tends to overflow)
        // "any doubles" >> prop { (x: Double, y: Double) =>
        //   binary(Multiply(_, _).embed, Data.Dec(x), Data.Dec(y), Data.Dec(x * y))
        // }

        // TODO: figure out what domain can be tested here
        // "mixed int/double" >> prop { (x: Int, y: Double) =>
        //   commute(Multiply(_, _).embed, Data.Int(x), Data.Dec(y), Data.Dec(x * y))
        // }

        // TODO: Interval * Int
      }

      "Power" >> {
        "Int to 0" >> prop { (x: BigInt) =>
          binary(Power(_, _).embed, Data.Int(x), Data.Int(0), Data.Int(1))
        }

        "Dec to 0" >> prop { (x: BigDecimal) =>
          binary(Power(_, _).embed, Data.Dec(x), Data.Int(0), Data.Int(1))
        }

        "Int to 1" >> prop { (x: BigInt) =>
          binary(Power(_, _).embed, Data.Int(x), Data.Int(1), Data.Int(x))
        }

        "Dec to 1" >> prop { (x: BigDecimal) =>
          binary(Power(_, _).embed, Data.Dec(x), Data.Int(1), Data.Dec(x))
        }

        "0 to small positive int" >> prop { (y0: Int) =>
          val y = abs(y0 % 10)
          y != 0 ==>
            binary(Power(_, _).embed, Data.Int(0), Data.Int(y), Data.Int(0))
        }

        // TODO: figure out what domain can be tested here (negatives?)
        // "0 to Dec" >> prop { (y: BigDecimal) =>
        //   y != 0 ==>
        //     binary(Power(_, _).embed, Data.Int(0), Data.Dec(y), Data.Int(0))
        // }

        "Int squared" >> prop { (x: Int) =>
          binary(Power(_, _).embed, Data.Int(x), Data.Int(2), Data.Int(x.toLong * x.toLong))
        }

        // TODO: test as much of the domain as much sense
      }

      "Subtract" >> {
        "any ints" >> prop { (x: Int, y: Int) =>
          binary(Subtract(_, _).embed, Data.Int(x), Data.Int(y), Data.Int(x.toLong - y.toLong))
        }

        "any doubles" >> prop { (x: Double, y: Double) =>
          binary(Subtract(_, _).embed, Data.Dec(x), Data.Dec(y), Data.Dec(x - y))
        }

        "mixed int/double" >> prop { (x: Int, y: Double) =>
          binary(Subtract(_, _).embed, Data.Int(x), Data.Dec(y), Data.Dec(x - y)) and
            binary(Subtract(_, _).embed, Data.Dec(y), Data.Int(x), Data.Dec(y - x))
        }

        // TODO:
        // Timestamp - Timestamp, Timestamp - Interval,
        // Date - Date, Date - Interval,
        // Time - Time, Time + Interval
      }

      "Divide" >> {
        "any ints" >> prop { (x: Int, y: Int) =>
          y != 0 ==>
            binary(Divide(_, _).embed, Data.Int(x), Data.Int(y), Data.Dec(x.toDouble / y.toDouble))
        }

        // TODO: figure out what domain can be tested here
        // "any doubles" >> prop { (x: Double, y: Double) =>
        //   binary(Divide(_, _).embed, Data.Dec(x), Data.Dec(y), Data.Dec(x / y))
        // }

        // TODO: figure out what domain can be tested here
        // "mixed int/double" >> prop { (x: Int, y: Double) =>
        //   commute(Divide(_, _).embed, Data.Int(x), Data.Dec(y), Data.Dec(x / y))
        // }

        // TODO: Interval * Int
      }

      "Negate" >> {
        "any Int" >> prop { (x: BigInt) =>
          unary(Negate(_).embed, Data.Int(x), Data.Int(-x))
        }

        "any Dec" >> prop { (x: BigDecimal) =>
          unary(Negate(_).embed, Data.Dec(x), Data.Dec(-x))
        }

        // TODO: Interval
      }

      "Abs" >> {
        "any Int" >> prop { (x: BigInt) =>
          unary(Abs(_).embed, Data.Int(x), Data.Int(x.abs))
        }

        "any Dec" >> prop { (x: BigDecimal) =>
          unary(Abs(_).embed, Data.Dec(x), Data.Dec(x.abs))
        }

        // TODO: add support for interval
        // "any Interval" >> prop { (x: Duration) =>
        //   unary(Abs(_).embed, Data.Interval(x), if (x.isNegative) Data.Interval(x.negated) else Data.Interval(x))
        // }
      }

      "Trunc" >> {
        "any Int" >> prop { (x: BigInt) =>
          unary(Trunc(_).embed, Data.Int(x), Data.Int(x))
        }

        "any Dec" >> prop { (x: BigDecimal) =>
          unary(Trunc(_).embed, Data.Dec(x), Data.Dec(x.setScale(0, RoundingMode.DOWN)))
        }
      }

      "Ceil" >> {
        "any Int" >> prop { (x: BigInt) =>
          unary(Ceil(_).embed, Data.Int(x), Data.Int(x))
        }

        "any Dec" >> prop { (x: BigDecimal) =>
          unary(Ceil(_).embed, Data.Dec(x), Data.Dec(x.setScale(0, RoundingMode.CEILING)))
        }
      }

      "Floor" >> {
        "any Int" >> prop { (x: BigInt) =>
          unary(Floor(_).embed, Data.Int(x), Data.Int(x))
        }

        "any Dec" >> prop { (x: BigDecimal) =>
          unary(Floor(_).embed, Data.Dec(x), Data.Dec(x.setScale(0, RoundingMode.FLOOR)))
        }
      }

      "Round" >> {
        "any Int" >> prop { (x: BigInt) =>
          unary(Round(_).embed, Data.Int(x), Data.Int(x))
        }

        "0.5 -> 0" >> {
          unary(Round(_).embed, Data.Dec(0.5), Data.Int(0))
        }

        "1.5 -> 2" >> {
          unary(Round(_).embed, Data.Dec(1.5), Data.Int(2))
        }

        "1.75 -> 2" >> {
          unary(Round(_).embed, Data.Dec(1.75), Data.Int(2))
        }

        "2.5 -> 2" >> {
          unary(Round(_).embed, Data.Dec(2.5), Data.Int(2))
        }

        "2.75 -> 3" >> {
          unary(Round(_).embed, Data.Dec(2.75), Data.Int(3))
        }

        "-0.5 -> 0" >> {
          unary(Round(_).embed, Data.Dec(-0.5), Data.Int(0))
        }

        "-1.5 -> -2" >> {
          unary(Round(_).embed, Data.Dec(-1.5), Data.Int(-2))
        }

        "-2.5 -> -2" >> {
          unary(Round(_).embed, Data.Dec(-2.5), Data.Int(-2))
        }
      }

      "CeilScale" >> {
        "scale 0" >> {
          val scale = 0

          "any Int" >> prop { (x: BigInt) =>
            binary(CeilScale(_, _).embed, Data.Int(x), Data.Int(scale), Data.Int(x))
          }

          "0.5 -> 1" >> {
            binary(CeilScale(_, _).embed, Data.Dec(0.5), Data.Int(scale), Data.Int(1))
          }

          "1.5 -> 2" >> {
            binary(CeilScale(_, _).embed, Data.Dec(1.5), Data.Int(scale), Data.Int(2))
          }

          "2.5 -> 3" >> {
            binary(CeilScale(_, _).embed, Data.Dec(2.5), Data.Int(scale), Data.Int(3))
          }

          "-0.5 -> 0" >> {
            binary(CeilScale(_, _).embed, Data.Dec(-0.5), Data.Int(scale), Data.Int(0))
          }

          "-1.5 -> -1" >> {
            binary(CeilScale(_, _).embed, Data.Dec(-1.5), Data.Int(scale), Data.Int(-1))
          }

          "-2.5 -> -2" >> {
            binary(CeilScale(_, _).embed, Data.Dec(-2.5), Data.Int(scale), Data.Int(-2))
          }
        }

        "scale 1" >> {
          val scale = 1

          "any Int" >> prop { (x: BigInt) =>
            binary(CeilScale(_, _).embed, Data.Int(x), Data.Int(scale), Data.Int(x))
          }

          "0.5 -> 0.5" >> {
            binary(CeilScale(_, _).embed, Data.Dec(0.5), Data.Int(scale), Data.Dec(0.5))
          }

          "0.25 -> 0.3" >> {
            binary(CeilScale(_, _).embed, Data.Dec(0.25), Data.Int(scale), Data.Dec(0.3))
          }

          "-0.5 -> -0.5" >> {
            binary(CeilScale(_, _).embed, Data.Dec(-0.5), Data.Int(scale), Data.Dec(-0.5))
          }

          "-0.25 -> 0.2" >> {
            binary(CeilScale(_, _).embed, Data.Dec(-0.25), Data.Int(scale), Data.Dec(-0.2))
          }
        }

        "scale 2" >> {
          val scale = 2

          "any Int" >> prop { (x: BigInt) =>
            binary(CeilScale(_, _).embed, Data.Int(x), Data.Int(scale), Data.Int(x))
          }

          "0.5 -> 0.5" >> {
            binary(CeilScale(_, _).embed, Data.Dec(0.5), Data.Int(scale), Data.Dec(0.5))
          }

          "0.25 -> 0.25" >> {
            binary(CeilScale(_, _).embed, Data.Dec(0.25), Data.Int(scale), Data.Dec(0.25))
          }

          "0.125 -> 0.13" >> {
            binary(CeilScale(_, _).embed, Data.Dec(0.125), Data.Int(scale), Data.Dec(0.13))
          }

          "-0.5 -> -0.5" >> {
            binary(CeilScale(_, _).embed, Data.Dec(-0.5), Data.Int(scale), Data.Dec(-0.5))
          }

          "-0.25 -> 0.25" >> {
            binary(CeilScale(_, _).embed, Data.Dec(-0.25), Data.Int(scale), Data.Dec(-0.25))
          }

          "-0.125 -> -0.12" >> {
            binary(CeilScale(_, _).embed, Data.Dec(-0.125), Data.Int(scale), Data.Dec(-0.12))
          }
        }

        "scale -1" >> {
          val scale = -1

          "1 -> 10" >> {
            binary(CeilScale(_, _).embed, Data.Int(1), Data.Int(scale), Data.Int(10))
          }

          "10 -> 10" >> {
            binary(CeilScale(_, _).embed, Data.Int(10), Data.Int(scale), Data.Int(10))
          }

          "12345 -> 12350" >> {
            binary(CeilScale(_, _).embed, Data.Int(12345), Data.Int(scale), Data.Int(12350))
          }
        }
      }

      "FloorScale" >> {
        "scale 0" >> {
          val scale = 0

          "any Int" >> prop { (x: BigInt) =>
            binary(FloorScale(_, _).embed, Data.Int(x), Data.Int(scale), Data.Int(x))
          }

          "0.5 -> 0" >> {
            binary(FloorScale(_, _).embed, Data.Dec(0.5), Data.Int(scale), Data.Int(0))
          }

          "1.5 -> 1" >> {
            binary(FloorScale(_, _).embed, Data.Dec(1.5), Data.Int(scale), Data.Int(1))
          }

          "2.5 -> 2" >> {
            binary(FloorScale(_, _).embed, Data.Dec(2.5), Data.Int(scale), Data.Int(2))
          }

          "-0.5 -> -1" >> {
            binary(FloorScale(_, _).embed, Data.Dec(-0.5), Data.Int(scale), Data.Int(-1))
          }

          "-1.5 -> -2" >> {
            binary(FloorScale(_, _).embed, Data.Dec(-1.5), Data.Int(scale), Data.Int(-2))
          }

          "-2.5 -> -3" >> {
            binary(FloorScale(_, _).embed, Data.Dec(-2.5), Data.Int(scale), Data.Int(-3))
          }
        }

        "scale 1" >> {
          val scale = 1

          "any Int" >> prop { (x: BigInt) =>
            binary(FloorScale(_, _).embed, Data.Int(x), Data.Int(scale), Data.Int(x))
          }

          "0.5 -> 0.5" >> {
            binary(FloorScale(_, _).embed, Data.Dec(0.5), Data.Int(scale), Data.Dec(0.5))
          }

          "0.25 -> 0.2" >> {
            binary(FloorScale(_, _).embed, Data.Dec(0.25), Data.Int(scale), Data.Dec(0.2))
          }

          "-0.5 -> -0.5" >> {
            binary(FloorScale(_, _).embed, Data.Dec(-0.5), Data.Int(scale), Data.Dec(-0.5))
          }

          "-0.25 -> -0.3" >> {
            binary(FloorScale(_, _).embed, Data.Dec(-0.25), Data.Int(scale), Data.Dec(-0.3))
          }
        }

        "scale 2" >> {
          val scale = 2

          "any Int" >> prop { (x: BigInt) =>
            binary(FloorScale(_, _).embed, Data.Int(x), Data.Int(scale), Data.Int(x))
          }

          "0.5 -> 0.5" >> {
            binary(FloorScale(_, _).embed, Data.Dec(0.5), Data.Int(scale), Data.Dec(0.5))
          }

          "0.25 -> 0.25" >> {
            binary(FloorScale(_, _).embed, Data.Dec(0.25), Data.Int(scale), Data.Dec(0.25))
          }

          "0.125 -> 0.12" >> {
            binary(FloorScale(_, _).embed, Data.Dec(0.125), Data.Int(scale), Data.Dec(0.12))
          }

          "-0.5 -> -0.5" >> {
            binary(FloorScale(_, _).embed, Data.Dec(-0.5), Data.Int(scale), Data.Dec(-0.5))
          }

          "-0.25 -> 0.25" >> {
            binary(FloorScale(_, _).embed, Data.Dec(-0.25), Data.Int(scale), Data.Dec(-0.25))
          }

          "-0.125 -> -0.13" >> {
            binary(FloorScale(_, _).embed, Data.Dec(-0.125), Data.Int(scale), Data.Dec(-0.13))
          }
        }

        "scale -1" >> {
          val scale = -1

          "1 -> 0" >> {
            binary(FloorScale(_, _).embed, Data.Int(1), Data.Int(scale), Data.Int(0))
          }

          "10 -> 10" >> {
            binary(FloorScale(_, _).embed, Data.Int(10), Data.Int(scale), Data.Int(10))
          }

          "12345 -> 12340" >> {
            binary(FloorScale(_, _).embed, Data.Int(12345), Data.Int(scale), Data.Int(12340))
          }
        }
      }

      "RoundScale" >> {
        "scale 0" >> {
          val scale = 0

          "any Int" >> prop { (x: BigInt) =>
            binary(RoundScale(_, _).embed, Data.Int(x), Data.Int(scale), Data.Int(x))
          }

          "0.5 -> 0" >> {
            binary(RoundScale(_, _).embed, Data.Dec(0.5), Data.Int(scale), Data.Int(0))
          }

          "1.5 -> 2" >> {
            binary(RoundScale(_, _).embed, Data.Dec(1.5), Data.Int(scale), Data.Int(2))
          }

          "1.75 -> 2" >> {
            binary(RoundScale(_, _).embed, Data.Dec(1.75), Data.Int(scale), Data.Int(2))
          }

          "2.5 -> 2" >> {
            binary(RoundScale(_, _).embed, Data.Dec(2.5), Data.Int(scale), Data.Int(2))
          }

          "2.75 -> 3" >> {
            binary(RoundScale(_, _).embed, Data.Dec(2.75), Data.Int(scale), Data.Int(3))
          }

          "-0.5 -> 0" >> {
            binary(RoundScale(_, _).embed, Data.Dec(-0.5), Data.Int(scale), Data.Int(0))
          }

          "-1.5 -> -2" >> {
            binary(RoundScale(_, _).embed, Data.Dec(-1.5), Data.Int(scale), Data.Int(-2))
          }

          "-2.5 -> -2" >> {
            binary(RoundScale(_, _).embed, Data.Dec(-2.5), Data.Int(scale), Data.Int(-2))
          }
        }

        "scale 1" >> {
          val scale = 1

          "any Int" >> prop { (x: BigInt) =>
            binary(RoundScale(_, _).embed, Data.Int(x), Data.Int(scale), Data.Int(x))
          }

          "0.5 -> 0.5" >> {
            binary(RoundScale(_, _).embed, Data.Dec(0.5), Data.Int(scale), Data.Dec(0.5))
          }

          "1.5 -> 1.5" >> {
            binary(RoundScale(_, _).embed, Data.Dec(1.5), Data.Int(scale), Data.Dec(1.5))
          }

          "1.75 -> 1.8" >> {
            binary(RoundScale(_, _).embed, Data.Dec(1.75), Data.Int(scale), Data.Dec(1.8))
          }

          "1.65 -> 1.6" >> {
            binary(RoundScale(_, _).embed, Data.Dec(1.65), Data.Int(scale), Data.Dec(1.6))
          }

          "-0.5 -> -0.5" >> {
            binary(RoundScale(_, _).embed, Data.Dec(-0.5), Data.Int(scale), Data.Dec(-0.5))
          }

          "-1.5 -> -1.5" >> {
            binary(RoundScale(_, _).embed, Data.Dec(-1.5), Data.Int(scale), Data.Dec(-1.5))
          }

          "-1.75 -> -1.8" >> {
            binary(RoundScale(_, _).embed, Data.Dec(-1.75), Data.Int(scale), Data.Dec(-1.8))
          }

          "-1.85 -> -1.8" >> {
            binary(RoundScale(_, _).embed, Data.Dec(-1.85), Data.Int(scale), Data.Dec(-1.8))
          }
        }

        "scale -1" >> {
          val scale = -1

          "1 -> 0" >> {
            binary(RoundScale(_, _).embed, Data.Int(1), Data.Int(scale), Data.Int(0))
          }

          "5 -> 0" >> {
            binary(RoundScale(_, _).embed, Data.Int(5), Data.Int(scale), Data.Int(0))
          }

          "10 -> 10" >> {
            binary(RoundScale(_, _).embed, Data.Int(10), Data.Int(scale), Data.Int(10))
          }

          "12345 -> 12340" >> {
            binary(RoundScale(_, _).embed, Data.Int(12345), Data.Int(scale), Data.Int(12340))
          }

          "12335 -> 12340" >> {
            binary(RoundScale(_, _).embed, Data.Int(12335), Data.Int(scale), Data.Int(12340))
          }

          "123 -> 120" >> {
            binary(RoundScale(_, _).embed, Data.Int(123), Data.Int(scale), Data.Int(120))
          }
        }
      }

      "Modulo" >> {
        "any int by 1" >> prop { (x: Int) =>
          binary(Modulo(_, _).embed, Data.Int(x), Data.Int(1), Data.Int(0))
        }

        "any ints" >> prop { (x: Int, y: Int) =>
          y != 0 ==>
            binary(Modulo(_, _).embed, Data.Int(x), Data.Int(y), Data.Int(BigInt(x) % BigInt(y)))
        }

        // TODO analyze and optionally shortCircuit per connector
        // "any doubles" >> prop { (x: Double, y: Double) =>
        //   y != 0 ==>
        //     binary(Modulo(_, _).embed, Data.Dec(x), Data.Dec(y), Data.Dec(BigDecimal(x).remainder(BigDecimal(y))))
        // }
        //
        // "any big decimals" >> prop { (x: BigDecimal, y: BigDecimal) =>
        //   !y.equals(0.0) ==>
        //     binary(Modulo(_, _).embed, Data.Dec(x), Data.Dec(y), Data.Dec(x.remainder(y)))
        // }
        //
        // "mixed int/double" >> prop { (x: Int, y: Double) =>
        //   y != 0 ==>
        //     binary(Modulo(_, _).embed, Data.Int(x), Data.Dec(y), Data.Dec(BigDecimal(y).remainder(BigDecimal(x))))
        //   x != 0 ==>
        //     binary(Modulo(_, _).embed, Data.Dec(y), Data.Int(x), Data.Dec(BigDecimal(y).remainder(BigDecimal(x))))
        // }
      }
    }

    "RelationsLib" >> {
      import RelationsLib._

      "Eq" >> {
        "any Int with self" >> prop { (x: BigInt) =>
          binary(Eq(_, _).embed, Data.Int(x), Data.Int(x), Data.Bool(true))
        }

        "any two Ints" >> prop { (x: BigInt, y: BigInt) =>
          binary(Eq(_, _).embed, Data.Int(x), Data.Int(y), Data.Bool(x == y))
        }

        "any Dec with self" >> prop { (x: BigDecimal) =>
          binary(Eq(_, _).embed, Data.Dec(x), Data.Dec(x), Data.Bool(true))
        }

        "any two Decs" >> prop { (x: BigDecimal, y: BigDecimal) =>
          binary(Eq(_, _).embed, Data.Dec(x), Data.Dec(y), Data.Bool(x == y))
        }

        "any Str with self" >> prop { (x: String) =>
          binary(Eq(_, _).embed, Data.Str(x), Data.Str(x), Data.Bool(true))
        }

        "any two Strs" >> prop { (x: String, y: String) =>
          binary(Eq(_, _).embed, Data.Str(x), Data.Str(y), Data.Bool(x == y))
        }

        "any value with self" >> prop { (x: Data) =>
          binary(Eq(_, _).embed, x, x, Data.Bool(true))
        }

        "any values with different types" >> prop { (x: Data, y: Data) =>
          // ...provided they are not both Numeric (Int | Dec)
          (x.dataType != y.dataType &&
            !((Type.Numeric contains x.dataType) &&
              (Type.Numeric contains y.dataType))) ==>
            binary(Eq(_, _).embed, x, y, Data.Bool(false))
        }

        "any date & timestamp" >> prop { (d: LocalDate, i: Instant) =>
          binary(Eq(_, _).embed, Data.Date(d), Data.Timestamp(i), Data.NA)
        }
        // TODO: the rest of the types
      }

      "Neq" >> {
        "any Int with self" >> prop { (x: BigInt) =>
          binary(Neq(_, _).embed, Data.Int(x), Data.Int(x), Data.Bool(false))
        }

        "any two Ints" >> prop { (x: BigInt, y: BigInt) =>
          binary(Neq(_, _).embed, Data.Int(x), Data.Int(y), Data.Bool(x != y))
        }

        "any Dec with self" >> prop { (x: BigDecimal) =>
          binary(Neq(_, _).embed, Data.Dec(x), Data.Dec(x), Data.Bool(false))
        }

        "any two Decs" >> prop { (x: BigDecimal, y: BigDecimal) =>
          binary(Neq(_, _).embed, Data.Dec(x), Data.Dec(y), Data.Bool(x != y))
        }

        "any Str with self" >> prop { (x: String) =>
          binary(Neq(_, _).embed, Data.Str(x), Data.Str(x), Data.Bool(false))
        }

        "any two Strs" >> prop { (x: String, y: String) =>
          binary(Neq(_, _).embed, Data.Str(x), Data.Str(y), Data.Bool(x != y))
        }

        "any value with self" >> prop { (x: Data) =>
          binary(Neq(_, _).embed, x, x, Data.Bool(false))
        }

        "any values with different types" >> prop { (x: Data, y: Data) =>
          // ...provided they are not both Numeric (Int | Dec)
          (x.dataType != y.dataType &&
            !((Type.Numeric contains x.dataType) &&
              (Type.Numeric contains y.dataType))) ==>
            binary(Neq(_, _).embed, x, y, Data.Bool(true))
        }

        // TODO: the rest of the types
      }

      "Lt" >> {
        "any Int with self" >> prop { (x: BigInt) =>
          binary(Lt(_, _).embed, Data.Int(x), Data.Int(x), Data.Bool(false))
        }

        "any two Ints" >> prop { (x: BigInt, y: BigInt) =>
          binary(Lt(_, _).embed, Data.Int(x), Data.Int(y), Data.Bool(x < y))
        }

        "any Dec with self" >> prop { (x: BigDecimal) =>
          binary(Lt(_, _).embed, Data.Dec(x), Data.Dec(x), Data.Bool(false))
        }

        "any two Decs" >> prop { (x: BigDecimal, y: BigDecimal) =>
          binary(Lt(_, _).embed, Data.Dec(x), Data.Dec(y), Data.Bool(x < y))
        }

        "any Str with self" >> prop { (x: String) =>
          binary(Lt(_, _).embed, Data.Str(x), Data.Str(x), Data.Bool(false))
        }

        "any two Strs" >> prop { (x: String, y: String) =>
          binary(Lt(_, _).embed, Data.Str(x), Data.Str(y), Data.Bool(x < y))
        }

        "any date & timestamp" >> prop { (d: LocalDate, i: Instant) =>
          binary(Lt(_, _).embed, Data.Date(d), Data.Timestamp(i), Data.NA)
        }
        // TODO: Timestamp, Interval, cross-type comparison
      }

      "Lte" >> {
        "any Int with self" >> prop { (x: BigInt) =>
          binary(Lte(_, _).embed, Data.Int(x), Data.Int(x), Data.Bool(true))
        }

        "any two Ints" >> prop { (x: BigInt, y: BigInt) =>
          binary(Lte(_, _).embed, Data.Int(x), Data.Int(y), Data.Bool(x <= y))
        }

        "any Dec with self" >> prop { (x: BigDecimal) =>
          binary(Lte(_, _).embed, Data.Dec(x), Data.Dec(x), Data.Bool(true))
        }

        "any two Decs" >> prop { (x: BigDecimal, y: BigDecimal) =>
          binary(Lte(_, _).embed, Data.Dec(x), Data.Dec(y), Data.Bool(x <= y))
        }

        "any Str with self" >> prop { (x: String) =>
          binary(Lte(_, _).embed, Data.Str(x), Data.Str(x), Data.Bool(true))
        }

        "any two Strs" >> prop { (x: String, y: String) =>
          binary(Lte(_, _).embed, Data.Str(x), Data.Str(y), Data.Bool(x <= y))
        }

        "any date & timestamp" >> prop { (d: LocalDate, i: Instant) =>
          binary(Lte(_, _).embed, Data.Date(d), Data.Timestamp(i), Data.NA)
        }
      }

      "Gt" >> {
        "any Int with self" >> prop { (x: BigInt) =>
          binary(Gt(_, _).embed, Data.Int(x), Data.Int(x), Data.Bool(false))
        }

        "any two Ints" >> prop { (x: BigInt, y: BigInt) =>
          binary(Gt(_, _).embed, Data.Int(x), Data.Int(y), Data.Bool(x > y))
        }

        "any Dec with self" >> prop { (x: BigDecimal) =>
          binary(Gt(_, _).embed, Data.Dec(x), Data.Dec(x), Data.Bool(false))
        }

        "any two Decs" >> prop { (x: BigDecimal, y: BigDecimal) =>
          binary(Gt(_, _).embed, Data.Dec(x), Data.Dec(y), Data.Bool(x > y))
        }

        "any Str with self" >> prop { (x: String) =>
          binary(Gt(_, _).embed, Data.Str(x), Data.Str(x), Data.Bool(false))
        }

        "any two Strs" >> prop { (x: String, y: String) =>
          binary(Gt(_, _).embed, Data.Str(x), Data.Str(y), Data.Bool(x > y))
        }
        "any date & timestamp" >> prop { (d: LocalDate, i: Instant) =>
          binary(Gt(_, _).embed, Data.Date(d), Data.Timestamp(i), Data.NA)
        }
      }

      "Gte" >> {
        "any Int with self" >> prop { (x: BigInt) =>
          binary(Gte(_, _).embed, Data.Int(x), Data.Int(x), Data.Bool(true))
        }

        "any two Ints" >> prop { (x: BigInt, y: BigInt) =>
          binary(Gte(_, _).embed, Data.Int(x), Data.Int(y), Data.Bool(x >= y))
        }

        "any Dec with self" >> prop { (x: BigDecimal) =>
          binary(Gte(_, _).embed, Data.Dec(x), Data.Dec(x), Data.Bool(true))
        }

        "any two Decs" >> prop { (x: BigDecimal, y: BigDecimal) =>
          binary(Gte(_, _).embed, Data.Dec(x), Data.Dec(y), Data.Bool(x >= y))
        }

        "any Str with self" >> prop { (x: String) =>
          binary(Gte(_, _).embed, Data.Str(x), Data.Str(x), Data.Bool(true))
        }

        "any two Strs" >> prop { (x: String, y: String) =>
          binary(Gte(_, _).embed, Data.Str(x), Data.Str(y), Data.Bool(x >= y))
        }

        "any date & timestamp" >> prop { (d: LocalDate, i: Instant) =>
          binary(Gte(_, _).embed, Data.Date(d), Data.Timestamp(i), Data.NA)
        }
      }

      "Between" >> {
        "any Int with self" >> prop { (x: BigInt) =>
          ternary(Between(_, _, _).embed, Data.Int(x), Data.Int(x), Data.Int(x), Data.Bool(true))
        }

        "any three Ints" >> prop { (x1: BigInt, x2: BigInt, x3: BigInt) =>
          val xs = List(x1, x2, x3).sorted
          ternary(Between(_, _, _).embed, Data.Int(xs(1)), Data.Int(xs(0)), Data.Int(xs(2)), Data.Bool(true))
        }

        "any Dec with self" >> prop { (x: BigDecimal) =>
          ternary(Between(_, _, _).embed, Data.Dec(x), Data.Dec(x), Data.Dec(x), Data.Bool(true))
        }

        "any three Decs" >> prop { (x1: BigDecimal, x2: BigDecimal, x3: BigDecimal) =>
          val xs = List(x1, x2, x3).sorted
          ternary(Between(_, _, _).embed, Data.Dec(xs(1)), Data.Dec(xs(0)), Data.Dec(xs(2)), Data.Bool(true))
        }

        "any Str with self" >> prop { (x: String) =>
          ternary(Between(_, _, _).embed, Data.Str(x), Data.Str(x), Data.Str(x), Data.Bool(true))
        }

        "any three Strs" >> prop { (x1: String, x2: String, x3: String) =>
          val xs = List(x1, x2, x3).sorted
          ternary(Between(_, _, _).embed, Data.Str(xs(1)), Data.Str(xs(0)), Data.Str(xs(2)), Data.Bool(true))
        }

        // TODO: Timestamp, Interval, cross-type comparison
      }

      "IfUndefined" >> {
        """NA ?? 42""" >> {
          binary(
            IfUndefined(_, _).embed,
            Data.NA,
            Data.Int(42),
            Data.Int(42))
        }

        """1 ?? 2""" >> {
          binary(
            IfUndefined(_, _).embed,
            Data.Int(1),
            Data.Int(2),
            Data.Int(1))
        }

        """{"a": 1} ?? 2""" >> {
          binary(
            IfUndefined(_, _).embed,
            Data.Obj("a" -> Data.Int(1)),
            Data.Int(2),
            Data.Obj("a" -> Data.Int(1)))
        }

        """{"a": NA, "b": 2} ?? 3""" >> {
          binary(
            IfUndefined(_, _).embed,
            Data.Obj("a" -> Data.NA, "b" -> Data.Int(2)),
            Data.Int(3),
            Data.Obj("b" -> Data.Int(2)))
        }

        """[NA, 2] ?? 3""" >> {
          binary(
            IfUndefined(_, _).embed,
            Data.Arr(Data.NA :: Data.Int(2) :: Nil),
            Data.Int(3),
            Data.Arr(Data.Int(2) :: Nil))
        }
      }

      "And" >> {
        "false, false" >> {
          binary(And(_, _).embed, Data.Bool(false), Data.Bool(false), Data.Bool(false))
        }

        "false, true" >> {
          commute(And(_, _).embed, Data.Bool(false), Data.Bool(true), Data.Bool(false))
        }

        "true, true" >> {
          binary(And(_, _).embed, Data.Bool(true), Data.Bool(true), Data.Bool(true))
        }

        "undefined, false" >> {
          commute(And(_, _).embed, Data.NA, Data.Bool(false), Data.Bool(false))
        }

        "undefined, true" >> {
          commute(And(_, _).embed, Data.NA, Data.Bool(true), Data.NA)
        }
      }

      "Or" >> {
        "false, false" >> {
          binary(Or(_, _).embed, Data.Bool(false), Data.Bool(false), Data.Bool(false))
        }

        "false, true" >> {
          commute(Or(_, _).embed, Data.Bool(false), Data.Bool(true), Data.Bool(true))
        }

        "true, true" >> {
          binary(Or(_, _).embed, Data.Bool(true), Data.Bool(true), Data.Bool(true))
        }

        "undefined, false" >> {
          commute(Or(_, _).embed, Data.NA, Data.Bool(false), Data.NA)
        }

        "undefined, true" >> {
          commute(Or(_, _).embed, Data.NA, Data.Bool(true), Data.Bool(true))
        }
      }

      "Not" >> {
        "false" >> {
          unary(Not(_).embed, Data.Bool(false), Data.Bool(true))
        }

        "true" >> {
          unary(Not(_).embed, Data.Bool(true), Data.Bool(false))
        }
      }

      "Cond" >> {
        "true" >> prop { (x: Data, y: Data) =>
          ternary(Cond(_, _, _).embed, Data.Bool(true), x, y, x)
        }

        "false" >> prop { (x: Data, y: Data) =>
          ternary(Cond(_, _, _).embed, Data.Bool(false), x, y, y)
        }
      }
    }

    "StructuralLib" >> {
      import StructuralLib._

      // FIXME: No idea why this is necessary, but ScalaCheck arbContainer
      //        demands it and can't seem to find one in this context.
      implicit def listToTraversable[A](as: List[A]): Traversable[A] = as

      "ConcatOp" >> {
        "array  || array" >> prop { (xs: List[BigInt], ys: List[BigInt]) =>
          val (xints, yints) = (xs map (Data._int(_)), ys map (Data._int(_)))
          binary(ConcatOp(_, _).embed, Data._arr(xints), Data._arr(yints), Data._arr(xints ::: yints))
        }

        "array  || string" >> prop { (xs: List[BigInt], y: String) =>
          val (xints, ystrs) = (xs map (Data._int(_)), y.toList map (c => Data._str(c.toString)))
          binary(ConcatOp(_, _).embed, Data._arr(xints), Data._str(y), Data._arr(xints ::: ystrs))
        }

        "string || array" >> prop { (x: String, ys: List[BigInt]) =>
          val (xstrs, yints) = (x.toList map (c => Data._str(c.toString)), ys map (Data._int(_)))
          binary(ConcatOp(_, _).embed, Data._str(x), Data._arr(yints), Data._arr(xstrs ::: yints))
        }

        "string || string" >> prop { (x: String, y: String) =>
          binary(ConcatOp(_, _).embed, Data._str(x), Data._str(y), Data._str(x + y))
        }
      }

      "MapProject" >> {
        """({"a":1}).a""" >> {
          binary(
            MapProject(_, _).embed,
            Data.Obj("a" -> Data.Int(1)),
            Data.Str("a"),
            Data.Int(1))
        }

        """({"a":1, "b":2}).b""" >> {
          binary(
            MapProject(_, _).embed,
            Data.Obj("a" -> Data.Int(1), "b" -> Data.Int(2)),
            Data.Str("b"),
            Data.Int(2))
        }

        """({"a":1, "b":2}).c""" >> {
          binary(
            MapProject(_, _).embed,
            Data.Obj("a" -> Data.Int(1), "b" -> Data.Int(2)),
            Data.Str("c"),
            Data.NA)
        }

        """({}).c""" >> {
          binary(
            MapProject(_, _).embed,
            Data.Obj(),
            Data.Str("c"),
            Data.NA)
        }
      }

      "DeleteKey" >> {
        "{a:1, b:2} delete .a" >> {
          binary(
            DeleteKey(_, _).embed,
            Data.Obj("a" -> Data.Int(1), "b" -> Data.Int(2)),
            Data.Str("a"),
            Data.Obj("b" -> Data.Int(2)))
        }

        "{a:1, b:2} delete .b" >> {
          binary(
            DeleteKey(_, _).embed,
            Data.Obj("a" -> Data.Int(1), "b" -> Data.Int(2)),
            Data.Str("b"),
            Data.Obj("a" -> Data.Int(1)))
        }

        "{a:1, b:2} delete .c" >> {
          binary(
            DeleteKey(_, _).embed,
            Data.Obj("a" -> Data.Int(1), "b" -> Data.Int(2)),
            Data.Str("c"),
            Data.Obj("a" -> Data.Int(1), "b" -> Data.Int(2)))
        }
      }

      "Meta" >> {
        // FIXME: Implement once we've switched to EJson in LogicalPlan.
        "returns metadata associated with a value" >> pending("Requires EJson.")
      }
    }

    "SetLib" >> {
      import SetLib._

      "Within" >> {
        "0 in [1, 2, 3]" >> {
          binary(Within(_, _).embed, Data.Int(0), Data.Arr(List(Data.Int(1), Data.Int(2), Data.Int(3))), Data.False)
        }

        "1 in [1, 2, 3]" >> {
          binary(Within(_, _).embed, Data.Int(1), Data.Arr(List(Data.Int(1), Data.Int(2), Data.Int(3))), Data.True)
        }

        "0 in []" >> {
          binary(Within(_, _).embed, Data.Int(0), Data.Arr(Nil), Data.False)
        }

        "[0] in [[1], 2, {a:3}, [0]]" >> {
          binary(
            Within(_, _).embed,
            Data.Arr(List(Data.Int(0))),
            Data.Arr(
              List(
                Data.Arr(List(Data.Int(1))),
                Data.Int(2),
                Data.Obj(ListMap("a" -> Data.Int(3))),
                Data.Arr(List(Data.Int(0))))),
            Data.True)
        }

        "[0, 1] in [[1], 2, {a:3}, [0, 1]]" >> {
          binary(
            Within(_, _).embed,
            Data.Arr(List(Data.Int(0), Data.Int(1))),
            Data.Arr(
              List(
                Data.Arr(List(Data.Int(1))),
                Data.Int(2),
                Data.Obj(ListMap("a" -> Data.Int(3))),
                Data.Arr(List(Data.Int(0), Data.Int(1))))),
            Data.True)
        }
      }
    }
  }
}
