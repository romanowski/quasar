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

package quasar.qscript

import matryoshka.data.Fix
import slamdata.Predef.{Eq => _, _}
import matryoshka.{Hole => _, _}
import matryoshka.implicits._
import quasar.{Data, DSLTree, RenderDSL, Type, ejson}
import quasar.contrib.pathy.{ADir, AFile}
import quasar.ejson.EJson
import quasar.fp._
import quasar.fp.ski._
import slamdata.Predef

import scalaz.{Const, Coproduct, Free, Functor}
import scalaz.syntax.bifunctor._
import scalaz.syntax.either._
import scalaz.syntax.std.option._
import scalaz.syntax.show._
import scalaz.syntax.std.tuple._
import scalaz.std.anyVal._
import scalaz.std.option._
import scalaz.std.tuple._

@SuppressWarnings(Array("org.wartremover.warts.Recursion"))
object RenderQScriptDSL {
  type RenderQScriptDSL[A] = (String, A) => DSLTree
  implicit def qscriptInstance[T[_[_]]: RecursiveT, F[_]: Functor]
  (implicit I: Injectable.Aux[F, QScriptTotal[T, ?]]): RenderDSL[T[F]] =
    new RenderDSL[T[F]] {
      // hard-coded here to fix.
      def toDsl(a: T[F]) = fixQSRender.apply("fix", a.transCata[Fix[QScriptTotal[T, ?]]](I.inject(_)))
    }

  def delayRenderQScriptDSL[T[_[_]]: RecursiveT, F[_]: Functor]
  (D: Delay[RenderQScriptDSL, F]): RenderQScriptDSL[T[F]] = {
    def toDsl(base: String, a: T[F]): DSLTree = D[T[F]](toDsl)("fix", a.project)
    toDsl
  }

  def freeDelayRenderQScriptDSL[T[_[_]]: RecursiveT, F[_]: Functor, A]
  (D: Delay[RenderQScriptDSL, F], A: RenderQScriptDSL[A]): RenderQScriptDSL[Free[F, A]] = {
    def toDsl(base: String, a: Free[F, A]): DSLTree =
      a.resume.fold(D[Free[F, A]](toDsl)("free", _), A("free", _))
    toDsl
  }

  def delayRenderQScriptDSLFreeDelay[F[_]]
  (implicit D: Delay[RenderQScriptDSL, F], F: Functor[F]): Delay[RenderQScriptDSL, Free[F, ?]] =
    new Delay[RenderQScriptDSL, Free[F, ?]] {
      def apply[A](A: RenderQScriptDSL[A]) = {
        def toDsl(base: String, a: Free[F, A]): DSLTree =
          a.resume.fold(D[Free[F, A]](toDsl)("free", _), A("free", _))
        toDsl
      }
    }

  def coproduct[F[_], G[_]]
  (delF: Delay[RenderQScriptDSL, F], delG: Delay[RenderQScriptDSL, G]): Delay[RenderQScriptDSL, Coproduct[F, G, ?]] =
    new Delay[RenderQScriptDSL, Coproduct[F, G, ?]] {
      def apply[A](rec: RenderQScriptDSL[A]) = {
        (base: Predef.String, a: Coproduct[F, G, A]) =>
          a.run.fold(delF(rec)(base, _), delG(rec)(base, _))
      }
    }

  def ejsonRenderQScriptDSLDelay: Delay[RenderQScriptDSL, EJson] = new Delay[RenderQScriptDSL, EJson] {
    def apply[A](fa: RenderQScriptDSL[A]): RenderQScriptDSL[EJson[A]] = {
      (base: String, a: EJson[A]) =>
        val base = "json"
        val (label, children) = a.run.fold({
          case ejson.Meta(value, meta) => ("meta", fa(base, value).right :: fa(base, meta).right :: Nil)
          case ejson.Map(value)        => ("map",
            DSLTree("", "List", (value.map(t => DSLTree("", "", t.umap(fa(base, _).right).toIndexedSeq.toList.some).right).some)).right :: Nil)
          case ejson.Byte(value)       => ("byte", value.toString.left :: Nil)
          case ejson.Char(value)       => ("char", ("'" + value.toString + "'").left :: Nil)
          case ejson.Int(value)        => ("int", value.toString.left :: Nil)
        }, {
          case ejson.Arr(value)  => ("arr", DSLTree("", "List", value.map(fa(base, _).right).some).right :: Nil)
          case ejson.Null()      => ("nul", Nil)
          case ejson.Bool(value) => ("bool", value.toString.left :: Nil)
          case ejson.Str(value)  => ("str", ("\"" + value + "\"").left :: Nil)
          case ejson.Dec(value)  => ("dec", value.toString.left :: Nil)
        })
        DSLTree(base, label, children.some)
    }
  }

  def eJsonRenderQScriptDSL[T[_[_]]](implicit T: RecursiveT[T]): RenderQScriptDSL[T[EJson]] =
    delayRenderQScriptDSL(ejsonRenderQScriptDSLDelay)

  def showType(ty: Type): String = ty match {
    case Type.Const(d) => "Type.Const(" + showData(d) + ")"
    case Type.Arr(types) => "Type.Arr(" + types.map(showType).mkString("List(", ", ", ")") + ")"
    case Type.FlexArr(min, max, mbrs) =>
      "Type.FlexArr(" + min.shows + ", " + max.shows + ", "  + showType(mbrs) + ")"
    case Type.Obj(assocs, unkns) =>
      assocs.map { case (k, v) => ("\"" + k + "\"", showType(v)) }.mkString("Type.Obj(Map(", ", ", "), " +
        unkns.fold("None")(t => "Some(" + showType(t) + ")") + ")")
    case Type.Coproduct(l, r) =>
      "Type.Coproduct(" + showType(l) + ", " + showType(r) + ")"
    case x => "Type." + x.shows
  }

  def showData(data: Data): String = data match {
    case Data.Arr(a) => a.map(showData).mkString("Data.Arr(List(", ", ", "))")
    case Data.Binary(b) => b.mkString("Data.Binary(scalaz.ImmutableArray.fromArray(Array[Byte](", ", ", ")))")
    case Data.Bool(b) => "Data.Bool(" + b.shows + ")"
    case Data.Date(d) => "Data.Date(java.time.LocalDate.parse(\"" + d.toString + "\"))"
    case Data.Dec(d) => "Data.Dec(BigDecimal(\"" + d.toString + "\"))"
    case Data.Id(id) => "Data.Id(" + id + ")"
    case Data.Int(i) => "Data.Int(BigInt(\"" + i.toString + "\"))"
    case Data.Interval(i) => "Data.Interval(java.time.Duration.parse(\"" + i.toString + "\"))"
    case Data.NA => "Data.NA"
    case Data.Null => "Data.Null"
    case Data.Obj(o) => o.mapValues(showData).mkString("Data.Obj(", ", ", ")")
    case Data.Set(s) => s.mkString("Data.Set(List(", ", ", "))")
    case Data.Str(s) => "Data.Str(\"" + s + "\")"
    case Data.Time(t) => "Data.Time(java.time.LocalTime.parse(\"" + t.toString + "\"))"
    case Data.Timestamp(ts) => "Data.Timestamp(java.time.Instant.parse(\"" + ts.toString + "\"))"
  }

  def mapFuncRenderQScriptDSLDelay[T[_[_]]: RecursiveT]: Delay[RenderQScriptDSL, MapFunc[T, ?]] =
    new Delay[RenderQScriptDSL, MapFunc[T, ?]] {
      import MapFuncsCore._, MapFuncsDerived._
      def apply[A](fa: RenderQScriptDSL[A]) = {
        (base: String, mf: MapFunc[T, A]) =>
          val prefix = "func"
          val (label, children) = mf.run.fold({
            case Constant(ejson) => ("Constant", (eJsonRenderQScriptDSL[T].apply(base, ejson).right :: Nil).some)
            case Undefined()     => ("Undefined", none)
            case JoinSideName(n) => ("JoinSideName", (n.shows.left :: Nil).some)
            case Now()           => ("Now", none)

            case ExtractCentury(a1)        => ("ExtractCentury", (fa(base, a1).right :: Nil).some)
            case ExtractDayOfMonth(a1)     => ("ExtractDayOfMonth", (fa(base, a1).right :: Nil).some)
            case ExtractDecade(a1)         => ("ExtractDecade", (fa(base, a1).right :: Nil).some)
            case ExtractDayOfWeek(a1)      => ("ExtractDayOfWeek", (fa(base, a1).right :: Nil).some)
            case ExtractDayOfYear(a1)      => ("ExtractDayOfYear", (fa(base, a1).right :: Nil).some)
            case ExtractEpoch(a1)          => ("ExtractEpoch", (fa(base, a1).right :: Nil).some)
            case ExtractHour(a1)           => ("ExtractHour", (fa(base, a1).right :: Nil).some)
            case ExtractIsoDayOfWeek(a1)   => ("ExtractIsoDayOfWeek", (fa(base, a1).right :: Nil).some)
            case ExtractIsoYear(a1)        => ("ExtractIsoYear", (fa(base, a1).right :: Nil).some)
            case ExtractMicroseconds(a1)   => ("ExtractMicroseconds", (fa(base, a1).right :: Nil).some)
            case ExtractMillennium(a1)     => ("ExtractMillennium", (fa(base, a1).right :: Nil).some)
            case ExtractMilliseconds(a1)   => ("ExtractMilliseconds", (fa(base, a1).right :: Nil).some)
            case ExtractMinute(a1)         => ("ExtractMinute", (fa(base, a1).right :: Nil).some)
            case ExtractMonth(a1)          => ("ExtractMonth", (fa(base, a1).right :: Nil).some)
            case ExtractQuarter(a1)        => ("ExtractQuarter", (fa(base, a1).right :: Nil).some)
            case ExtractSecond(a1)         => ("ExtractSecond", (fa(base, a1).right :: Nil).some)
            case ExtractTimezone(a1)       => ("ExtractTimezone", (fa(base, a1).right :: Nil).some)
            case ExtractTimezoneHour(a1)   => ("ExtractTimezoneHour", (fa(base, a1).right :: Nil).some)
            case ExtractTimezoneMinute(a1) => ("ExtractTimezoneMinute", (fa(base, a1).right :: Nil).some)
            case ExtractWeek(a1)           => ("ExtractWeek", (fa(base, a1).right :: Nil).some)
            case ExtractYear(a1)           => ("ExtractYear", (fa(base, a1).right :: Nil).some)
            case Date(a1)                  => ("Date", (fa(base, a1).right :: Nil).some)
            case Time(a1)                  => ("Time", (fa(base, a1).right :: Nil).some)
            case Timestamp(a1)             => ("Timestamp", (fa(base, a1).right :: Nil).some)
            case Interval(a1)              => ("Interval", (fa(base, a1).right :: Nil).some)
            case StartOfDay(a1)            => ("StartOfDay", (fa(base, a1).right :: Nil).some)
            case TemporalTrunc(a1, a2)     => ("TemporalTrunc", (DSLTree("TemporalPart", a1.shows, none).right :: fa(base, a2).right :: Nil).some)
            case TimeOfDay(a1)             => ("TimeOfDay", (fa(base, a1).right :: Nil).some)
            case ToTimestamp(a1)           => ("ToTimestamp", (fa(base, a1).right :: Nil).some)
            case TypeOf(a1)                => ("TypeOf", (fa(base, a1).right :: Nil).some)
            case ToId(a1)                  => ("ToId", (fa(base, a1).right :: Nil).some)
            case Negate(a1)                => ("Negate", (fa(base, a1).right :: Nil).some)
            case Not(a1)                   => ("Not", (fa(base, a1).right :: Nil).some)
            case Length(a1)                => ("Length", (fa(base, a1).right :: Nil).some)
            case Lower(a1)                 => ("Lower", (fa(base, a1).right :: Nil).some)
            case Upper(a1)                 => ("Upper", (fa(base, a1).right :: Nil).some)
            case Bool(a1)                  => ("Bool", (fa(base, a1).right :: Nil).some)
            case Integer(a1)               => ("Integer", (fa(base, a1).right :: Nil).some)
            case Decimal(a1)               => ("Decimal", (fa(base, a1).right :: Nil).some)
            case Null(a1)                  => ("Null", (fa(base, a1).right :: Nil).some)
            case ToString(a1)              => ("ToString", (fa(base, a1).right :: Nil).some)
            case MakeArray(a1)             => ("MakeArray", (fa(base, a1).right :: Nil).some)
            case Meta(a1)                  => ("Meta", (fa(base, a1).right :: Nil).some)

            case Add(a1, a2)          => ("Add", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case Multiply(a1, a2)     => ("Multiply", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case Subtract(a1, a2)     => ("Subtract", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case Divide(a1, a2)       => ("Divide", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case Modulo(a1, a2)       => ("Modulo", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case Power(a1, a2)        => ("Power", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case Eq(a1, a2)           => ("Eq", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case Neq(a1, a2)          => ("Neq", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case Lt(a1, a2)           => ("Lt", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case Lte(a1, a2)          => ("Lte", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case Gt(a1, a2)           => ("Gt", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case Gte(a1, a2)          => ("Gte", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case IfUndefined(a1, a2)  => ("IfUndefined", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case And(a1, a2)          => ("And", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case Or(a1, a2)           => ("Or", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case Within(a1, a2)       => ("Within", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case MakeMap(a1, a2)      => ("MakeMap", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case ConcatMaps(a1, a2)   => ("ConcatMaps", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case ProjectIndex(a1, a2) => ("ProjectIndex", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case ProjectKey(a1, a2)   => ("ProjectKey", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case DeleteKey(a1, a2)    => ("DeleteKey", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case ConcatArrays(a1, a2) => ("ConcatArrays", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case Range(a1, a2)        => ("Range", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            case Split(a1, a2)        => ("Split", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)

            case Between(a1, a2, a3)    => ("Between", (fa(base, a1).right :: fa(base, a2).right :: fa(base, a3).right :: Nil).some)
            case Cond(a1, a2, a3)       => ("Cond", (fa(base, a1).right :: fa(base, a2).right :: fa(base, a3).right :: Nil).some)
            case Search(a1, a2, a3)     => ("Search", (fa(base, a1).right :: fa(base, a2).right :: fa(base, a3).right :: Nil).some)
            case Substring(a1, a2, a3)  => ("Substring", (fa(base, a1).right :: fa(base, a2).right :: fa(base, a3).right :: Nil).some)
            case Guard(a1, tpe, a2, a3) =>
              ("Guard", (fa(base, a1).right :: showType(tpe).left :: fa(base, a2).right :: fa(base, a3).right :: Nil).some)
          },
            {
              case Abs(a1)   => ("Abs", (fa(base, a1).right :: Nil).some)
              case Ceil(a1)  => ("Ceil", (fa(base, a1).right :: Nil).some)
              case Floor(a1) => ("Floor", (fa(base, a1).right :: Nil).some)
              case Trunc(a1) => ("Trunc", (fa(base, a1).right :: Nil).some)
              case Round(a1) => ("Round", (fa(base, a1).right :: Nil).some)

              case FloorScale(a1, a2) => ("FloorScale", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
              case CeilScale(a1, a2)  => ("CeilScale", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
              case RoundScale(a1, a2) => ("RoundScale", (fa(base, a1).right :: fa(base, a2).right :: Nil).some)
            })
          DSLTree(prefix, label, children)
      }
    }

  def freeMapARender[T[_[_]]: RecursiveT, A](A: RenderQScriptDSL[A]): RenderQScriptDSL[FreeMapA[T, A]] = {
    def toDsl(base: String, mf: FreeMapA[T, A]): DSLTree =
      mf.resume.fold(mapFuncRenderQScriptDSLDelay[T].apply[FreeMapA[T, A]](toDsl)(base, _), A(base, _))
    toDsl
  }

  def holeRender(base: String): RenderQScriptDSL[Hole] = {
    (_, a: Hole) => DSLTree(base, "Hole", none)
  }

  def joinSideRender(base: String): RenderQScriptDSL[JoinSide] = {
    (_, a: JoinSide) => DSLTree(base, a match {
      case LeftSide => "LeftSide"
      case RightSide => "RightSide"
    }, none)
  }

  def freeMapRender[T[_[_]]: RecursiveT] = freeMapARender(holeRender("func"))
  def joinFuncRender[T[_[_]]: RecursiveT] = freeMapARender(joinSideRender("func"))
  def freeMapReduceIndexRender[T[_[_]]: RecursiveT] = freeMapARender(reduceIndexRender("func"))

  def reduceIndexRender(base: String): RenderQScriptDSL[ReduceIndex] = {
    (_, a: ReduceIndex) =>
      val suffix = a.idx.fold(κ(".left"), κ(".right"))
      val idx = a.idx.merge
      DSLTree(base, "ReduceIndex", ((idx.toString + suffix).left :: Nil).some)
  }

  def qscriptTotalRenderDelay[T[_[_]]: RecursiveT]: Delay[RenderQScriptDSL, QScriptTotal[T, ?]] =
    coproduct(qscriptCoreRenderDelay[T],
      coproduct(projectBucketRenderDelay[T],
        coproduct(thetaJoinRenderDelay[T],
          coproduct(equiJoinRenderDelay[T],
            coproduct(shiftedReadDirRenderDelay,
              coproduct(shiftedReadFileRenderDelay,
                coproduct(readDirRenderDelay,
                  coproduct(readFileRenderDelay,
                    deadEndRenderDelay))))))))

  def freeQSRender[T[_[_]]: RecursiveT]: RenderQScriptDSL[FreeQS[T]] =
    freeDelayRenderQScriptDSL[T, QScriptTotal[T, ?], Hole](qscriptTotalRenderDelay[T], holeRender("free"))

  def fixQSRender[T[_[_]]: RecursiveT]: RenderQScriptDSL[Fix[QScriptTotal[T, ?]]] =
    delayRenderQScriptDSL(qscriptTotalRenderDelay[T])

  def reduceFuncRender[T[_[_]]: RecursiveT]: RenderQScriptDSL[ReduceFunc[FreeMap[T]]] = { (base, rf) =>
    val freeMap = freeMapRender[T]
    rf match {
      case ReduceFuncs.Count(a) => DSLTree("ReduceFuncs", "Count", (freeMap(base, a).right :: Nil).some)
      case ReduceFuncs.Sum(a) => DSLTree("ReduceFuncs", "Sum", (freeMap(base, a).right :: Nil).some)
      case ReduceFuncs.Min(a) => DSLTree("ReduceFuncs", "Min", (freeMap(base, a).right :: Nil).some)
      case ReduceFuncs.Max(a) => DSLTree("ReduceFuncs", "Max", (freeMap(base, a).right :: Nil).some)
      case ReduceFuncs.Avg(a) => DSLTree("ReduceFuncs", "Avg", (freeMap(base, a).right :: Nil).some)
      case ReduceFuncs.Arbitrary(a) => DSLTree("ReduceFuncs", "Arbitrary", (freeMap(base, a).right :: Nil).some)
      case ReduceFuncs.First(a) => DSLTree("ReduceFuncs", "First", (freeMap(base, a).right :: Nil).some)
      case ReduceFuncs.Last(a) => DSLTree("ReduceFuncs", "Last", (freeMap(base, a).right :: Nil).some)
      case ReduceFuncs.UnshiftArray(a) => DSLTree("ReduceFuncs", "UnshiftArray", (freeMap(base, a).right :: Nil).some)
      case ReduceFuncs.UnshiftMap(a1, a2) =>
        DSLTree("ReduceFuncs", "UnshiftMap", (freeMap(base, a1).right :: freeMap(base, a2).right :: Nil).some)
    }
  }

  def qscriptCoreRenderDelay[T[_[_]]: RecursiveT]: Delay[RenderQScriptDSL, QScriptCore[T, ?]] =
    new Delay[RenderQScriptDSL, QScriptCore[T, ?]] {
      def apply[A](A: RenderQScriptDSL[A]): RenderQScriptDSL[QScriptCore[T, A]] = {
        val freeMap = freeMapRender[T]
        val joinFunc = joinFuncRender[T]
        val reduceIndex = freeMapReduceIndexRender[T]
        val freeQS = freeQSRender[T]
        (base: String, qsc: QScriptCore[T, A]) => qsc match {
          case Map(src, f) =>
            DSLTree(base, "Map", (A(base, src).right :: freeMap(base, f).right :: Nil).some)

          case LeftShift(src, struct, idStatus, shiftType, repair) =>
            DSLTree(base, "LeftShift",
              (A(base, src).right ::
                freeMap(base, struct).right ::
                idStatus.shows.left ::
                ("ShiftType." + shiftType.shows).left ::
                joinFunc(base, repair).right ::
                Nil).some)

          case Reduce(src, bucket, reducers, repair) =>
            val bucketArg = DSLTree("", "List", bucket.map(freeMap(base, _).right).some)
            val reducersArg = DSLTree("", "List", reducers.map(reduceFuncRender[T].apply(base, _).right).some)
            DSLTree(base, "Reduce", (A(base, src).right :: bucketArg.right :: reducersArg.right :: reduceIndex(base, repair).right :: Nil).some)

          case Sort(src, bucket, order) =>
            val args = A(base, src).right ::
              DSLTree("", "List", bucket.map(freeMap(base, _).right).some).right ::
              DSLTree("", "NonEmptyList",
                order.map { case (f, o) =>
                  DSLTree("", "", (freeMap(base, f).right :: DSLTree("SortDir", o.shows, none).right :: Nil).some).right
                }.list.toList.some).right :: Nil
            DSLTree(base, "Sort", args.some)

          case Union(src, lBranch, rBranch) =>
            val args = A(base, src).right ::
              freeQS(base, lBranch).right ::
              freeQS(base, rBranch).right ::
              Nil
            DSLTree(base, "Union", args.some)

          case Filter(src, f) =>
            val args = A(base, src).right :: freeMap(base, f).right :: Nil
            DSLTree(base, "Filter", args.some)

          case Subset(src, from, op, count) =>
            val args = A(base, src).right ::
              freeQS(base, from).right ::
              op.shows.left ::
              freeQS(base, count).right ::
              Nil
            DSLTree(base, "Subset", args.some)

          case Unreferenced() =>
            DSLTree(base, "Unreferenced", none)
        }
      }
    }

  def projectBucketRenderDelay[T[_[_]]: RecursiveT]: Delay[RenderQScriptDSL, ProjectBucket[T, ?]] =
    new Delay[RenderQScriptDSL, ProjectBucket[T, ?]] {
      val freeMap = freeMapRender[T]
      def apply[A](A: RenderQScriptDSL[A]) = {
        (base: String, a: ProjectBucket[T, A]) => a match {
          case BucketKey(src, value, name) =>
            val args = A(base, src).right ::
              freeMap(base, value).right ::
              freeMap(base, name).right ::
              Nil
            DSLTree(base, "BucketKey", args.some)

          case BucketIndex(src, value, index) =>
            val args = A(base, src).right ::
              freeMap(base, value).right ::
              freeMap(base, index).right ::
              Nil
            DSLTree(base, "BucketIndex", args.some)
        }
      }
    }

  def thetaJoinRenderDelay[T[_[_]]: RecursiveT]: Delay[RenderQScriptDSL, ThetaJoin[T, ?]] =
    new Delay[RenderQScriptDSL, ThetaJoin[T, ?]] {
      def apply[A](A: RenderQScriptDSL[A]) = {
        (base: String, a: ThetaJoin[T, A]) => a match {
          case ThetaJoin(src, lBranch, rBranch, on, f, combine) =>
            val joinFunc = joinFuncRender[T]
            val freeQS = freeQSRender[T]
            val args = A(base, src).right ::
              freeQS(base, lBranch).right ::
              freeQS(base, rBranch).right ::
              joinFunc(base, on).right ::
              DSLTree("JoinType", f.shows, none).right ::
              joinFunc(base, combine).right ::
              Nil
            DSLTree(base, "ThetaJoin", args.some)
        }
      }
    }

  def equiJoinRenderDelay[T[_[_]]: RecursiveT]: Delay[RenderQScriptDSL, EquiJoin[T, ?]] =
    new Delay[RenderQScriptDSL, EquiJoin[T, ?]] {
      def apply[A](A: RenderQScriptDSL[A]) = {
        (base: String, a: EquiJoin[T, A]) => a match {
          case EquiJoin(src, lBranch, rBranch, key, f, combine) =>
            val freeMap = freeMapRender[T]
            val joinFunc = joinFuncRender[T]
            val freeQS = freeQSRender[T]
            val args = A(base, src).right ::
              freeQS(base, lBranch).right ::
              freeQS(base, rBranch).right ::
              DSLTree("", "List", key.map { case (k, v) => DSLTree("", "", (freeMap(base, k).right :: freeMap(base, v).right :: Nil).some).right }.some).right ::
              DSLTree("JoinType", f.shows, none).right ::
              joinFunc(base, combine).right ::
              Nil
            DSLTree(base, "EquiJoin", args.some)
        }
      }
    }

  def delayRenderConst[B](render: RenderQScriptDSL[B]): Delay[RenderQScriptDSL, Const[B, ?]] =
    new Delay[RenderQScriptDSL, Const[B, ?]] {
      def apply[A](fa: RenderQScriptDSL[A]): RenderQScriptDSL[Const[B, A]] = {
        (b, a) => render(b, a.getConst)
      }
    }

  def readFileRenderDelay: Delay[RenderQScriptDSL, Const[Read[AFile], ?]] =
    delayRenderConst(
      (base: String, a: Read[AFile]) =>
        DSLTree(base, "Read[AFile]", (a.path.shows.left :: Nil).some)
    )

  def readDirRenderDelay: Delay[RenderQScriptDSL, Const[Read[ADir], ?]] =
    delayRenderConst(
      (base: String, a: Read[ADir]) =>
        DSLTree(base, "Read[ADir]", (a.path.shows.left :: Nil).some)
    )

  def shiftedReadFileRenderDelay: Delay[RenderQScriptDSL, Const[ShiftedRead[AFile], ?]] =
    delayRenderConst(
      (base: String, a: ShiftedRead[AFile]) =>
        DSLTree(base, "ShiftedRead[AFile]", (a.path.shows.left :: a.idStatus.shows.left :: Nil).some)
    )

  def shiftedReadDirRenderDelay: Delay[RenderQScriptDSL, Const[ShiftedRead[ADir], ?]] =
    delayRenderConst(
      (base: String, a: ShiftedRead[ADir]) =>
        DSLTree(base, "ShiftedRead[ADir]", (a.path.shows.left :: a.idStatus.shows.left :: Nil).some)
    )

  def deadEndRenderDelay: Delay[RenderQScriptDSL, Const[DeadEnd, ?]] =
    delayRenderConst(
      (base: String, a: DeadEnd) =>
        DSLTree(base, "Root", none)
    )
}
