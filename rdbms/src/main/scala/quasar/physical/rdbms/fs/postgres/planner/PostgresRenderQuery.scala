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

package quasar.physical.rdbms.fs.postgres.planner

import slamdata.Predef._

import quasar.common.JoinType._
import quasar.common.SortDir.{Ascending, Descending}
import quasar.{Data, DataCodec}
import quasar.fp.ski._
import quasar.DataCodec.Precise.TimeKey
import quasar.physical.rdbms.model._
import quasar.physical.rdbms.fs.postgres._
import quasar.physical.rdbms.planner.RenderQuery
import quasar.physical.rdbms.planner.sql._
import quasar.physical.rdbms.planner.sql.SqlExpr.Select._
import quasar.physical.rdbms.planner.sql.SqlExpr.Case._
import quasar.Planner.InternalError
import quasar.Planner.{NonRepresentableData, PlannerError}

import matryoshka._
import matryoshka.implicits._
import scalaz._
import Scalaz._

object PostgresRenderQuery extends RenderQuery {
  import SqlExpr._

  implicit val codec: DataCodec = DataCodec.Precise

  def asString[T[_[_]]: BirecursiveT](a: T[SqlExpr]): PlannerError \/ String = {

    // This is a workaround to transform "select _4 as some_alias" to "select row_to_json(_4) as some_alias" in order
    // to avoid working with record types.
    def aliasSelectionToJson(e: T[SqlExpr]): T[SqlExpr] = {
      (e.project match {
        case ea@ExprWithAlias(expr, alias) =>
          expr.project match {
            case Id(txt) =>
              ExprWithAlias(UnaryFunction(ToJson, Id[T[SqlExpr]](txt).embed).embed, alias)
            case _ => ea
          }
        case other => other
      }).embed
    }

    a.transCataT(aliasSelectionToJson).paraM(galg) ∘ (s => s"select row_to_json(row) from ($s) as row")
  }

  def alias(a: Option[SqlExpr.Id[String]]) = ~(a ∘ (i => s" as ${i.v}"))

  def rowAlias(a: Option[SqlExpr.Id[String]]) = ~(a ∘ (i => s" ${i.v}"))

  def buildJson(str: String): String =
    s"json_build_object($str)#>>'{}'"

  def text[T[_[_]]: BirecursiveT](pair: (T[SqlExpr], String)): String = {
    // The -> operator returns jsonb type, while ->> returns text. We need to choose one
    // depending on context, hence this function called in certain cases (see functionsNested.test)
    val (expr, str) = pair
    val toReplace = "->"
    val replacement = "->>"
    expr.project match {
      case Refs(_) =>
        val pos = str.lastIndexOf(toReplace)
        if (pos > -1 && !str.contains(replacement))
          s"${str.substring(0, pos)}$replacement${str.substring(pos + toReplace.length, str.length)}"
        else
          str
      case _ =>
        str
    }
  }

  def num[T[_[_]]: BirecursiveT](pair: (T[SqlExpr], String)): String = s"(${text(pair)})::numeric"

  def bool[T[_[_]]: BirecursiveT](pair: (T[SqlExpr], String)): String = s"(${text(pair)})::boolean"

  object TextExpr {
    def unapply[T[_[_]]: BirecursiveT](pair: (T[SqlExpr], String)): Option[String] =
      text(pair).some
  }

  object NumExpr {
    def unapply[T[_[_]]: BirecursiveT](pair: (T[SqlExpr], String)): Option[String] =
      TextExpr.unapply(pair).map(t => s"($t)::numeric")
  }

  object BoolExpr {
    def unapply[T[_[_]]: BirecursiveT](pair: (T[SqlExpr], String)): Option[String] =
      TextExpr.unapply(pair).map(t => s"($t)::boolean")
  }

  private def postgresArray(jsonArrayRepr: String) = s"array_to_json(ARRAY$jsonArrayRepr)"

  def galg[T[_[_]]: BirecursiveT]: GAlgebraM[(T[SqlExpr], ?), PlannerError \/ ?, SqlExpr, String] = {
    case Unreferenced() =>
    InternalError("Unexpected Unreferenced!", none).left
    case Null() => "null".right
    case SqlExpr.Id(v) =>
      s"""$v""".right
    case Table(v) =>
      v.right
    case AllCols() =>
      s"*".right
    case Refs(srcs) =>
      srcs.unzip(ι) match {
        case (Vector(_, last), Vector(key, value)) =>
          last.project match {
            case Constant(Data.Int(index)) => s"""$key->${index+1}""".right
            case _ =>
              val valueStripped = value.stripPrefix("'").stripSuffix("'")
              s"""$key."$valueStripped"""".right
          }
        case (_, key +: mid :+ last) =>
          val firstValStripped = ~mid.headOption.map(_.stripPrefix("'").stripSuffix("'"))
          val midTail = mid.drop(1)
          val midStr = if (midTail.nonEmpty)
            s"->${midTail.map(e => s"$e").intercalate("->")}"
          else
            ""
          s"""$key."$firstValStripped"$midStr->$last""".right
        case _ => InternalError.fromMsg(s"Cannot process Refs($srcs)").left
      }
    case Obj(m) =>
      buildJson(m.map {
        case ((_, k), (_, v)) => s"'$k', $v"
      }.mkString(",")).right
    case RegexMatches(TextExpr(e), TextExpr(pattern), caseInsensitive: Boolean) =>
      val op = if (caseInsensitive) "~*" else "~"
      s"($e $op $pattern)".right
    case IsNotNull((_, expr)) =>
      s"($expr notnull)".right
    case IfNull(exprs) =>
      s"coalesce(${exprs.map(e => text(e)).intercalate(", ")})".right
    case ExprWithAlias((_, expr), alias) =>
        s"""$expr as "$alias"""".right
    case ExprPair((_, s1), (_, s2)) =>
      s"$s1, $s2".right
    case ConcatStr(TextExpr(e1), TextExpr(e2))  =>
      s"$e1 || $e2".right
    case Time((_, expr)) =>
      buildJson(s"""{ "$TimeKey": $expr }""").right
    case NumericOp(sym, NumExpr(left), NumExpr(right)) =>
      s"($left $sym $right)".right
    case Mod(NumExpr(a1), NumExpr(a2)) =>
      s"mod($a1, $a2)".right
    case Pow(NumExpr(a1), NumExpr(a2)) =>
      s"power($a1, $a2)".right
    case And(BoolExpr(a1), BoolExpr(a2)) =>
      s"($a1 and $a2)".right
    case Or(BoolExpr(a1), BoolExpr(a2)) =>
      s"($a1 or $a2)".right
    case Neg(NumExpr(e)) =>
      s"(-$e)".right
    case Eq(TextExpr(a1), TextExpr(a2)) =>
      s"($a1 = $a2)".right
    case Neq(TextExpr(a1), TextExpr(a2)) =>
      s"($a1 != $a2)".right
    case Lt(NumExpr(a1), NumExpr(a2)) =>
      s"($a1 < $a2)".right
    case Lte(NumExpr(a1), NumExpr(a2)) =>
      s"($a1 <= $a2)".right
    case Gt(NumExpr(a1), NumExpr(a2)) =>
      s"($a1 > $a2)".right
    case Gte(NumExpr(a1), NumExpr(a2)) =>
      s"($a1 >= $a2)".right
    case WithIds((_, str))    => s"(row_number() over(), $str)".right
    case RowIds()        => "row_number() over()".right
    case Offset((_, from), NumExpr(count)) => s"$from OFFSET $count".right
    case Limit((_, from), NumExpr(count)) => s"$from LIMIT $count".right
    case Select(selection, from, joinOpt, filterOpt, order) =>
      val filter = ~(filterOpt ∘ (f => s" where ${f.v._2}"))
      val join = ~(joinOpt ∘ (j => {

        val joinKeyStr = j.keys.map {
          case (TextExpr(lK), TextExpr(rK)) => s"$lK = $rK"
        }.intercalate(" and ")

        val joinKeyExpr = if (j.keys.nonEmpty) s"on $joinKeyStr" else ""
        val joinTypeStr = if (j.keys.nonEmpty) {
          j.jType match {
            case Inner => "inner"
            case FullOuter => "full outer"
            case LeftOuter => "left outer"
            case RightOuter => "right outer"
          }
        } else "cross"
        s" $joinTypeStr join ${j.v._2} ${j.alias.v} $joinKeyExpr"
      }))
      val orderStr = order.map { o =>
        val dirStr = o.sortDir match {
          case Ascending => "asc"
          case Descending => "desc"
        }
        s"${o.v._2} $dirStr"
      }.mkString(", ")

      val orderByStr = if (order.nonEmpty)
        s" order by $orderStr"
      else
        ""

      val fromExpr = s" from ${from.v._2} ${from.alias.v}"
      s"(select ${selection.v._2}$fromExpr$join$filter$orderByStr)".right
    case Union((_, left), (_, right)) => s"($left UNION $right)".right
    case Constant(Data.Str(v)) =>
      val text = v.flatMap { case '\'' => "''"; case iv => iv.toString }.self
      s"'$text'".right
    case Constant(v) =>
      DataCodec.render(v).map{ rendered => v match {
        case _: Data.Arr => postgresArray(rendered)
        case _ => rendered
      }} \/> NonRepresentableData(v)
    case Case(wt, e) =>
      val wts = wt ∘ { case WhenThen(TextExpr(w), TextExpr(t)) => s"when ($w)::boolean then $t" }
      s"(case ${wts.intercalate(" ")} else ${text(e.v)} end)".right
    case Coercion(t, TextExpr(e)) => s"($e)::${t.mapToStringName}".right
    case ToArray(TextExpr(v)) => postgresArray(s"[$v]").right
    case UnaryFunction(fType, TextExpr(e)) =>
      val fName = fType match {
        case StrLower => "lower"
        case StrUpper => "upper"
        case ToJson => "row_to_json"
      }
      s"$fName($e)".right
    case BinaryFunction(fType, TextExpr(a1), TextExpr(a2)) => (fType match {
        case StrSplit => s"regexp_split_to_array($a1, $a2)"
        case ArrayConcat => s"(to_jsonb($a1) || to_jsonb($a2))"
        case Contains => s"($a1::text IN (SELECT jsonb_array_elements_text(to_jsonb($a2))))"
      }).right
    case TernaryFunction(fType, a1, a2, a3) => (fType match {
      case Search => s"(case when ${bool(a3)} then ${text(a1)} ~* ${text(a2)} else ${text(a1)} ~ ${text(a2)} end)"
      case Substring => s"substring(${text(a1)} from ((${text(a2)})::integer + 1) for (${text(a3)})::integer)"
    }).right
  }
}
