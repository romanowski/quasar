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

package quasar.physical.rdbms.planner

import quasar.fp.ski._
import quasar.NameGenerator
import quasar.Planner.PlannerErrorME
import quasar.physical.rdbms.planner.sql.{SqlExpr, genId}
import SqlExpr._
import quasar.qscript.{EquiJoin, FreeMap, JoinFunc, LeftSide, MapFunc, QScriptTotal, RightSide}
import quasar.physical.rdbms.planner.sql.SqlExpr.Select.AllCols
import matryoshka._
import matryoshka.data._
import matryoshka.implicits._
import matryoshka.patterns._

import scalaz._
import Scalaz._

class EquiJoinPlanner[T[_[_]]: BirecursiveT: ShowT,
F[_]: Monad: NameGenerator: PlannerErrorME](
    mapFuncPlanner: Planner[T, F, MapFunc[T, ?]])
    extends Planner[T, F, EquiJoin[T, ?]] {

  private def processJoinFunc(
      f: JoinFunc[T],
      leftAlias: SqlExpr[T[SqlExpr]],
      rightAlias: SqlExpr[T[SqlExpr]]
  ): F[T[SqlExpr]] =
    f.cataM(interpretM({
      case LeftSide  => leftAlias.embed.η[F]
      case RightSide => rightAlias.embed.η[F]
    }, mapFuncPlanner.plan))

  private def processFreeMap(f: FreeMap[T],
                             alias: SqlExpr[T[SqlExpr]]): F[T[SqlExpr]] =
    f.cataM(interpretM(κ(alias.embed.η[F]), mapFuncPlanner.plan))

  def * : T[SqlExpr] = AllCols[T[SqlExpr]]().embed

  val unref: T[SqlExpr] = SqlExpr.Unreferenced[T[SqlExpr]]().embed

  def plan: AlgebraM[F, EquiJoin[T, ?], T[SqlExpr]] = {
    case EquiJoin(src, lBranch, rBranch, keys, joinType, combine) =>
      val compile = Planner[T, F, QScriptTotal[T, ?]].plan

      for {
        leftAlias <- genId[T[SqlExpr], F]
        rightAlias <- genId[T[SqlExpr], F]
        left <- lBranch.cataM(interpretM(κ(src.point[F]), compile))
        right <- rBranch.cataM(interpretM(κ(src.point[F]), compile))
        combined <- processJoinFunc(combine, leftAlias, rightAlias)
        keyExprs <-
          keys.traverse {
            case (lFm, rFm) =>
              (processFreeMap(lFm, leftAlias) |@| processFreeMap(rFm, rightAlias))(scala.Tuple2.apply)
          }
      } yield {

        val selectionExpr = combined.project match {
          case e@ExprPair(a, b) =>
            (a.project, b.project) match {
              case (SqlExpr.Id(_), SqlExpr.Id(_)) => *
              case _ => e.embed
            }
          case other =>
            other.embed
        }

        Select(
          selection = Selection(selectionExpr, none),
          from = From(left, leftAlias),
          join = Join(right, keyExprs, joinType, rightAlias).some,
          filter = none,
          orderBy = nil
        ).embed
      }
  }
}
