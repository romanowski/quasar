/*
 * Copyright 2014–2016 SlamData Inc.
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

package quasar.physical.marklogic

import quasar.SKI.κ
import quasar.NameGenerator
import quasar.Planner.PlannerError
import quasar.fp.{freeCataM, interpretM, ShowT}
import quasar.qscript._
import quasar.physical.marklogic.xquery.{PrologW, XQuery}

import matryoshka.Recursive
import scalaz._, Scalaz._

package object qscript {
  // TODO: Maybe a ML-specific error type here?
  type MonadPlanErr[F[_]] = MonadError_[F, PlannerError]
  type MarkLogicPlanner[QS[_]] = Planner[QS, XQuery]

  object MarkLogicPlanner {
    implicit def qScriptCore[T[_[_]]: Recursive: ShowT]: MarkLogicPlanner[QScriptCore[T, ?]] =
      new QScriptCorePlanner[T]

    implicit def constDeadEnd: MarkLogicPlanner[Const[DeadEnd, ?]] =
      new DeadEndPlanner

    implicit def constRead: MarkLogicPlanner[Const[Read, ?]] =
      new ReadPlanner

    implicit def constShiftedRead: MarkLogicPlanner[Const[ShiftedRead, ?]] =
      new ShiftedReadPlanner

    implicit def projectBucket[T[_[_]]]: MarkLogicPlanner[ProjectBucket[T, ?]] =
      new ProjectBucketPlanner[T]

    implicit def thetajoin[T[_[_]]]: MarkLogicPlanner[ThetaJoin[T, ?]] =
      new ThetaJoinPlanner[T]

    implicit def equiJoin[T[_[_]]]: MarkLogicPlanner[EquiJoin[T, ?]] =
      new EquiJoinPlanner[T]
  }

  def mapFuncXQuery[T[_[_]]: Recursive: ShowT, F[_]: NameGenerator: PrologW: MonadPlanErr](fm: FreeMap[T], src: XQuery): F[XQuery] =
    planMapFunc[T, F, Hole](fm)(κ(src))

  def mergeXQuery[T[_[_]]: Recursive: ShowT, F[_]: NameGenerator: PrologW: MonadPlanErr](jf: JoinFunc[T], l: XQuery, r: XQuery): F[XQuery] =
    planMapFunc[T, F, JoinSide](jf) {
      case LeftSide  => l
      case RightSide => r
    }

  def planMapFunc[T[_[_]]: Recursive: ShowT, F[_]: NameGenerator: PrologW: MonadPlanErr, A](
    freeMap: Free[MapFunc[T, ?], A])(
    recover: A => XQuery
  ): F[XQuery] =
    freeCataM(freeMap)(interpretM(a => recover(a).point[F], MapFuncPlanner[T, F]))

  def rebaseXQuery[T[_[_]]: Recursive: ShowT, F[_]: NameGenerator: PrologW: MonadPlanErr](
    fqs: FreeQS[T], src: XQuery
  ): F[XQuery] = {
    import MarkLogicPlanner._
    freeCataM(fqs)(interpretM(κ(src.point[F]), Planner[QScriptTotal[T, ?], XQuery].plan[F]))
  }
}
