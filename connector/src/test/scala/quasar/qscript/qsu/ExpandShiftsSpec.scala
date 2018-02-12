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

package quasar.qscript.qsu

import quasar.Planner.PlannerError
import quasar.ejson.EJson
import slamdata.Predef.{Map => _, _}
import quasar.{Qspec, TreeMatchers}

import scalaz.\/
import quasar.qscript.{construction, Hole, ExcludeId, SrcHole}
import matryoshka._
import matryoshka.data._
import quasar.fp._
import Fix._
import org.specs2.matcher.{Expectable, MatchResult, Matcher}
import pathy.Path._

import scalaz.{EitherT, Need, StateT}
import scalaz.syntax.applicative._
import scalaz.syntax.either._
import scalaz.syntax.show._
import quasar.qscript.qsu.{QScriptUniform => QSU}
import QSU.Rotation
import QSUGraph.Extractors._

object ExpandShiftsSpec extends Qspec with QSUTTypes[Fix] with TreeMatchers {
  type QSU[A] = QScriptUniform[A]

  val qsu = QScriptUniform.DslT[Fix]
  val func = construction.Func[Fix]

  type F[A] = EitherT[StateT[Need, Long, ?], PlannerError, A]

  val hole: Hole = SrcHole
  def index(i: Int): FreeMapA[QAccess[Hole] \/ Int] =
    i.right[QAccess[Hole]].pure[FreeMapA]

  "convert singly nested LeftShift/ThetaJoin" in {
    val dataset = qsu.leftShift(
      qsu.read(rootDir </> file("dataset")),
      func.Hole,
      ExcludeId,
      func.RightTarget,
      Rotation.ShiftArray)

    val multiShift = QSUGraph.fromTree(qsu.multiLeftShift(
      dataset,
      List(
        (func.ProjectKeyS(func.Hole, "foo"), ExcludeId, Rotation.ShiftArray),
        (func.ProjectKeyS(func.Hole, "bar"), ExcludeId, Rotation.ShiftArray)
      ),
      func.Add(index(0), index(1))
    ))

    multiShift must expandTo {
      case qg@Map(
        LeftShift(
          LeftShift(
            LeftShift(
              Read(afile),
              shiftedReadStruct,
              ExcludeId,
              shiftedReadRepair,
              Rotation.ShiftArray
            ),
            projectFoo,
            ExcludeId,
            innerRepair,
            Rotation.ShiftArray
          ),
          projectBar,
          ExcludeId,
          outerRepair,
          Rotation.ShiftArray
        ),
        fm
      ) =>
        fm must beTreeEqual(
          func.Add(
            func.ProjectKeyS(func.Hole, "0"),
            func.ProjectKeyS(func.Hole, "1")))
        projectBar must beTreeEqual(
          func.ProjectKeyS(func.ProjectKeyS(func.Hole, "original"), "bar")
        )
        projectFoo must beTreeEqual(
          func.ProjectKeyS(func.Hole, "foo")
        )
        shiftedReadStruct must beTreeEqual(
          func.Hole
        )
        shiftedReadRepair must beTreeEqual(
          func.RightTarget
        )
        innerRepair must beTreeEqual(
          func.ConcatMaps(
            func.MakeMapS("original", func.AccessLeftTarget(Access.valueHole(_))),
            func.MakeMapS("0", func.RightTarget))
        )
        outerRepair must beTreeEqual(
          func.Cond(
            func.Eq(
              func.AccessLeftTarget(Access.id(IdAccess.identity[Fix[EJson]]('qsu0), _)),
              func.AccessLeftTarget(Access.id(IdAccess.identity[Fix[EJson]]('qsu1), _))),
            func.ConcatMaps(
              func.ConcatMaps(
                func.MakeMapS(
                  "original",
                  func.ProjectKeyS(func.AccessLeftTarget(Access.valueHole(_)), "original")),
                func.MakeMapS(
                  "0",
                  func.ProjectKeyS(func.AccessLeftTarget(Access.valueHole(_)), "0"))),
              func.MakeMapS("1", func.RightTarget)),
            func.Undefined
          )
        )
        ok
    }

    ok
  }

  "convert doubly nested LeftShift/ThetaJoin" in {
    val dataset = qsu.leftShift(
      qsu.read(rootDir </> file("dataset")),
      func.Hole,
      ExcludeId,
      func.RightTarget,
      Rotation.ShiftArray)

    val multiShift = QSUGraph.fromTree(qsu.multiLeftShift(
      dataset,
      List(
        (func.ProjectKeyS(func.Hole, "foo"), ExcludeId, Rotation.ShiftArray),
        (func.ProjectKeyS(func.Hole, "bar"), ExcludeId, Rotation.ShiftArray),
        (func.ProjectKeyS(func.Hole, "baz"), ExcludeId, Rotation.ShiftArray)
      ),
      func.Subtract(func.Add(index(0), index(1)), index(2))
    ))

    multiShift must expandTo {
      case qg @ Map(
        LeftShift(
          LeftShift(
            LeftShift(
              LeftShift(
                Read(afile),
                shiftedReadStruct,
                ExcludeId,
                shiftedReadRepair,
                Rotation.ShiftArray
              ),
              projectFoo,
              ExcludeId,
              innermostRepair,
              Rotation.ShiftArray
            ),
            projectBar,
            ExcludeId,
            innerRepair,
            Rotation.ShiftArray
          ),
          projectBaz,
          ExcludeId,
          outerRepair,
          Rotation.ShiftArray
        ),
        fm
      ) =>
        fm must beTreeEqual(
          func.Subtract(
            func.Add(
              func.ProjectKeyS(func.Hole, "0"),
              func.ProjectKeyS(func.Hole, "1")),
            func.ProjectKeyS(func.Hole, "2")))
        projectBaz must beTreeEqual(
          func.ProjectKeyS(func.ProjectKeyS(func.Hole, "original"), "baz")
        )
        projectBar must beTreeEqual(
          func.ProjectKeyS(func.ProjectKeyS(func.Hole, "original"), "bar")
        )
        projectFoo must beTreeEqual(
          func.ProjectKeyS(func.Hole, "foo")
        )
        shiftedReadStruct must beTreeEqual(
          func.Hole
        )
        shiftedReadRepair must beTreeEqual(
          func.RightTarget
        )
        innermostRepair must beTreeEqual(
          func.ConcatMaps(
            func.MakeMapS("original", func.AccessLeftTarget(Access.valueHole(_))),
            func.MakeMapS("0", func.RightTarget))
        )
        innerRepair must beTreeEqual(
          func.Cond(
            func.Eq(
              func.AccessLeftTarget(Access.id(IdAccess.identity[Fix[EJson]]('qsu0), _)),
              func.AccessLeftTarget(Access.id(IdAccess.identity[Fix[EJson]]('qsu1), _))),
            func.ConcatMaps(
              func.ConcatMaps(
                func.MakeMapS(
                  "original",
                  func.ProjectKeyS(func.AccessLeftTarget(Access.valueHole(_)), "original")),
                func.MakeMapS(
                  "0",
                  func.ProjectKeyS(func.AccessLeftTarget(Access.valueHole(_)), "0"))),
              func.MakeMapS("1", func.RightTarget)),
            func.Undefined))
        outerRepair must beTreeEqual(
          func.Cond(
            func.Eq(
              func.AccessLeftTarget(Access.id(IdAccess.identity[Fix[EJson]]('qsu1), _)),
              func.AccessLeftTarget(Access.id(IdAccess.identity[Fix[EJson]]('qsu2), _))),
            func.ConcatMaps(
              func.ConcatMaps(
                func.ConcatMaps(
                  func.MakeMapS(
                    "original",
                    func.ProjectKeyS(func.AccessLeftTarget(Access.valueHole(_)), "original")),
                  func.MakeMapS(
                    "0",
                    func.ProjectKeyS(func.AccessLeftTarget(Access.valueHole(_)), "0"))),
                func.MakeMapS(
                  "1",
                  func.ProjectKeyS(func.AccessLeftTarget(Access.valueHole(_)), "1"))),
              func.MakeMapS("2", func.RightTarget)),
            func.Undefined
        ))
        ok
    }

    ok
  }

  def expandTo(pf: PartialFunction[QSUGraph, MatchResult[_]]): Matcher[QSUGraph] =
    new Matcher[QSUGraph] {
      def apply[S <: QSUGraph](s: Expectable[S]): MatchResult[S] = {
        val actual =
          ApplyProvenance[Fix, F](s.value).flatMap(
           ExpandShifts[Fix, F]
          ).run.eval(0).value

        val mapped = actual.toOption.flatMap(aq => pf.lift(aq.graph)) map { r =>
          result(
            r.isSuccess,
            s.description + " is correct: " + r.message,
            s.description + " is incorrect: " + r.message,
            s)
        }

        // TODO Show[QSUGraph[Fix]]
        mapped.getOrElse(
          failure(s"${actual.shows} did not match expected pattern", s))
      }
    }
}
