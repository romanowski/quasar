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

package quasar.qscript.analysis

import slamdata.Predef.{Map => _, _}

import quasar.contrib.pathy.APath
import quasar.fp._, ski._
import quasar.qscript._

import matryoshka.{Hole => _, _}
import matryoshka.patterns._
import matryoshka.implicits._
import matryoshka.data._
import scalaz._, Scalaz._
import simulacrum.typeclass

@typeclass
trait Cost[F[_]] {
  def evaluate[M[_] : Monad](pathCard : APath => M[Int]): GAlgebraM[(Int, ?), M, F, Int]
}

/**
  * This is a "generic" implementation for `Cost` that can be used by any connector.
  * Can be used for newly created connectors. More mature connectors should provide
  * their own instance that will take into account connector-specific information.
  */
object Cost {
  implicit def deadEnd: Cost[Const[DeadEnd, ?]] = new Cost[Const[DeadEnd, ?]] {
      def evaluate[M[_] : Monad](pathCard: APath => M[Int]): GAlgebraM[(Int, ?), M, Const[DeadEnd, ?], Int] =
        (qs: Const[DeadEnd, (Int, Int)]) => 1.point[M]
    }

  implicit def read[A]: Cost[Const[Read[A], ?]] =
    new Cost[Const[Read[A], ?]] {
      def evaluate[M[_] : Monad](pathCard: APath => M[Int]): GAlgebraM[(Int, ?), M, Const[Read[A], ?], Int] =
        (qs: Const[Read[A], (Int, Int)]) => 1.point[M]
    }
  implicit def shiftedRead[A]: Cost[Const[ShiftedRead[A], ?]] =
    new Cost[Const[ShiftedRead[A], ?]] {
      def evaluate[M[_] : Monad](pathCard: APath => M[Int]): GAlgebraM[(Int, ?), M, Const[ShiftedRead[A], ?], Int] =
        (qs: Const[ShiftedRead[A], (Int, Int)]) => 1.point[M]
    }

  implicit def qscriptCore[T[_[_]]: RecursiveT: ShowT]: Cost[QScriptCore[T, ?]] =
    new Cost[QScriptCore[T, ?]] {
      @SuppressWarnings(Array("org.wartremover.warts.Recursion"))
      def evaluate[M[_] : Monad](pathCard: APath => M[Int]): GAlgebraM[(Int, ?), M, QScriptCore[T, ?], Int] = {
        case Map((card, cost), f) => (card + cost).point[M]
        case Reduce((card, cost), bucket, reducers, repair) => (card + cost).point[M]
        case Sort((card, cost), bucket, orders) => (card + cost).point[M]
        case Filter((card, cost), f) => (card + cost).point[M]
        case Subset((card, cost), from, sel, count) => (card + cost).point[M]
        case LeftShift((card, cost), struct, id, stpe, repair) => (card + cost).point[M]
        case Union((card, cost), lBranch, rBranch) => {
          val compileCardinality = Cardinality[QScriptTotal[T, ?]].calculate(pathCard)
          val compileCost = Cost[QScriptTotal[T, ?]].evaluate(pathCard)
          val left = lBranch.zygoM(interpretM(κ(card.point[M]), compileCardinality), ginterpretM(κ(cost.point[M]), compileCost))
          val right = lBranch.zygoM(interpretM(κ(card.point[M]), compileCardinality), ginterpretM(κ(cost.point[M]), compileCost))
          (left |@| right)( (l, r) => (l + r) / 2)
        }
        case Unreferenced() => 0.point[M]
      }
    }

  implicit def projectBucket[T[_[_]]]: Cost[ProjectBucket[T, ?]] =
    new Cost[ProjectBucket[T, ?]] {
      def evaluate[M[_] : Monad](pathCard: APath => M[Int]): GAlgebraM[(Int, ?), M, ProjectBucket[T, ?], Int] = {
        case BucketKey((card, cost), _, _) => (card + cost).point[M]
        case BucketIndex((card, cost), _, _) => (card + cost).point[M]
      }
    }

  implicit def equiJoin[T[_[_]]: RecursiveT: ShowT]: Cost[EquiJoin[T, ?]] =
    new Cost[EquiJoin[T, ?]] {
      @SuppressWarnings(Array("org.wartremover.warts.Recursion"))
      def evaluate[M[_] : Monad](pathCard: APath => M[Int]): GAlgebraM[(Int, ?), M, EquiJoin[T, ?], Int] = {
        case EquiJoin((card, cost), lBranch, rBranch, key, jt, combine) =>
          val compileCardinality = Cardinality[QScriptTotal[T, ?]].calculate(pathCard)
          val compileCost = Cost[QScriptTotal[T, ?]].evaluate(pathCard)
          (lBranch.zygoM(interpretM(κ(card.point[M]), compileCardinality), ginterpretM(κ(cost.point[M]), compileCost)) |@|
          rBranch.zygoM(interpretM(κ(card.point[M]), compileCardinality), ginterpretM(κ(cost.point[M]), compileCost))) { _ + _ }
      }
    }
  implicit def thetaJoin[T[_[_]] : RecursiveT : ShowT]: Cost[ThetaJoin[T, ?]] =
    new Cost[ThetaJoin[T, ?]] {
      @SuppressWarnings(Array("org.wartremover.warts.Recursion"))
      def evaluate[M[_] : Monad](pathCard: APath => M[Int]): GAlgebraM[(Int, ?), M, ThetaJoin[T, ?], Int] = {
        case ThetaJoin((card, cost), lBranch, rBranch, _, _, _) => {
          val compileCardinality = Cardinality[QScriptTotal[T, ?]].calculate(pathCard)
          val compileCost = Cost[QScriptTotal[T, ?]].evaluate(pathCard)
          (lBranch.zygoM(interpretM(κ(card.point[M]), compileCardinality), ginterpretM(κ(cost.point[M]), compileCost)) |@|
          rBranch.zygoM(interpretM(κ(card.point[M]), compileCardinality), ginterpretM(κ(cost.point[M]), compileCost))) { _ + _ }
        }
      }
    }

  implicit def coproduct[F[_], G[_]](implicit F: Cost[F], G: Cost[G]):
      Cost[Coproduct[F, G, ?]] =
    new Cost[Coproduct[F, G, ?]] {
      def evaluate[M[_] : Monad](pathCard: APath => M[Int]): GAlgebraM[(Int, ?), M, Coproduct[F, G, ?], Int] =
        _.run.fold(F.evaluate(pathCard), G.evaluate(pathCard))
    }

}
