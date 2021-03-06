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

import slamdata.Predef._
import quasar.{NameGenerator, RenderTreeT}
import quasar.Planner.PlannerErrorME
import quasar.frontend.logicalplan.LogicalPlan

import matryoshka.{delayShow, showTShow, BirecursiveT, EqualT, ShowT}
import scalaz.{Applicative, Cord, Functor, Kleisli => K, Monad, Show}
import scalaz.syntax.applicative._
import scalaz.syntax.show._

final class LPtoQS[T[_[_]]: BirecursiveT: EqualT: ShowT: RenderTreeT] extends QSUTTypes[T] {
  import LPtoQS.MapSyntax
  import ApplyProvenance.AuthenticatedQSU
  import ReifyIdentities.ResearchedQSU

  def apply[F[_]: Monad: PlannerErrorME: NameGenerator](lp: T[LogicalPlan])
      : F[T[QScriptEducated]] = {

    val lpToQs =
      K(ReadLP[T, F])                  >==>
      debugG("ReadLP: ")               >==>
      RewriteGroupByArrays[T, F]       >==>
      debugG("RewriteGBArrays: ")      >-
      EliminateUnary[T]                >==>
      debugG("EliminateUnary: ")       >-
      RecognizeDistinct[T]             >==>
      debugG("RecognizeDistinct: ")    >==>
      ExtractFreeMap[T, F]             >==>
      debugG("ExtractFreeMap: ")       >==>
      ApplyProvenance[T, F]            >==>
      debugAG("ApplyProv: ")           >==>
      ReifyBuckets[T, F]               >==>
      debugAG("ReifyBuckets: ")        >==>
      MinimizeAutoJoins[T, F]          >==>
      debugAG("MinimizeAJ: ")          >==>
      ReifyAutoJoins[T, F]             >==>
      debugAG("ReifyAutoJoins: ")      >==>
      ExpandShifts[T, F]               >==>
      debugAG("ExpandShifts: ")        >-
      ResolveOwnIdentities[T]          >==>
      debugAG("ResolveOwnIdentities: ") >==>
      ReifyIdentities[T, F]            >==>
      debugRG("ReifyIdentities: ")     >==>
      Graduate[T, F]

    lpToQs(lp)
  }

  def debugG[F[_]: Applicative](prefix: String): QSUGraph => F[QSUGraph] =
    debug[F, QSUGraph](prefix)
  def debugAG[F[_]: Applicative](prefix: String): AuthenticatedQSU[T] => F[AuthenticatedQSU[T]] =
    debug[F, AuthenticatedQSU[T]](prefix)
  def debugRG[F[_]: Applicative](prefix: String): ResearchedQSU[T] => F[ResearchedQSU[T]] =
    debug[F, ResearchedQSU[T]](prefix)

  @SuppressWarnings(Array("org.wartremover.warts.ToString"))
  private def debug[F[_]: Applicative, A: Show](prefix: String)(in: A): F[A] = {
    // uh... yeah do better
    in.point[F].map { i =>
      maybePrint((Cord("\n\n") ++ Cord(prefix) ++ in.show).toString)
      i
    }
  }

  private def maybePrint(str: => String): Unit = {
    // println(str)

    ()
  }
}

object LPtoQS {
  def apply[T[_[_]]: BirecursiveT: EqualT: ShowT: RenderTreeT]: LPtoQS[T] = new LPtoQS[T]

  final implicit class MapSyntax[F[_], A](val self: F[A]) extends AnyVal {
    def >-[B](f: A => B)(implicit F: Functor[F]): F[B] =
      F.map(self)(f)
  }
}
