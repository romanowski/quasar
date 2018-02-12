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

package quasar.physical.mongodb.expression

import slamdata.Predef._
import quasar.fp._
import quasar.fp.ski._
import quasar.physical.mongodb.{Bson}

import matryoshka._
import matryoshka.data.Fix
import scalaz._, Scalaz._

/** "Pipeline" operators added in MongoDB version 3.4.4 (backported from 3.6) */
trait ExprOp3_4_4F[A]
object ExprOp3_4_4F {

  final case class $arrayToObjectF[A](expr: A) extends ExprOp3_4_4F[A]
  final case class $objectToArrayF[A](obj: A) extends ExprOp3_4_4F[A]

  implicit val equal: Delay[Equal, ExprOp3_4_4F] =
    new Delay[Equal, ExprOp3_4_4F] {
      def apply[A](eq: Equal[A]) = {
        implicit val EQ: Equal[A] = eq
        Equal.equal {
          case ($arrayToObjectF(e1), $arrayToObjectF(e2)) => e1 ≟ e2
          case ($objectToArrayF(o1), $objectToArrayF(o2)) => o1 ≟ o2
          case _ => false
        }
      }
    }

  implicit val traverse: Traverse[ExprOp3_4_4F] = new Traverse[ExprOp3_4_4F] {
    def traverseImpl[G[_], A, B](fa: ExprOp3_4_4F[A])(f: A => G[B])(implicit G: Applicative[G]):
        G[ExprOp3_4_4F[B]] =
      fa match {
        case $arrayToObjectF(e) => G.map(f(e))($arrayToObjectF(_))
        case $objectToArrayF(o) => G.map(f(o))($objectToArrayF(_))
      }
  }

  implicit def ops[F[_]: Functor](implicit I: ExprOp3_4_4F :<: F): ExprOpOps.Aux[ExprOp3_4_4F, F] = new ExprOpOps[ExprOp3_4_4F] {
    type OUT[A] = F[A]

    val simplify: AlgebraM[Option, ExprOp3_4_4F, Fix[F]] = κ(None)

    def bson: Algebra[ExprOp3_4_4F, Bson] = {
      case $arrayToObjectF(e) => Bson.Doc("$arrayToObject" -> e)
      case $objectToArrayF(o) => Bson.Doc("$objectToArray" -> o)
    }

    def rebase[T](base: T)(implicit T: Recursive.Aux[T, OUT]) = I(_).some

    def rewriteRefs0(applyVar: PartialFunction[DocVar, DocVar]) = κ(None)
  }

  final class fixpoint[T, EX[_]: Functor]
    (embed: EX[T] => T)
    (implicit I: ExprOp3_4_4F :<: EX) {
    @inline private def convert(expr: ExprOp3_4_4F[T]): T = embed(I.inj(expr))

    def $arrayToObject(expr: T): T = convert($arrayToObjectF(expr))
    def $objectToArray(obj: T): T = convert($objectToArrayF(obj))
  }
}

object $arrayToObject {
  def apply[EX[_], A](expr: A)(implicit I: ExprOp3_4_4F :<: EX): EX[A] =
    I.inj(ExprOp3_4_4F.$arrayToObjectF(expr))
}

object $objectToArray {
  def apply[EX[_], A](obj: A)(implicit I: ExprOp3_4_4F :<: EX): EX[A] =
    I.inj(ExprOp3_4_4F.$objectToArrayF(obj))
}
