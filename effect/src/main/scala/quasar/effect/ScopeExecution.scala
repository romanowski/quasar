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

package quasar.effect

import slamdata.Predef._
import java.time.Instant
import java.time.temporal.ChronoUnit
import scala.collection.immutable.TreeMap
import quasar.RenderedTree
import quasar.fp._
import quasar.fp.numeric.Natural
import matryoshka._
import matryoshka.patterns.EnvT
import matryoshka.data.cofree._

import scalaz._, Scalaz._
import scalaz.concurrent.Task

/** Represents the ability to create an execution scope, within which timing scopes can be created.
  */
trait ScopeExecution[F[_], T] {
  def newExecution[A](index: Long, action: ScopeTiming[F, T] => F[A]): F[A]
}

object ScopeExecution {
  def ignore[F[_], T]: ScopeExecution[F, T] = new ScopeExecution[F, T] {
    def newExecution[A](index: Long, action: ScopeTiming[F, T] => F[A]): F[A] =
      action(ScopeTiming.ignore[F, T])
  }
  def forTask[T](repo: TimingRepository,
                 print: (ExecutionId, ExecutionTimings) => Task[Unit]): ScopeExecution[Task, T] =
    new ScopeExecution[Task, T] {
      def newExecution[A](index: Long, action: ScopeTiming[Task, T] => Task[A]): Task[A] = {
        for {
          newExecutionRef <- SingleExecutionRef.empty
          start <- Task.delay(Instant.now())
          result <- action(ScopeTiming.forTask(newExecutionRef))
          end <- Task.delay(Instant.now())
          executionId = ExecutionId(index, start, end)
          newScope <- newExecutionRef.under.read
          _ <- repo.addExecution(executionId, newScope)
          _ <- print(executionId, newScope)
        } yield result
      }
    }

  def forFreeTask[F[_], T](repo: TimingRepository, print: (ExecutionId, ExecutionTimings) => Free[F, Unit])
                          (implicit task: Task :<: F): ScopeExecution[Free[F, ?], T] =
    new ScopeExecution[Free[F, ?], T] {
      def newExecution[A](index: Long, action: ScopeTiming[Free[F, ?], T] => Free[F, A]): Free[F, A] = {
        for {
          newExecutionRef <- Free.liftF(task(SingleExecutionRef.empty))
          start <- Free.liftF(task(Task.delay(Instant.now())))
          result <- action(ScopeTiming.forFreeTask(newExecutionRef))
          end <- Free.liftF(task(Task.delay(Instant.now())))
          executionId = ExecutionId(index, start, end)
          newScope <- Free.liftF(task(newExecutionRef.under.read))
          _ <- Free.liftF(task(repo.addExecution(executionId, newScope)))
          _ <- print(executionId, newScope)
        } yield result
      }
    }
}

/** Represents the ability to create a timing scope.
  */
trait ScopeTiming[F[_], T] {
  def newScope[A](scopeId: String, fa: => F[A]): F[A]
}

object ScopeTiming {
  def ignore[F[_], T]: ScopeTiming[F, T] = new ScopeTiming[F, T] {
    def newScope[A](scopeId: String, fa: => F[A]): F[A] = fa
  }
  def forTask[T](ref: SingleExecutionRef): ScopeTiming[Task, T] =
    new ScopeTiming[Task, T] {
      def newScope[A](scopeId: String, f: => Task[A]): Task[A] = {
        for {
          start <- Task.delay(Instant.now())
          result <- f
          end <- Task.delay(Instant.now())
          _ <- ref.addScope(scopeId, start, end)
        } yield result
      }
    }

  def forFreeTask[F[_], T](ref: SingleExecutionRef)
                          (implicit task: Task :<: F): ScopeTiming[Free[F, ?], T] =
  new ScopeTiming[Free[F, ?], T] {
    def newScope[A](scopeId: String, f: => Free[F, A]): Free[F, A] = {
      for {
        start <- Free.liftF(task(Task.delay(Instant.now())))
        result <- f
        end <- Free.liftF(task(Task.delay(Instant.now())))
        _ <- Free.liftF(task(ref.addScope(scopeId, start, end)))
      } yield result
    }
  }
}

final case class ExecutionId(index: Long, start: Instant, end: Instant)
object ExecutionId {
  import scala.Ordering
  implicit val executionIdOrdering: Ordering[ExecutionId] = Ordering.ordered[Instant](x => x).on(_.end)
  implicit val executionIdShow: Show[ExecutionId] = Show.shows {
    case ExecutionId(index, start, end) => s"Query execution $index began at $start and ended at $end"
  }
}

final case class LabelledInterval(label: String, start: Long, size: Long) {
  def contains(other: LabelledInterval) = start < other.start && (start + size) > (other.start + size)
}

final case class ExecutionTimings(timings: Map[String, (Instant, Instant)])

object ExecutionTimings {
  // Flame graph tree
  type LabelledIntervalTree = Cofree[List, LabelledInterval]
  def LabelledIntervalTree[A](head: LabelledInterval, tail: List[LabelledIntervalTree]): LabelledIntervalTree = Cofree(head, tail)
  def toLabelledIntervalTree(executionId: ExecutionId, timings: ExecutionTimings): LabelledIntervalTree = {
    def constructIntervalTree(newLabelledInterval: LabelledInterval, tree: LabelledIntervalTree): LabelledIntervalTree = {
      if (newLabelledInterval.contains(tree.head)) {
        LabelledIntervalTree(newLabelledInterval, List(tree))
      } else if (tree.tail.isEmpty) {
        LabelledIntervalTree(tree.head, List(LabelledIntervalTree(newLabelledInterval, Nil)))
      } else {
        @SuppressWarnings(Array("org.wartremover.warts.Recursion"))
        def findInsert(list: List[Cofree[List, LabelledInterval]]): List[Cofree[List, LabelledInterval]] = list match {
          case Nil =>
            LabelledIntervalTree(newLabelledInterval, Nil) :: Nil
          case Cofree(interval@LabelledInterval(id, _, _), tail) :: xs
            if interval.contains(newLabelledInterval) =>
            LabelledIntervalTree(interval, findInsert(tail)) :: xs
          case c :: xs =>
            c :: findInsert(xs)
        }
        LabelledIntervalTree(tree.head, findInsert(tree.tail))
      }
    }
    val asIntervalsFromStart: List[LabelledInterval] = timings.timings.map {
      case (label, (start, end)) =>
        LabelledInterval(label, 
          executionId.start.until(start, ChronoUnit.MILLIS), start.until(end, ChronoUnit.MILLIS))
    }.toList
    val sortedBySize =
      asIntervalsFromStart.sortBy(-_.size)
    val totalInterval = LabelledInterval("total", 0L, executionId.start.until(executionId.end, ChronoUnit.MILLIS))
    val initTree = LabelledIntervalTree(totalInterval, Nil)
    sortedBySize.foldRight(initTree)(constructIntervalTree)
  }

  @SuppressWarnings(Array("org.wartremover.warts.Recursion"))
  def render(tree: LabelledIntervalTree): RenderedTree = {
    val LabelledInterval(label, start, size) = tree.head
    RenderedTree((label + " ") :: Nil, (size.shows + " ms").some, tree.tail.sortBy(_.head.start).map(render))
  }

  import argonaut.Json
  def asJson(executionId: ExecutionId, tree: LabelledIntervalTree): Json = {
    @SuppressWarnings(Array("org.wartremover.warts.Recursion"))
    type PF[A] = EnvT[LabelledInterval, List, A]
    def treeToJson(in: PF[(String, Json)]): Json =
      Json.jObjectFields(
        "start" -> Json.jNumber(in.ask.start),
        "size" -> Json.jNumber(in.ask.size),
        "children" -> Json.jObjectFields(in.lower: _*)
      )
    val subtrees =
      Recursive[LabelledIntervalTree, PF].zygo[Json, String](tree)(_.ask.label, treeToJson)
    Json.jObjectFields(
      "id" -> Json.jObjectFields(
        "index" -> Json.jNumber(executionId.index),
        "start" -> Json.jString(executionId.start.toString)),
      "timings" -> subtrees
    )
  }
}

final case class SingleExecutionRef(under: TaskRef[ExecutionTimings]) {
  def addScope(scopeId: String, start: Instant, end: Instant): Task[Unit] = {
    under.modify {
      case ExecutionTimings(scopes) =>
        ExecutionTimings(scopes + ((scopeId, (start, end))))
    }.void
  }
}

object SingleExecutionRef {
  def empty: Task[SingleExecutionRef] =
   TaskRef(ExecutionTimings(Map.empty)).map(SingleExecutionRef(_))
}

final case class TimingRepository(recordedExecutions: Natural, under: TaskRef[TreeMap[ExecutionId, ExecutionTimings]]) {
  def addExecution(executionId: ExecutionId, timings: ExecutionTimings): Task[Unit] = {
    under.modify { executions =>
      val newExecutions = executions + ((executionId, timings))
      val excessExecutions = java.lang.Math.max(newExecutions.size - recordedExecutions.value.toInt, 0)
      newExecutions.drop(excessExecutions)
    }.void
  }
}

object TimingRepository {
  def empty(recordedExecutions: Natural): Task[TimingRepository] = {
    TaskRef(TreeMap.empty[ExecutionId, ExecutionTimings])
      .map(TimingRepository(recordedExecutions, _))
  }
}
