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

package quasar.physical.mongodb

import quasar._
import quasar.common.{Map => _, _}
import quasar.contrib.pathy._
import quasar.contrib.specs2.PendingWithActualTracking
import quasar.ejson.{EJson, Fixed}
import quasar.javascript._
import quasar.physical.mongodb.expression._
import quasar.physical.mongodb.planner._
import quasar.physical.mongodb.workflow._
import quasar.qscript.ShiftType
import quasar.sql.JoinDir
import slamdata.Predef._

import eu.timepit.refined.auto._
import matryoshka.data.Fix
import pathy.Path._
import scalaz._

class PlannerQScriptSpec extends
    PlannerHelpers with
    PendingWithActualTracking {

  import fixExprOp._
  import PlannerHelpers._
  import jscore._
  import CollectionUtil._
  import Reshape.reshape

  val dsl =
    quasar.qscript.construction.mkDefaults[Fix, fs.MongoQScript[Fix, ?]]

  import dsl._

  val json = Fixed[Fix[EJson]]

  "plan from qscript" should {
    "plan simple inner equi-join with expression ($lookup)" in {
      qplan(
        fix.EquiJoin(
          fix.Unreferenced,
          free.ShiftedRead[AFile](rootDir </> dir("db") </> file("smallZips"), qscript.ExcludeId),
          free.Filter(
            free.ShiftedRead[AFile](rootDir </> dir("db") </> file("zips"), qscript.ExcludeId),
            func.Guard(
              func.ProjectKey(func.Hole, func.Constant(json.str("_id"))),
              Type.Str,
              func.Constant(json.bool(true)),
              func.Constant(json.bool(false)))),
          List(
            (func.ProjectKey(func.Hole, func.Constant(json.str("_id"))),
              func.Lower(func.ProjectKey(func.Hole, func.Constant(json.str("_id")))))),
          JoinType.Inner,
          func.ConcatMaps(
            func.MakeMap(
              func.Constant(json.str("c1")),
              func.ProjectKey(
                func.LeftSide,
                func.Constant(json.str("name")))),
            func.MakeMap(
              func.Constant(json.str("c2")),
              func.ProjectKey(
                func.RightSide,
                func.Constant(json.str("name"))))))) must beWorkflow0(
        chain[Workflow](
          $read(collection("db", "zips")),
          $match(Selector.Doc(BsonField.Name("_id") -> Selector.Type(BsonType.Text))),
          $project(reshape(
            JoinDir.Left.name -> $$ROOT,
            "0" -> $toLower($field("_id"))),
            ExcludeId),
          $lookup(
            CollectionName("smallZips"),
            BsonField.Name("0"),
            BsonField.Name("_id"),
            JoinHandler.RightName),
          $project(reshape(
            JoinDir.Left.name -> $include(),
            JoinDir.Right.name -> $include()),
            ExcludeId),
          $unwind(DocField(JoinHandler.RightName)),
          $project(reshape(
            "city" -> $field("left", "city"),
            "state" -> $field("right", "state")
          ), IgnoreId)))
    }.pendingWithActual("qz-3571", qtestFile("plan simple inner equi-join with expression ($lookup)"))

    "plan simple inner equi-join with pre-filtering ($lookup)" in {
      qplan0(
        fix.EquiJoin(
          fix.Unreferenced,
          free.ShiftedRead[AFile](rootDir </> dir("db") </> file("foo"), qscript.ExcludeId),
          free.Filter(
            free.ShiftedRead[AFile](rootDir </> dir("db") </> file("bar"), qscript.ExcludeId),
            func.Guard(
              func.ProjectKey(func.Hole, func.Constant(json.str("rating"))),
              Type.Comparable,
              func.Gte(func.ProjectKey(func.Hole, func.Constant(json.str("rating"))),
                func.Constant(json.int(4))),
              func.Undefined)),
          List(
            (func.ProjectKey(func.Hole, func.Constant(json.str("id"))),
              func.ProjectKey(func.Hole, func.Constant(json.str("foo_id"))))),
          JoinType.Inner,
          func.ConcatMaps(
            func.MakeMap(func.Constant(json.str("name")),
              func.ProjectKey(
                func.LeftSide,
                func.Constant(json.str("name")))),
            func.MakeMap(
              func.Constant(json.str("address")),
              func.ProjectKey(
                func.RightSide,
                func.Constant(json.str("address")))))),
        defaultStats, indexes(collection("db", "foo") -> BsonField.Name("id"))) must beWorkflow0(
        chain[Workflow](
          $read(collection("db", "bar")),
          $match(
            Selector.And(
              isNumeric(BsonField.Name("rating")),
              Selector.Doc(
                BsonField.Name("rating") -> Selector.Gte(Bson.Int32(4))),
              Selector.Doc(
                BsonField.Name("foo_id") -> Selector.Exists(true)))),
          $project(reshape(
            JoinDir.Right.name -> $$ROOT),
            ExcludeId),
          $lookup(
            CollectionName("foo"),
            BsonField.Name("right") \ BsonField.Name("foo_id"),
            BsonField.Name("id"),
            JoinHandler.LeftName),
          $unwind(DocField(JoinHandler.LeftName)),
          $project(reshape(
            "name" -> $field("left", "name"),
            "address" -> $field("right", "address")),
            ExcludeId)))
    }

    "plan 3-way equi-join ($lookup)" in {
      qplan0(
        fix.EquiJoin(
          fix.Unreferenced,
          free.Filter(
            free.EquiJoin(
              free.Unreferenced,
              free.ShiftedRead[AFile](rootDir </> dir("db") </> file("foo"), qscript.ExcludeId),
              free.ShiftedRead[AFile](rootDir </> dir("db") </> file("bar"), qscript.ExcludeId),
              List(
                (func.ProjectKey(func.Hole, func.Constant(json.str("id"))),
                  func.ProjectKey(func.Hole, func.Constant(json.str("foo_id"))))),
              JoinType.Inner,
              func.ConcatMaps(
                func.MakeMap(
                  func.Constant(json.str("left")),
                  func.LeftSide),
                func.MakeMap(
                  func.Constant(json.str("right")),
                  func.RightSide))),
            func.Guard(
              func.ProjectKey(func.Hole, func.Constant(json.str("right"))),
              Type.Obj(Map(), Some(Type.Top)),
              func.Constant(json.bool(true)),
              func.Constant(json.bool(false)))),
          free.ShiftedRead[AFile](rootDir </> dir("db") </> file("baz"), qscript.ExcludeId),
          List(
            (func.ProjectKey(
              func.ProjectKey(func.Hole, func.Constant(json.str("right"))),
              func.Constant(json.str("id"))),
              func.ProjectKey(func.Hole, func.Constant(json.str("bar_id"))))),
          JoinType.Inner,
          func.ConcatMaps(
            func.ConcatMaps(
              func.MakeMap(
                func.Constant(json.str("name")),
                func.Guard(
                  func.ProjectKey(func.LeftSide, func.Constant(json.str("left"))),
                  Type.Obj(Map(), Some(Type.Top)),
                  func.ProjectKey(
                    func.ProjectKey(func.LeftSide, func.Constant(json.str("left"))),
                    func.Constant(json.str("name"))),
                  func.Undefined)),
              func.MakeMap(
                func.Constant(json.str("address")),
                func.Guard(
                  func.ProjectKey(func.LeftSide, func.Constant(json.str("right"))),
                  Type.Obj(Map(), Some(Type.Top)),
                  func.ProjectKey(
                    func.ProjectKey(func.LeftSide, func.Constant(json.str("right"))),
                    func.Constant(json.str("address"))),
                  func.Undefined))),
            func.MakeMap(
              func.Constant(json.str("zip")),
              func.ProjectKey(func.RightSide, func.Constant(json.str("zip")))))) , defaultStats,
        indexes(
          collection("db", "bar") -> BsonField.Name("foo_id"),
          collection("db", "baz") -> BsonField.Name("bar_id"))) must beWorkflow0(
        chain[Workflow](
          $read(collection("db", "foo")),
          $match(Selector.Doc(
            BsonField.Name("id") -> Selector.Exists(true))),
          $project(reshape(JoinDir.Left.name -> $$ROOT), ExcludeId),
          $lookup(
            CollectionName("bar"),
            JoinHandler.LeftName \ BsonField.Name("id"),
            BsonField.Name("foo_id"),
            JoinHandler.RightName),
          $unwind(DocField(JoinHandler.RightName)),
          $match(Selector.Doc(
            JoinHandler.RightName \ BsonField.Name("id") -> Selector.Exists(true))),
          $project(reshape(JoinDir.Left.name -> $$ROOT)),
          $lookup(
            CollectionName("baz"),
            JoinHandler.LeftName \ JoinHandler.RightName \ BsonField.Name("id"),
            BsonField.Name("bar_id"),
            JoinHandler.RightName),
          $unwind(DocField(JoinHandler.RightName)),
          $project(reshape(
            "name" ->
              $cond(
                $and(
                  $lte($literal(Bson.Doc()), $field(JoinDir.Left.name)),
                  $lt($field(JoinDir.Left.name), $literal(Bson.Arr()))),
                $cond(
                  $and(
                    $lte($literal(Bson.Doc()), $field(JoinDir.Left.name, JoinDir.Left.name)),
                    $lt($field(JoinDir.Left.name, JoinDir.Left.name), $literal(Bson.Arr()))),
                  $field(JoinDir.Left.name, JoinDir.Left.name, "city"),
                  $literal(Bson.Undefined)),
                $literal(Bson.Undefined)),
            "address" ->
              $cond(
                $and(
                  $lte($literal(Bson.Doc()), $field(JoinDir.Left.name)),
                  $lt($field(JoinDir.Left.name), $literal(Bson.Arr()))),
                $cond(
                  $and(
                    $lte($literal(Bson.Doc()), $field(JoinDir.Left.name, JoinDir.Right.name)),
                    $lt($field(JoinDir.Left.name, JoinDir.Right.name), $literal(Bson.Arr()))),
                  $field(JoinDir.Left.name, JoinDir.Right.name, "state"),
                  $literal(Bson.Undefined)),
                $literal(Bson.Undefined)),
            "zip" ->
              $cond(
                $and(
                  $lte($literal(Bson.Doc()), $field(JoinDir.Right.name)),
                  $lt($field(JoinDir.Right.name), $literal(Bson.Arr()))),
                $field(JoinDir.Right.name, "pop"),
                $literal(Bson.Undefined))),
            IgnoreId)))
    }.pendingWithActual("qz-3571", qtestFile("plan 3-way equi-join ($lookup)"))

    "plan filtered flatten" in {
      qplan(
        fix.LeftShift(
          fix.Filter(
            fix.ShiftedRead[AFile](rootDir </> dir("db") </> file("patients"), qscript.ExcludeId),
            func.Eq(func.ProjectKeyS(func.Hole, "state"), func.Constant(json.str("CO")))),
          func.Guard(
            func.ProjectKey(func.Hole, func.Constant(json.str("codes"))),
            Type.FlexArr(0, None, Type.Top),
            func.ProjectKey(func.Hole, func.Constant(json.str("codes"))),
            func.Undefined),
          qscript.ExcludeId,
          ShiftType.Array,
          func.ConcatMaps(
            func.MakeMap(
              func.Constant(json.str("codes")),
              func.RightSide),
            func.MakeMap(
              func.Constant(json.str("first_name")),
              func.ProjectKey(
                func.LeftSide,
                func.Constant(json.str("first_name"))))))) must beWorkflow0(
        chain[Workflow](
          $read(collection("db", "patients")),
          $match(Selector.Doc(
            BsonField.Name("state") -> Selector.Eq(Bson.Text("CO")))),
          $project(reshape(
            "s" -> $$ROOT,
            "f" ->
              $cond(
                $and(
                  $lte($literal(Bson.Arr()), $field("codes")),
                  $lt($field("codes"), $literal(Bson.Binary.fromArray(scala.Array[Byte]())))),
                $field("codes"),
                $arrayLit(List($literal(Bson.Undefined)))))),
          $unwind(DocField("f")),
          $project(reshape(
            "codes"      -> $field("f"),
            "first_name" -> $field("s", "first_name")))))

    }

    "plan with flatenning in filter predicate with reference to LeftSide" in {
      qplan(
        fix.Filter(
          fix.LeftShift(
            fix.ShiftedRead[AFile](rootDir </> dir("db") </> file("zips"), qscript.ExcludeId),
            func.Guard(
              func.ProjectKey(func.Hole, func.Constant(json.str("loc"))),
              Type.FlexArr(0, None, Type.Top),
              func.ProjectKey(func.Hole, func.Constant(json.str("loc"))),
              func.Undefined),
            qscript.ExcludeId,
            qscript.ShiftType.Array,
            func.ConcatMaps(
              func.MakeMap(func.Constant(json.str("city")),
                func.ProjectKey(func.LeftSide, func.Constant(json.str("city")))),
              func.MakeMap(
                func.Constant(json.str("loc")), func.RightSide))),
          func.Lt(func.ProjectKeyS(func.Hole, "loc"), func.Constant(json.int(-165))))) must beWorkflow0(
        chain[Workflow](
          $read(collection("db", "zips")),
          $project(reshape(
            "s" -> $$ROOT,
            "f" ->
              $cond(
                $and(
                  $lte($literal(Bson.Arr()), $field("loc")),
                  $lt($field("loc"), $literal(Bson.Binary.fromArray(scala.Array[Byte]())))),
                $field("loc"),
                $arrayLit(List($literal(Bson.Undefined)))))),
          $unwind(DocField("f")),
          $match(Selector.Doc((BsonField.Name("f")) -> Selector.Lt(Bson.Int32(-165)))),
          $project(reshape(
            "city" -> $field("s", "city"),
            "loc" -> $field("f")))))
    }

    "plan with flatenning in filter predicate without reference to LeftSide" in {
      qplan(
        fix.Filter(
          fix.LeftShift(
            fix.ShiftedRead[AFile](rootDir </> dir("db") </> file("zips"), qscript.ExcludeId),
            func.Guard(
              func.ProjectKey(func.Hole, func.Constant(json.str("loc"))),
              Type.FlexArr(0, None, Type.Top),
              func.ProjectKey(func.Hole, func.Constant(json.str("loc"))),
              func.Undefined),
            qscript.ExcludeId,
            qscript.ShiftType.Array,
            func.RightSide),
          func.Lt(func.Hole, func.Constant(json.int(-165))))) must beWorkflow0(
        chain[Workflow](
          $read(collection("db", "zips")),
          $project(reshape(
            "0" ->
              $cond(
                $and(
                  $lte($literal(Bson.Arr()), $field("loc")),
                  $lt($field("loc"), $literal(Bson.Binary.fromArray(scala.Array[Byte]())))),
                $field("loc"),
                $arrayLit(List($literal(Bson.Undefined)))))),
          $unwind(DocField("0")),
          $match(Selector.Doc(
            BsonField.Name("0") -> Selector.Lt(Bson.Int32(-165)))),
          $project(reshape(sigil.Quasar -> $field("0")))))
    }

    "plan double flatten with reference to LeftSide" in {
      qplan(
        fix.LeftShift(
          fix.LeftShift(
            fix.ShiftedRead[AFile](rootDir </> dir("db") </> file("zips"), qscript.ExcludeId),
            func.Guard(
              func.ProjectKey(func.Hole, func.Constant(json.str("loc"))),
              Type.FlexArr(0, None, Type.FlexArr(0, None, Type.Top)),
              func.ProjectKey(func.Hole, func.Constant(json.str("loc"))),
              func.Undefined),
            qscript.ExcludeId,
            qscript.ShiftType.Array,
            func.ConcatMaps(
              func.MakeMap(
                func.Constant(json.str("results")),
                func.Guard(
                  func.RightSide,
                  Type.FlexArr(0, None, Type.Top),
                  func.RightSide,
                  func.Undefined)),
              func.MakeMap(
                func.Constant(json.str("original")),
                func.LeftSide))),
          func.ProjectKey(func.Hole, func.Constant(json.str("results"))),
          qscript.ExcludeId,
          qscript.ShiftType.Array,
          func.ConcatMaps(
            func.MakeMap(
              func.Constant(json.str("0")),
              func.ProjectKey(
                func.ProjectKey(
                  func.LeftSide,
                  func.Constant(json.str("original"))),
                func.Constant(json.str("city")))),
            func.MakeMap(
              func.Constant(json.str("1")),
              func.RightSide)))) must beWorkflow0(
        chain[Workflow](
          $read(collection("db", "zips")),
          $project(reshape(
            "s" -> $$ROOT,
            "f" ->
              $cond(
                $and(
                  $lte($literal(Bson.Arr()), $field("loc")),
                  $lt($field("loc"), $literal(Bson.Binary.fromArray(scala.Array[Byte]())))),
                $field("loc"),
                $arrayLit(List($literal(Bson.Undefined)))))),
          $unwind(DocField("f")),
          $project(reshape(
            "s" -> reshape("original" -> $field("s")),
            "f" ->
              $cond(
                $and(
                  $lte($literal(Bson.Arr()), $field("f")),
                  $lt($field("f"), $literal(Bson.Binary.fromArray(scala.Array[Byte]())))),
                $field("f"),
                $arrayLit(List($literal(Bson.Undefined)))))),
          $unwind(DocField("f")),
          $project(reshape(
            "0" -> $field("s", "original", "city"),
            "1" -> $field("f")))))
    }

    "plan double flatten without reference to LeftSide" in {
      qplan(
        fix.LeftShift(
          fix.LeftShift(
            fix.ShiftedRead[AFile](rootDir </> dir("db") </> file("zips"), qscript.ExcludeId),
            func.Guard(
              func.ProjectKey(func.Hole, func.Constant(json.str("loc"))),
              Type.FlexArr(0, None, Type.FlexArr(0, None, Type.Top)),
              func.ProjectKey(func.Hole, func.Constant(json.str("loc"))),
              func.Undefined),
            qscript.ExcludeId,
            qscript.ShiftType.Array,
            func.Guard(func.RightSide,
              Type.FlexArr(0, None, Type.Top),
              func.RightSide,
              func.Undefined)),
          func.Hole,
          qscript.ExcludeId,
          qscript.ShiftType.Array,
          func.RightSide)) must beWorkflow0(
        chain[Workflow](
          $read(collection("db", "zips")),
          $project(reshape(
            "0" ->
              $cond(
                $and(
                  $lte($literal(Bson.Arr()), $field("loc")),
                  $lt($field("loc"), $literal(Bson.Binary.fromArray(scala.Array[Byte]())))),
                $field("loc"),
                $arrayLit(List($literal(Bson.Undefined)))))),
          $unwind(DocField("0")),
          $project(reshape(
            "0" ->
              $cond(
                $and(
                  $lte($literal(Bson.Arr()), $field("0")),
                  $lt($field("0"), $literal(Bson.Binary.fromArray(scala.Array[Byte]())))),
                $field("0"),
                $arrayLit(List($literal(Bson.Undefined)))))),
          $unwind(DocField("0")),
          $project(reshape(
            sigil.Quasar -> $field("0")))))
    }

    "plan flatten with reference to LeftSide" in {
      qplan(
        fix.LeftShift(
          fix.ShiftedRead[AFile](rootDir </> dir("db") </> file("zips"), qscript.ExcludeId),
          func.Guard(
            func.ProjectKey(func.Hole, func.Constant(json.str("loc"))),
            Type.FlexArr(0, None, Type.Top),
            func.ProjectKey(func.Hole, func.Constant(json.str("loc"))),
            func.Undefined),
          qscript.ExcludeId,
          qscript.ShiftType.Array,
          func.ConcatMaps(
            func.MakeMap(func.Constant(json.str("city")),
              func.ProjectKey(func.LeftSide, func.Constant(json.str("city")))),
            func.MakeMap(
              func.Constant(json.str("loc")), func.RightSide)))) must beWorkflow0(
        chain[Workflow](
          $read(collection("db", "zips")),
          $project(reshape(
            "s" -> $$ROOT,
            "f" ->
              $cond(
                $and(
                  $lte($literal(Bson.Arr()), $field("loc")),
                  $lt($field("loc"), $literal(Bson.Binary.fromArray(scala.Array[Byte]())))),
                $field("loc"),
                $arrayLit(List($literal(Bson.Undefined)))))),
          $unwind(DocField("f")),
          $project(reshape(
            "city" -> $field("s", "city"),
            "loc" -> $field("f")))))
    }

    "plan flatten with Cond in struct and repair" in {
      qplan(
        fix.LeftShift(fix.ShiftedRead[AFile](rootDir </> dir("db") </> file("patients"), qscript.ExcludeId),
          func.Guard(
            func.ProjectKey(
              func.Cond(
                func.And(
                  func.Eq(
                    func.ProjectKey(func.Hole, func.Constant(json.str("state"))),
                    func.Constant(json.str("CO"))),
                  func.Within(
                    func.ProjectKey(func.Hole, func.Constant(json.str("city"))),
                    func.Constant(json.arr(List(json.str("BOULDER"), json.str("AURORA")))))),
                func.Hole,
                func.Undefined),
              func.Constant(json.str("codes"))),
            Type.FlexArr(0, None, Type.Top),
            func.ProjectKey(
              func.Cond(
                func.And(
                  func.Eq(
                    func.ProjectKey(func.Hole, func.Constant(json.str("state"))),
                    func.Constant(json.str("CO"))),
                  func.Within(
                    func.ProjectKey(func.Hole, func.Constant(json.str("city"))),
                    func.Constant(json.arr(List(json.str("BOULDER"), json.str("AURORA")))))),
                func.Hole, func.Undefined), func.Constant(json.str("codes"))),
            func.Undefined),
          qscript.ExcludeId,
          ShiftType.Array,
          func.ConcatMaps(
            func.ConcatMaps(
              func.MakeMap(
                func.Constant(json.str("codes")),
                func.RightSide),
              func.MakeMap(
                func.Constant(json.str("first_name")),
                func.ProjectKey(
                  func.Cond(
                    func.And(
                      func.Eq(
                        func.ProjectKey(func.LeftSide, func.Constant(json.str("state"))),
                        func.Constant(json.str("CO"))),
                      func.Within(
                        func.ProjectKey(func.LeftSide, func.Constant(json.str("city"))),
                        func.Constant(json.arr(List(json.str("BOULDER"), json.str("AURORA")))))),
                    func.LeftSide,
                    func.Undefined),
                  func.Constant(json.str("first_name"))))),
            func.MakeMap(
              func.Constant(json.str("city")),
              func.ProjectKey(
                func.Cond(
                  func.And(
                    func.Eq(
                      func.ProjectKey(func.LeftSide, func.Constant(json.str("state"))),
                      func.Constant(json.str("CO"))),
                    func.Within(
                      func.ProjectKey(func.LeftSide, func.Constant(json.str("city"))),
                      func.Constant(json.arr(List(json.str("BOULDER"), json.str("AURORA")))))),
                  func.LeftSide,
                  func.Undefined),
                func.Constant(json.str("city"))))))) must beWorkflow0(
        chain[Workflow](
          $read(collection("db", "patients")),
          $match(
            Selector.And(
              Selector.Doc(
                BsonField.Name("state") ->
                  Selector.Eq(Bson.Text("CO"))),
              Selector.Doc(
                BsonField.Name("city") ->
                  Selector.In(Bson.Arr(List(Bson.Text("BOULDER"), Bson.Text("AURORA"))))))),
          $project(reshape(
            "s" -> $$ROOT,
            "f" ->
              $cond(
                $and(
                  $lte($literal(Bson.Arr()), $field("codes")),
                  $lt($field("codes"), $literal(Bson.Binary.fromArray(scala.Array[Byte]())))),
                $field("codes"),
                $arrayLit(List($literal(Bson.Undefined)))))),
          $unwind(DocField("f")),
          $project(reshape(
            "codes" -> $field("f"),
            "first_name" -> $field("s", "first_name"),
            "city" -> $field("s", "city")))))
    }

    "plan typechecks with JS when unable to extract ExprOp" in {
      qplan(
        fix.Filter(
          fix.ShiftedRead[AFile](rootDir </> dir("db") </> file("zips"), qscript.IncludeId),
          func.Guard(
            func.DeleteKey(func.Constant(json.str("a")), func.Constant(json.str("b"))),
            Type.Str,
            func.Constant(json.bool(false)),
            func.Constant(json.bool(true))))) must beWorkflow(
        chain[Workflow](
          $read(collection("db", "zips")),
          $project(reshape("0" -> $arrayLit(List($field("_id"), $$ROOT)))),
          $simpleMap(
            NonEmptyList(MapExpr(JsFn(Name("x"), obj(
              "0" ->
                If(Call(ident("isString"),
                    List(Call(ident("remove"), List(Literal(Js.Str("a")), Literal(Js.Str("b")))))),
                  jscore.Literal(Js.Bool(false)),
                  jscore.Literal(Js.Bool(true))),
              "src" -> Access(ident("x"), jscore.Literal(Js.Str("0")))
            )))),
            ListMap()),
          $match(Selector.Doc(
            BsonField.Name("0") -> Selector.Eq(Bson.Bool(true)))),
          $project(reshape(sigil.Quasar -> $field("src")))))
    }
  }
}
