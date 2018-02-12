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

import slamdata.Predef._
import quasar.common.SortDir
import quasar.javascript._
import quasar.physical.mongodb.accumulator._
import quasar.physical.mongodb.expression._
import quasar.physical.mongodb.workflow._

import scala.collection.immutable.ListMap

import scalaz._
import scalaz.syntax.either._

class JavaScriptWorkflowExecutionSpec extends quasar.Qspec {
  import CollectionUtil._
  import fixExprOp._

  def toJS(wf: Workflow): WorkflowExecutionError \/ String =
    WorkflowExecutor.toJS(Crystallize[WorkflowF].crystallize(wf))

  "Executing 'Workflow' as JavaScript" should {

    "write trivial workflow to JS" in {
      val wf = $read[WorkflowF](collection("db", "zips"))

      toJS(wf) must beRightDisjunction("db.zips.find();\n")
    }

    "write trivial workflow to JS with fancy collection name" in {
      val wf = $read[WorkflowF](collection("db", "tmp.123"))

      toJS(wf) must beRightDisjunction("db.getCollection(\"tmp.123\").find();\n")
    }

    "be empty for pure values" in {
      val wf = $pure[WorkflowF](Bson.Arr(List(
        Bson.Doc(ListMap("foo" -> Bson.Int64(1))),
        Bson.Doc(ListMap("bar" -> Bson.Int64(2))))))

        toJS(wf) must beRightDisjunction("")
    }

    "write simple query to JS" in {
      val wf = chain(
        $read[WorkflowF](collection("db", "zips")),
        $match[WorkflowF](Selector.Doc(
          BsonField.Name("pop") -> Selector.Gte(Bson.Int64(1000)))))

      toJS(wf) must beRightDisjunction(
        """db.zips.find({ "pop": { "$gte": NumberLong("1000") } });
          |""".stripMargin)
    }

    "write limit to JS" in {
      val wf = chain(
        $read[WorkflowF](collection("db", "zips")),
        $limit[WorkflowF](10))

      toJS(wf) must beRightDisjunction(
        """db.zips.find().limit(10);
          |""".stripMargin)
    }

    "write project and limit to JS" in {
      val wf = chain(
        $read[WorkflowF](collection("db", "zips")),
        $limit[WorkflowF](10),
        $project[WorkflowF](
          Reshape(ListMap(
            BsonField.Name("city") -> $include().right)),
          ExcludeId))

      toJS(wf) must beRightDisjunction(
        """db.zips.find({ "city": true, "_id": false }).limit(10);
          |""".stripMargin)
    }

    "write filter, project, and limit to JS" in {
      val wf = chain(
        $read[WorkflowF](collection("db", "zips")),
        $match[WorkflowF](Selector.Doc(
          BsonField.Name("pop") -> Selector.Lt(Bson.Int64(1000)))),
        $limit[WorkflowF](10),
        $project[WorkflowF](
          Reshape(ListMap(
            BsonField.Name("city") -> $include().right)),
          ExcludeId))

      toJS(wf) must beRightDisjunction(
        """db.zips.find(
          |  { "pop": { "$lt": NumberLong("1000") } },
          |  { "city": true, "_id": false }).limit(
          |  10);
          |""".stripMargin)
    }

    "write simple count to JS" in {
      val wf = chain(
        $read[WorkflowF](collection("db", "zips")),
        $match[WorkflowF](Selector.Doc(
          BsonField.Name("pop") -> Selector.Gte(Bson.Int64(1000)))),
        $group[WorkflowF](
          Grouped(ListMap(
            BsonField.Name("num") -> $sum($literal(Bson.Int32(1))))),
          $literal(Bson.Null).right))

      toJS(wf) must beRightDisjunction(
        """db.zips.count({ "pop": { "$gte": NumberLong("1000") } });
          |""".stripMargin)
    }

    "write count followed by limit to JS" in {
      val wf = chain(
        $read[WorkflowF](collection("db", "zips")),
        $group[WorkflowF](
          Grouped(ListMap(
            BsonField.Name("num") -> $sum($literal(Bson.Int32(1))))),
          $literal(Bson.Null).right),
        $limit[WorkflowF](11))

      toJS(wf) must beRightDisjunction(
        """db.zips.count();
          |""".stripMargin)
    }

    "write simple distinct to JS" in {
      val wf = chain(
        $read[WorkflowF](collection("db", "zips")),
        $group[WorkflowF](
          Grouped(ListMap()),
          Reshape(ListMap(
            BsonField.Name("0") -> $field("city").right)).left),
        $project[WorkflowF](
          Reshape(ListMap(
            BsonField.Name("c") -> $field("_id", "0").right)),
          ExcludeId))

      toJS(wf) must beRightDisjunction(
        """db.zips.distinct("city").map(function (elem) { return { "c": elem } });
          |""".stripMargin)
    }

    "write filtered distinct to JS" in {
      val wf = chain(
        $read[WorkflowF](collection("db", "zips")),
        $match[WorkflowF](Selector.Doc(
          BsonField.Name("pop") -> Selector.Gte(Bson.Int64(1000)))),
        $group[WorkflowF](
          Grouped(ListMap()),
          Reshape(ListMap(
            BsonField.Name("0") -> $field("city").right)).left),
        $project[WorkflowF](
          Reshape(ListMap(
            BsonField.Name("c") -> $field("_id", "0").right)),
          ExcludeId))

      toJS(wf) must beRightDisjunction(
        """db.zips.distinct("city", { "pop": { "$gte": NumberLong("1000") } }).map(
          |  function (elem) { return { "c": elem } });
          |""".stripMargin)
    }

    "write simple pipeline workflow to JS" in {
      val wf = chain(
        $read[WorkflowF](collection("db", "zips")),
        $match[WorkflowF](Selector.Doc(
          BsonField.Name("pop") -> Selector.Gte(Bson.Int64(1000)))))

      toJS(wf) must beRightDisjunction(
        """db.zips.find({ "pop": { "$gte": NumberLong("1000") } });
          |""".stripMargin)
    }

    "write chained pipeline workflow to JS find()" in {
      val wf = chain(
        $read[WorkflowF](collection("db", "zips")),
        $match[WorkflowF](Selector.Doc(
          BsonField.Name("pop") -> Selector.Lte(Bson.Int64(1000)))),
        $match[WorkflowF](Selector.Doc(
          BsonField.Name("pop") -> Selector.Gte(Bson.Int64(100)))),
        $sort[WorkflowF](NonEmptyList(BsonField.Name("city") -> SortDir.Ascending)))

      toJS(wf) must beRightDisjunction(
        """db.zips.find(
          |  {
          |    "$and": [
          |      { "pop": { "$lte": NumberLong("1000") } },
          |      { "pop": { "$gte": NumberLong("100") } }]
          |  }).sort(
          |  { "city": NumberInt("1") });
          |""".stripMargin)
    }

    "write chained pipeline workflow to JS" in {
      val wf = chain(
        $read[WorkflowF](collection("db", "zips")),
        $match[WorkflowF](Selector.Doc(
          BsonField.Name("pop") -> Selector.Lte(Bson.Int64(1000)))),
        $match[WorkflowF](Selector.Doc(
          BsonField.Name("pop") -> Selector.Gte(Bson.Int64(100)))),
        $group[WorkflowF](
          Grouped(ListMap(
            BsonField.Name("pop") -> $sum($field("pop")))),
          $field("city").right),
        $sort[WorkflowF](NonEmptyList(BsonField.Name("_id") -> SortDir.Ascending)))

      toJS(wf) must beRightDisjunction(
        """db.zips.aggregate(
          |  [
          |    {
          |      "$match": {
          |        "$and": [
          |          { "pop": { "$lte": NumberLong("1000") } },
          |          { "pop": { "$gte": NumberLong("100") } }]
          |      }
          |    },
          |    { "$group": { "pop": { "$sum": "$pop" }, "_id": "$city" } },
          |    { "$sort": { "_id": NumberInt("1") } }],
          |  { "allowDiskUse": true });
          |""".stripMargin)
    }

    "write map-reduce Workflow to JS" in {
      val wf = chain(
        $read[WorkflowF](collection("db", "zips")),
        $map[WorkflowF]($MapF.mapKeyVal(("key", "value"),
          Js.Select(Js.Ident("value"), "city"),
          Js.Select(Js.Ident("value"), "pop")),
          ListMap()),
        $reduce[WorkflowF](Js.AnonFunDecl(List("key", "values"), List(
          Js.Return(Js.Call(
            Js.Select(Js.Ident("Array"), "sum"),
            List(Js.Ident("values")))))),
          ListMap()))

      toJS(wf) must beRightDisjunction(
        s"""db.zips.mapReduce(
          |  function () {
          |    emit.apply(
          |      null,
          |      (function (key, value) { return [value.city, value.pop] })(
          |        this._id,
          |        this))
          |  },
          |  function (key, values) { return Array.sum(values) },
          |  {
          |    "out": { "inline": NumberLong("1") },
          |    "finalize": function (key, value) { return { "${sigil.Quasar}": value } }
          |  });
          |""".stripMargin)
    }

    "write $where condition to JS" in {
      val wf = chain(
        $read[WorkflowF](collection("db", "zips2")),
        $match[WorkflowF](Selector.Where(Js.Ident("foo"))))

      toJS(wf) must beRightDisjunction(
        """db.zips2.mapReduce(
          |  function () {
          |    emit.apply(
          |      null,
          |      (function (key, value) { return [key, value] })(this._id, this))
          |  },
          |  function (key, values) { return values[0] },
          |  {
          |    "out": { "inline": NumberLong("1") },
          |    "query": { "$where": function () { return foo } }
          |  });
          |""".stripMargin)
    }

    "write join Workflow to JS" in {
      val wf =
        $foldLeft[WorkflowF](
          chain(
            $read[WorkflowF](collection("db", "zips1")),
            $match[WorkflowF](Selector.Doc(
              BsonField.Name("city") -> Selector.Eq(Bson.Text("BOULDER"))))),
          chain(
            $read[WorkflowF](collection("db", "zips2")),
            $match[WorkflowF](Selector.Doc(
              BsonField.Name("pop") -> Selector.Lte(Bson.Int64(1000)))),
            $map[WorkflowF]($MapF.mapKeyVal(("key", "value"),
              Js.Select(Js.Ident("value"), "city"),
              Js.Select(Js.Ident("value"), "pop")),
              ListMap()),
            $reduce[WorkflowF](Js.AnonFunDecl(List("key", "values"), List(
              Js.Return(Js.Call(
                Js.Select(Js.Ident("Array"), "sum"),
                List(Js.Ident("values")))))),
              ListMap())))

      toJS(wf) must beRightDisjunction(
        """db.zips1.aggregate(
          |  [
          |    { "$match": { "city": "BOULDER" } },
          |    { "$project": { "value": "$$ROOT" } },
          |    { "$out": "tmp.gen_0" }],
          |  { "allowDiskUse": true });
          |db.zips2.mapReduce(
          |  function () {
          |    emit.apply(
          |      null,
          |      (function (key, value) { return [value.city, value.pop] })(
          |        this._id,
          |        this))
          |  },
          |  function (key, values) { return Array.sum(values) },
          |  {
          |    "out": { "reduce": "tmp.gen_0", "db": "db", "nonAtomic": true },
          |    "query": { "pop": { "$lte": NumberLong("1000") } }
          |  });
          |db.tmp.gen_0.find();
          |""".stripMargin)
    }
  }

  "SimpleCollectionNamePattern" should {
    import JavaScriptWorkflowExecutor.SimpleCollectionNamePattern

    "match identifier" in {
      SimpleCollectionNamePattern.unapplySeq("foo") must beSome
    }

    "not match leading _" in {
      SimpleCollectionNamePattern.unapplySeq("_foo") must beNone
    }

    "match dot-separated identifiers" in {
      SimpleCollectionNamePattern.unapplySeq("foo.bar") must beSome
    }

    "match everything allowed" in {
      SimpleCollectionNamePattern.unapplySeq("foo2.BAR_BAZ") must beSome
    }

    "not match leading digit" in {
      SimpleCollectionNamePattern.unapplySeq("123") must beNone
    }

    "not match leading digit in second position" in {
      SimpleCollectionNamePattern.unapplySeq("foo.123") must beNone
    }
  }
}
