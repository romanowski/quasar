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

package quasar.physical.sparkcore.fs.cassandra

import quasar.Predef._
import quasar.effect._
import quasar.contrib.pathy._
import quasar.{Data, DataCodec}
import quasar.physical.sparkcore.fs.queryfile.Input
import quasar.fs._,
  FileSystemError._, 
  PathError._

import org.apache.spark.SparkContext
import org.apache.spark.rdd._
import com.datastax.spark.connector._
import com.datastax.driver.core.Session
import com.datastax.spark.connector.cql.CassandraConnector
import scalaz._, Scalaz._
import scalaz.concurrent.Task
import pathy.Path._


object queryfile {

  def fromFile(sc: SparkContext, file: AFile): Task[RDD[String]] = Task.delay {
    sc.cassandraTable[String](keyspace(fileParent(file)), tableName(file))
      .select("data")
  }

  def store[S[_]](rdd: RDD[Data], out: AFile)(implicit 
    read: Read.Ops[SparkContext, S]
    ): Free[S, Unit] = read.asks { sc =>
      val ks = keyspace(fileParent(out))
      val tb = tableName(out)

      val connector = CassandraConnector(sc.getConf)

      connector.withSessionDo { implicit session =>
        val k = if(!keyspaceExists(ks)) {
          session.execute(s"CREATE KEYSPACE $ks WITH replication = {'class': 'SimpleStrategy', 'replication_factor': 1};")
        }


        if(!tableExists(ks, tb)){
            val u = session.execute(s"CREATE TABLE $ks.$tb (id timeuuid PRIMARY KEY, data text);")
        }
        rdd.flatMap(data =>
          DataCodec.render(data)(DataCodec.Precise).toList).collect().foreach (v => insertData(ks, tb, v))
      }
    }

  def fileExists[S[_]](f: AFile)(implicit
    read: Read.Ops[SparkContext, S]
  ): Free[S, Boolean] = read.asks { sc =>
    CassandraConnector(sc.getConf).withSessionDo{ implicit session =>
      tableExists(keyspace(fileParent(f)), tableName(f))
    }
  }

  def listContents[S[_]](d: ADir)(implicit
    read: Read.Ops[SparkContext, S]
  ): Free[S, FileSystemError \/ Set[PathSegment]] = 
    read.asks { sc =>
      CassandraConnector(sc.getConf).withSessionDo{ implicit session =>

        val k = keyspace(d)
        val dirsRDD = sc.cassandraTable[String]("system_schema", "keyspaces")
            .select("keyspace_name")
            .filter(!_.startsWith("system"))
            .filter(_.startsWith(k))
            .map { kspc =>
              val dir = kspc.replace(k, "").split("_")(0)
              DirName(dir)
            }

        if(dirsRDD.count() > 0) {
         val files = if(k.length > 0 && keyspaceExists(k)) {
           sc.cassandraTable[String]("system_schema", "tables")
            .select("table_name")
            .where("keyspace_name = ?", keyspace(d))
            .map { table =>
              FileName(table).right[DirName]
            }.collect.toSet

        } else {
          Set[PathSegment]()
        } 

          val dirs = dirsRDD.filter(_.value.length > 0)
            .map(_.left[FileName])
            .collect.toSet

          (files ++ dirs).right[FileSystemError]
        }else{
          pathErr(pathNotFound(d)).left[Set[PathSegment]] 
        }

      }
    }

  def readChunkSize: Int = 5000

  def input[S[_]](implicit
    read: Read.Ops[SparkContext, S]
  ): Input[S] = 
    Input(fromFile _, store[S] _, fileExists[S] _, listContents[S] _, readChunkSize _)

  private def insertData(keyspace: String, table: String, data: String)(implicit session: Session) = {
    val stmt = session.prepare(s"INSERT INTO $keyspace.$table (id, data) VALUES (now(),  ?);")
    session.execute(stmt.bind(data))
  }

  private def keyspace(dir: ADir) =
    posixCodec.printPath(dir).substring(1).replace("/", "_")

  private def tableName(file: AFile) =
    posixCodec.printPath(file).split("/").reverse(0)

  private def keyspaceExists(keyspace: String)(implicit session: Session) = {
    val stmt = session.prepare("SELECT * FROM system_schema.keyspaces WHERE keyspace_name = ?;")
    session.execute(stmt.bind(keyspace)).all().size() > 0
  }

  private def tableExists(keyspace: String, table: String)(implicit session: Session) = {
    val stmt = session.prepare("SELECT * FROM system_schema.tables WHERE keyspace_name = ? AND table_name = ?;")
    session.execute(stmt.bind(keyspace, table)).all().size() > 0
  }

}
