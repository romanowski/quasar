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

package quasar.api.services

import slamdata.Predef.StringContext
import quasar.api._
import quasar.db.DbConnectionConfig
import quasar.fp.free._
import quasar.main.{MainErrT, MetaStoreLocation}
import quasar.metastore.MetaStore.{ShouldCopy, ShouldInitialize}

import argonaut.Json
import argonaut.Argonaut._
import org.http4s.dsl._
import org.http4s.argonaut._
import scalaz._, Scalaz._
import scalaz.concurrent.Task

object metastore {

  def service[S[_]](implicit meta: MetaStoreLocation.Ops[S], S0: Task :<: S): QHttpService[S] = {

    QHttpService {
      case GET -> Root =>
        respond(meta.get.map(_.asJson(DbConnectionConfig.secureEncodeJson)))
      case req @ PUT -> Root =>
        val initialize: ShouldInitialize = ShouldInitialize(req.params.keys.toList.contains("initialize"))
        val copy: ShouldCopy = ShouldCopy(req.params.keys.toList.contains("copy"))
        respondT((for {
          connConfigJson <- lift(req.as[Json]).into[S].liftM[MainErrT]
          connConfig     <- EitherT.fromEither(connConfigJson.as[DbConnectionConfig].result.leftMap(_._1).point[Free[S, ?]])
          _              <- EitherT(meta.set(connConfig, initialize, copy))
          newUrl         =  DbConnectionConfig.connectionInfo(connConfig).url
          initializedStr =  if (initialize.v) "newly initialized " else ""
          copiedStr      =  if (copy.v) "Metastore copied. " else ""
        } yield {
          s"${copiedStr}Now using ${initializedStr}metastore located at $newUrl"}
          ).leftMap(msg => ApiError.fromMsg_(BadRequest withReason "UninitializedMetastore", msg)))
    }
  }
}
