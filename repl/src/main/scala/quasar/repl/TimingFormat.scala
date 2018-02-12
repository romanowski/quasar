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

package quasar.repl

import slamdata.Predef._

import scalaz._, Scalaz._

sealed abstract class TimingFormat
object TimingFormat {
  // Print timing data as JSON
  case object Json extends TimingFormat
  // Print timing data as a RenderedTree
  case object Tree extends TimingFormat
  // Only include the total time
  case object OnlyTotal extends TimingFormat
  // Print no timing data
  case object Nothing extends TimingFormat

  def fromString(str: String): Option[TimingFormat] = str.toLowerCase match {
    case "json"      => Json.some
    case "tree"      => Tree.some
    case "onlytotal" => OnlyTotal.some
    case "nothing"   => Nothing.some
    case _           => none
  }
}
