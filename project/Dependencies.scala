package quasar.project

import scala.Boolean
import scala.collection.Seq

import sbt._

object Dependencies {
  private val algebraVersion      = "0.7.0"
  private val argonautVersion     = "6.2"
  private val disciplineVersion   = "0.7.2"
  private val doobieVersion       = "0.4.4"
  private val jawnVersion         = "0.10.4"
  private val jacksonVersion      = "2.4.4"
  private val matryoshkaVersion   = "0.18.3"
  private val monocleVersion      = "1.4.0"
  private val pathyVersion        = "0.2.11"
  private val raptureVersion      = "2.0.0-M9"
  private val refinedVersion      = "0.8.3"
  private val scodecBitsVersion   = "1.1.2"
  private val http4sVersion       = "0.16.6a"
  private val scalacheckVersion   = "1.13.4"
  private val scalazVersion       = "7.2.17"
  private val scalazStreamVersion = "0.8.6a"
  private val shapelessVersion    = "2.3.2"
  private val simulacrumVersion   = "0.10.0"
  // For unknown reason sbt-slamdata's specsVersion, 3.8.7,
  // leads to a ParquetRDDE failure under a full test run
  private val specsVersion        = "4.0.2"
  private val spireVersion        = "0.14.1"

  def foundation = Seq(
    "com.slamdata"               %% "slamdata-predef"           % "0.0.4",
    "org.scalaz"                 %% "scalaz-core"               % scalazVersion,
    "org.scalaz"                 %% "scalaz-concurrent"         % scalazVersion,
    "org.scalaz.stream"          %% "scalaz-stream"             % scalazStreamVersion,
    "com.github.julien-truffaut" %% "monocle-core"              % monocleVersion,
    "org.typelevel"              %% "algebra"                   % algebraVersion,
    "org.typelevel"              %% "spire"                     % spireVersion,
    "io.argonaut"                %% "argonaut"                  % argonautVersion,
    "io.argonaut"                %% "argonaut-scalaz"           % argonautVersion,
    "com.slamdata"               %% "matryoshka-core"           % matryoshkaVersion,
    "com.slamdata"               %% "pathy-core"                % pathyVersion,
    "com.slamdata"               %% "pathy-argonaut"            % pathyVersion,
    "eu.timepit"                 %% "refined"                   % refinedVersion,
    "com.chuusai"                %% "shapeless"                 % shapelessVersion,
    "org.scalacheck"             %% "scalacheck"                % scalacheckVersion,
    "com.propensive"             %% "contextual"                % "1.0.1",
    "com.github.mpilquist"       %% "simulacrum"                % simulacrumVersion                    % Test,
    "org.typelevel"              %% "algebra-laws"              % algebraVersion                       % Test,
    "org.typelevel"              %% "discipline"                % disciplineVersion                    % Test,
    "org.typelevel"              %% "spire-laws"                % spireVersion                         % Test,
    "org.specs2"                 %% "specs2-core"               % specsVersion                         % Test,
    "org.specs2"                 %% "specs2-scalacheck"         % specsVersion                         % Test,
    "org.scalaz"                 %% "scalaz-scalacheck-binding" % (scalazVersion + "-scalacheck-1.13") % Test,
    "org.typelevel"              %% "shapeless-scalacheck"      % "0.6.1"                              % Test,
    "org.typelevel"              %% "scalaz-specs2"             % "0.5.2"                              % Test
  )

  def frontend = Seq(
    "com.github.julien-truffaut" %% "monocle-macro"            % monocleVersion,
    "org.scala-lang.modules"     %% "scala-parser-combinators" % "1.0.6",
    "org.typelevel"              %% "algebra-laws"             % algebraVersion  % Test
  )

  def ejson = Seq(
    "org.spire-math" %% "jawn-parser" % jawnVersion
  )
  def effect = Seq(
    "com.fasterxml.uuid" % "java-uuid-generator" % "3.1.4"
  )
  def core = Seq(
    "org.tpolecat"               %% "doobie-core"               % doobieVersion,
    "org.tpolecat"               %% "doobie-hikari"             % doobieVersion,
    "org.tpolecat"               %% "doobie-postgres"           % doobieVersion,
    "org.http4s"                 %% "http4s-core"               % http4sVersion,
    "com.github.julien-truffaut" %% "monocle-macro"             % monocleVersion,
    "com.github.tototoshi"       %% "scala-csv"                 % "1.3.4",
    "com.slamdata"               %% "pathy-argonaut"            % pathyVersion,
    // Removing this will not cause any compile time errors, but will cause a runtime error once
    // Quasar attempts to connect to an h2 database to use as a metastore
    "com.h2database"              % "h2"                        % "1.4.196",
    "org.tpolecat"               %% "doobie-specs2"             % doobieVersion % Test
  )
  def interface = Seq(
    "com.github.scopt" %% "scopt" % "3.5.0",
    "org.jboss.aesh"    % "aesh"  % "0.66.17"
  )

  def mongodb = {
    val nettyVersion = "4.1.14.Final"

    Seq(
      "org.mongodb" % "mongodb-driver-async" %   "3.5.0",
      // These are optional dependencies of the mongo asynchronous driver.
      // They are needed to connect to mongodb vis SSL which we do under certain configurations
      "io.netty"    % "netty-buffer"         % nettyVersion,
      "io.netty"    % "netty-handler"        % nettyVersion
    )
  }

  def rdbmscore = {
    Seq(
      "org.tpolecat" %% "doobie-core"       % doobieVersion,
      "org.tpolecat" %% "doobie-postgres"   % doobieVersion,
      "org.tpolecat" %% "doobie-hikari"     % doobieVersion,
      "org.tpolecat" %% "doobie-h2"         % doobieVersion,
      "com.github.alexarchambault" %% "scalacheck-shapeless_1.13" % "1.1.6" % Test,
      "org.tpolecat" %% "doobie-specs2"     % doobieVersion % Test
    )
  }

  def sparkcore(sparkProvided: Boolean) = Seq(
    ("org.apache.spark" %% "spark-core" % "2.2.0" % (if(sparkProvided) "provided" else "compile"))
      .exclude("aopalliance", "aopalliance")                  // It seems crazy that we need to do this,
      .exclude("javax.inject", "javax.inject")                // but it looks like Spark had some dependency conflicts
      .exclude("commons-collections", "commons-collections")  // among its transitive dependencies which means
      .exclude("commons-beanutils", "commons-beanutils-core") // we need to exclude this stuff so that we can
      .exclude("commons-logging", "commons-logging")          // create an assembly jar without conflicts
      .exclude("commons-logging", "commons-logging")          // It would seem though that things work without them...
      .exclude("com.esotericsoftware.minlog", "minlog")       // It's likely this list will need to be updated
      .exclude("org.spark-project.spark", "unused")           // anytime the Spark dependency itselft is updated
      .excludeAll(ExclusionRule(organization = "io.netty")),
    ("org.apache.spark" %% "spark-sql" % "2.2.0" % (if(sparkProvided) "provided" else "compile"))
      .exclude("aopalliance", "aopalliance")                  // Same limitation
      .exclude("javax.inject", "javax.inject")                // as above for
      .exclude("commons-collections", "commons-collections")  // spark-sql dependency.
      .exclude("commons-beanutils", "commons-beanutils-core") // This hopefully will go away
      .exclude("commons-logging", "commons-logging")          // in near future with
      .exclude("commons-logging", "commons-logging")          // classloaders magic
      .exclude("com.esotericsoftware.minlog", "minlog")       // Keep calm and
      .exclude("org.spark-project.spark", "unused")           // ignore Spark.
      .excludeAll(ExclusionRule(organization = "io.netty")),
    "io.netty" % "netty-all" % "4.0.43.Final",    // we need THIS version
    ("org.apache.hadoop" % "hadoop-aws" % "2.7.3")
      .exclude("com.esotericsoftware.minlog", "minlog")
      .exclude("commons-collections", "commons-collections")
      .exclude("commons-beanutils", "commons-beanutils-core")
      .exclude("commons-logging", "commons-logging"),
    "org.apache.parquet"     % "parquet-format"          % "2.3.1",
    "org.apache.parquet"     % "parquet-hadoop"          % "1.9.0",
    ("com.datastax.spark" %% "spark-cassandra-connector" % "2.0.3")
      .excludeAll(ExclusionRule(organization = "io.netty")),
    "org.http4s"             %% "http4s-core"            % http4sVersion,
    "org.http4s"             %% "http4s-blaze-client"    % http4sVersion,
    "org.elasticsearch"      %% "elasticsearch-spark-20" % "5.4.1",
    ("com.sksamuel.elastic4s" %% "elastic4s-http"         % "5.4.6")
      .exclude("commons-logging", "commons-logging"),
    "io.verizon.delorean" %% "core" % "1.2.42-scalaz-7.2",
    // Please note that elastic4s-jackson and elastic4s-testkit DON'T contain
    // dependency to io.netty:netty-all in the elastic4s build.sbt. For the
    // unknown reasons however netty-all is a deriviative dependency (@daniel suspects
    // bug in ivy) thus we must exclude netty-all here since it is a conflicting version 4.1.x
    ("com.sksamuel.elastic4s" %% "elastic4s-jackson"      % "5.4.6")
      .exclude("io.netty", "netty-all"),
    ("com.sksamuel.elastic4s" %% "elastic4s-testkit"      % "5.4.6" % Test)
      .exclude("org.scalatest", "scalatest_2.11")
      .exclude("io.netty", "netty-all"),
    "org.apache.logging.log4j"              % "log4j-core"                % "2.6.2"
  )

  def marklogic = Seq(
    "com.fasterxml.jackson.core" %  "jackson-core"         % jacksonVersion,
    "com.fasterxml.jackson.core" %  "jackson-databind"     % jacksonVersion,
    "com.marklogic"              %  "marklogic-xcc"        % "8.0.5",
    "com.slamdata"               %% "xml-names-core"       % "0.0.1",
    "org.scala-lang.modules"     %% "scala-xml"            % "1.0.6",
    "eu.timepit"                 %% "refined-scalaz"       % refinedVersion,
    "eu.timepit"                 %% "refined-scalacheck"   % refinedVersion % Test,
    "com.slamdata"               %% "xml-names-scalacheck" % "0.0.1"        % Test
  )
  val couchbase = Seq(
    "com.couchbase.client" %  "java-client" % "2.3.5",
    "io.reactivex"         %% "rxscala"     % "0.26.4",
    "org.http4s"           %% "http4s-core" % http4sVersion,
    "log4j"                %  "log4j"       % "1.2.17" % Test
  )
  def web = Seq(
    "org.http4s"     %% "http4s-dsl"          % http4sVersion,
    "org.http4s"     %% "http4s-argonaut"     % http4sVersion,
    "org.http4s"     %% "http4s-client"       % http4sVersion,
    "org.http4s"     %% "http4s-server"       % http4sVersion,
    "org.http4s"     %% "http4s-blaze-server" % http4sVersion,
    "org.http4s"     %% "http4s-blaze-client" % http4sVersion,
    "org.scodec"     %% "scodec-scalaz"       % "1.4.1a",
    "org.scodec"     %% "scodec-bits"         % scodecBitsVersion,
    "com.propensive" %% "rapture-json"        % raptureVersion     % Test,
    "com.propensive" %% "rapture-json-json4s" % raptureVersion     % Test,
    "eu.timepit"     %% "refined-scalacheck"  % refinedVersion     % Test
  )
  def precog = Seq(
    "org.slf4s"            %% "slf4s-api"       % "1.7.25",
    "org.slf4j"            %  "slf4j-log4j12"   % "1.7.16",
    "org.typelevel"        %% "spire"           % spireVersion,
    "org.scodec"           %% "scodec-scalaz"   % "1.4.1a",
    "org.apache.jdbm"      %  "jdbm"            % "3.0-alpha5",
    "com.typesafe.akka"    %%  "akka-actor"     % "2.5.1",
    ("org.quartz-scheduler" %  "quartz"         % "2.3.0")
      .exclude("com.zaxxer", "HikariCP-java6"), // conflict with Doobie
    "commons-io"           %  "commons-io"      % "2.5",
    "org.scodec"           %% "scodec-bits"     % scodecBitsVersion
  )
  def it = Seq(
    "io.argonaut"      %% "argonaut-monocle"    % argonautVersion     % Test,
    "org.http4s"       %% "http4s-blaze-client" % http4sVersion       % Test,
    "eu.timepit"       %% "refined-scalacheck"  % refinedVersion      % Test,
    "io.verizon.knobs" %% "core"                % "4.0.30-scalaz-7.2" % Test)
}
