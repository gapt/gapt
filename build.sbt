import java.io.ByteArrayOutputStream

import org.apache.commons.compress.archivers.tar.{ TarArchiveEntry, TarArchiveOutputStream }
import sys.process._

val Version = "2.17.0-SNAPSHOT"

lazy val commonSettings = Seq(
  organization := "at.logic.gapt",
  homepage := Some( url( "https://logic.at/gapt/" ) ),
  organizationHomepage := homepage.value,
  licenses += ( "GPL-3.0" -> url( "http://www.gnu.org/licenses/gpl-3.0.html" ) ),
  startYear := Some( 2008 ),
  version := Version,
  autoAPIMappings := true,
  publishMavenStyle := true,

  publishTo := ( if ( isSnapshot.value )
    Opts.resolver.sonatypeOssSnapshots.headOption
  else
    Some( Opts.resolver.sonatypeStaging ) ),

  scmInfo := Some( ScmInfo(
    browseUrl = url( "https://github.com/gapt/gapt" ),
    connection = "scm:git:https://github.com/gapt/gapt.git",
    devConnection = Some( "scm:git:git@github.com:gapt/gapt.git" ) ) ),

  crossScalaVersions := Seq("2.13.12", "3.3.1"),
  scalaVersion := "2.13.12",

  developers := List(
    Developer(
      id = "jvierling",
      name = "Jannik Vierling",
      email = "jannik.vierling@gmail.com",
      url = url( "https://jvierling.github.io/" ) ),
    Developer(
      id = "shetzl",
      name = "Stefan Hetzl",
      email = "stefan.hetzl@tuwien.ac.at",
      url = url( "http://dmg.tuwien.ac.at/hetzl/" ) ),
    Developer(
      id = "gebner",
      name = "Gabriel Ebner",
      email = "gebner@gebner.org",
      url = url( "https://gebner.org/" ) ) ),

  Compile / scalacOptions ++= Seq(
    "-deprecation",
    "-language:postfixOps",
    "-language:implicitConversions",
    "-feature",
    "-unchecked" ) ++ (
        CrossVersion.partialVersion(scalaVersion.value) match {
          case Some((3,_)) => Seq(
            "-source:3.2-migration",
            "-explain")
          case _ => Seq()
        }
      ),

  javaOptions ++= Seq( "-Xss40m", "-Xmx1g" ),
  fork := true,
  run / baseDirectory := file( "." ),

  sourcesInBase := false // people like to keep scripts lying around
)

val specs2Version = "4.16.0"
lazy val testSettings = Seq(
  Test / testOptions += Tests.Argument( TestFrameworks.Specs2, "junitxml", "console" ),
  Test / javaOptions += "-Xmx2g",
  libraryDependencies ++= Seq(
    "org.specs2" %% "specs2-core" % specs2Version,
    "org.specs2" %% "specs2-junit" % specs2Version, // needed for junitxml output
    "org.specs2" %% "specs2-matcher" % specs2Version ) map ( _ % Test ) )

lazy val BuildSbtConfig = config( "buildsbt" ) extend Compile

lazy val root = project.in( file( "." ) ).
  aggregate( core, examples, tests, userManual, cli, testing ).
  dependsOn( core, examples, cli ).
  settings( commonSettings: _* ).
  enablePlugins( ScalaUnidocPlugin ).
  settings(
    console / fork := true,
    console / initialCommands := IO.read( resourceDirectory.in( cli, Compile ).value / "gapt-cli-prelude.scala" ),

    publish / skip := true,
    packagedArtifacts := Map(),

    apiURL := Some( url( "https://logic.at/gapt/api/" ) ),
    scalacOptions in ( ScalaUnidoc, unidoc ) ++= Seq(
      "-doc-title", "gapt",
      "-doc-version", version.value,
      "-doc-source-url", s"https://github.com/gapt/gapt/blob/${("git rev-parse HEAD" !!).strip}/€{FILE_PATH}.scala",
      "-doc-root-content", ( baseDirectory.value / "doc" / "rootdoc.txt" ).getAbsolutePath,
      "-sourcepath", baseDirectory.value.getAbsolutePath,
      "-skip-packages", "ammonite:ammonite.ops",
      "-diagrams",
      "-implicits", "-implicits-show-all",
      "-skip-packages", "scala" ) ,

    scripts := {
      val runJVMOptions = javaOptions.value ++ Seq( "-cp", Path.makeString(
        Attributed.data( fullClasspath.in( cli, Compile ).value ++ fullClasspath.in( testing, Compile ).value distinct ) ) )
      def mkScript( file: File, extraArgs: String* ) = {
        IO.write(
          file,
          s"#!/bin/sh\njava ${( runJVMOptions ++ extraArgs ).mkString( " " )} ${"\"$@\""}\n" )
        file.setExecutable( true )
      }
      (
        mkScript( target.value / "run" ),
        mkScript( target.value / "test-cut-intro", "gapt.testing.testCutIntro" ),
        mkScript( target.value / "test-pi2-cut-intro", "gapt.testing.testPi2CutIntro" ),
        mkScript( target.value / "test-induction", "gapt.testing.testInduction" ),
        mkScript( target.value / "viper", "gapt.provers.viper.Viper" ),
        mkScript( target.value / "escargot", "gapt.provers.escargot.Escargot" ),
        mkScript( target.value / "slakje", "gapt.provers.slakje.Slakje" ),
        mkScript( target.value / "cli", "gapt.cli.CLIMain" ) )
    },

    // Release stuff
    assembly / mainClass := Some( "gapt.cli.CLIMain" ),
    assembly / aggregate := false,
    releaseDist := {
      val baseDir = file( "." )
      val version = Keys.version.value
      val apidocs = doc.in( ScalaUnidoc, unidoc ).value

      val archiveFile = file( "." ) / "target" / s"gapt-$version.tar.gz"

      Process( List( "latexmk", "-pdf", "-silent", "user_manual.tex" ), baseDir / "doc" ) !

      val filesToIncludeAsIs = List(
        "COPYING", "gapt.sh", "slakje.sh", "escargot.sh", "viper.sh", "include.sh", "examples" )
      val entries = List( ( assembly.value, s"gapt-$version.jar" ) ) ++
        filesToIncludeAsIs.flatMap { fn => recursiveListFiles( baseDir / fn ) }
        .map { f => ( f, baseDir.toPath.relativize( f.toPath ) ) } ++
        List(
          ( baseDir / "doc/README.dist", "README" ),
          ( baseDir / "doc/user_manual.pdf", "user_manual.pdf" ) ) ++
          recursiveListFiles( apidocs ).map { f => f -> s"apidocs/${apidocs.toPath.relativize( f.toPath )}" }

      val archiveStem = s"gapt-$version"

      IO.gzipFileOut( archiveFile ) { gzipOut =>
        val tarOut = new TarArchiveOutputStream( gzipOut )
        tarOut.setLongFileMode( TarArchiveOutputStream.LONGFILE_POSIX )

        entries.foreach {
          case ( file, pathInArchive ) =>
            val tarEntry = new TarArchiveEntry( file, s"$archiveStem/$pathInArchive" )
            if ( file.canExecute ) tarEntry.setMode( BigInt( "755", 8 ).toInt )
            tarOut.putArchiveEntry( tarEntry )
            IO.transfer( file, tarOut )
            tarOut.closeArchiveEntry()
        }

        tarOut.close()
      }

      archiveFile
    },

    evalUserManual := {
      val userManFn = "doc/user_manual.tex"
      val out = new ByteArrayOutputStream
      val exitVal = new Fork( "java", Some( "gapt.doc.evalCodeSnippets" ) ).fork(
        ForkOptions(
          javaHome = javaHome.value,
          outputStrategy = Some( CustomOutput( out ) ),
          bootJars = Vector(),
          workingDirectory = Some( new java.io.File( "." ) ),
          runJVMOptions = Vector() ++ javaOptions.value ++ Seq( "-cp", Path.makeString(
            Attributed.data( fullClasspath.in( userManual, Compile ).value ) ) ),
          connectInput = false,
          envVars = envVars.value ),
        Seq( userManFn ) ).exitValue()
      if ( exitVal == 0 ) IO.write( file( userManFn ), out.toByteArray )
    } ,

    dependencyOverrides ++= dependencyConflictResolutions
    )

val dependencyConflictResolutions = Seq(
      "com.lihaoyi" %% "geny" % "1.0.0"
    )

lazy val core = project.in( file( "core" ) ).
  settings( commonSettings: _* ).
  settings(
    name := "gapt",
    description := "General Architecture for Proof Theory",

    Compile / scalacOptions += "-Xfatal-warnings",

    libraryDependencies ++= Seq(
      "org.scala-lang.modules" %% "scala-parallel-collections" % "1.0.4",
      "org.scala-lang.modules" %% "scala-parser-combinators" % "2.1.1",
      "org.parboiled" %% "parboiled" % "2.4.0",
      "com.lihaoyi" %% "fastparse" % "3.0.2",
      "com.lihaoyi" %% "sourcecode" % "0.2.8",
      "org.typelevel" %% "cats-free" % "2.7.0",
      "org.scala-lang.modules" %% "scala-xml" % "2.1.0",
      "org.apache.commons" % "commons-lang3" % "3.12.0",
      "com.lihaoyi" %% "os-lib" % "0.9.3",
      "de.uni-freiburg.informatik.ultimate" % "smtinterpol" % "2.5",
      "com.github.scopt" %% "scopt" % "4.0.1",
      "org.ow2.sat4j" % "org.ow2.sat4j.core" % "2.3.6",
      "org.ow2.sat4j" % "org.ow2.sat4j.maxsat" % "2.3.6")
      ++ {
        CrossVersion.partialVersion(scalaVersion.value) match {
          case Some((2, 13)) => Seq(
            "org.scala-lang" % "scala-reflect" % scalaVersion.value
          )
          case _ => Seq.empty
        }
      },

    dependencyOverrides ++= dependencyConflictResolutions,
    // UI
    libraryDependencies ++= Seq(
      "org.scala-lang.modules" %% "scala-swing" % "3.0.0",
      "com.itextpdf" % "itextpdf" % "5.5.13.3",
      "org.scilab.forge" % "jlatexmath" % "1.0.7" ),

    // JSON serialization
    libraryDependencies += "org.json4s" %% "json4s-native" % "4.0.5",
    libraryDependencies ++= Seq(
      "io.circe" %% "circe-core",
      "io.circe" %% "circe-generic",
      "io.circe" %% "circe-parser").map( _ % "0.14.6" )
      ++ {
        CrossVersion.partialVersion(scalaVersion.value) match {
          case Some((2, 13)) => Seq(
            "io.circe" %% "circe-generic-extras" % "0.14.3"
          )
          case _ => Seq.empty
        }
      }
  )

lazy val examples = project.in( file( "examples" ) ).
  dependsOn( core ).
  settings( commonSettings: _* ).
  settings(
    name := "gapt-examples",
    Compile / unmanagedSourceDirectories := Seq( baseDirectory.value ),
    Compile / resourceDirectory := baseDirectory.value,
    excludeFilter in ( Compile, unmanagedResources ) := {
      val target = ( baseDirectory.value / "target" ).getCanonicalPath
      new SimpleFileFilter( _.getCanonicalPath startsWith target )
    } || "*.scala",

    excludeFilter in (Compile, unmanagedSources) := {
      CrossVersion.partialVersion(scalaVersion.value) match {
          case Some((2, _)) =>
            new SimpleFileFilter( _.getCanonicalPath startsWith (baseDirectory.value / "scala-3").getCanonicalPath)
          
          case _ => new SimpleFileFilter( _.getCanonicalPath startsWith (baseDirectory.value / "scala-2").getCanonicalPath)
        }
    },
    dependencyOverrides ++= dependencyConflictResolutions )

lazy val tests = project.in( file( "tests" ) ).
  dependsOn( core, examples ).
  settings( commonSettings: _* ).
  settings( testSettings: _* ).
  disablePlugins( JUnitXmlReportPlugin ).
  settings(
    testForkedParallel := true,
    publish / skip := true,
    packagedArtifacts := Map(),
    dependencyOverrides ++= dependencyConflictResolutions )

lazy val userManual = project.in( file( "doc" ) ).
  dependsOn( cli ).
  settings( commonSettings: _* ).
  settings(
    Compile / unmanagedSourceDirectories := Seq( baseDirectory.value ),
    publish / skip := true,
    packagedArtifacts := Map(),
    dependencyOverrides ++= dependencyConflictResolutions )

lazy val cli = project.in( file( "cli" ) ).
  dependsOn( core, examples ).
  settings( commonSettings: _* ).
  settings(
    mainClass := Some( "gapt.cli.CLIMain" ),
    Compile / scalacOptions += "-Xfatal-warnings",
    crossScalaVersions := Seq("2.13.12"),
    libraryDependencies ++= Seq(
      "org.scala-lang" % "scala-compiler" % scalaVersion.value ),
    publish / skip := true,
    packagedArtifacts := Map(),
    dependencyOverrides ++= dependencyConflictResolutions )

addCommandAlias( "format", ";" )

lazy val testing = project.in( file( "testing" ) ).
  dependsOn( core, examples ).
  settings( commonSettings: _* ).
  settings(
    name := "gapt-testing",
    description := "gapt extended regression tests",
    Compile / scalacOptions += "-Xfatal-warnings",
    publish / skip := true,
    packagedArtifacts := Map(),
    dependencyOverrides ++= dependencyConflictResolutions )

lazy val releaseDist = TaskKey[File]( "release-dist", "Creates the release tar ball." )

lazy val evalUserManual = TaskKey[Unit]( "eval-user-manual", "Evaluates the snippets in the user manual." )

lazy val scripts = TaskKey[Unit]( "scripts", "Creates scripts in target/" )

def recursiveListFiles( f: File ): Seq[File] =
  if ( f.getName == "target" )
    Seq()
  else if ( f.isDirectory )
    IO.listFiles( f ).flatMap( recursiveListFiles )
  else
    Seq( f )

