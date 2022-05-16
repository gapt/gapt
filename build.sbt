import java.io.ByteArrayOutputStream

import org.apache.commons.compress.archivers.tar.{ TarArchiveEntry, TarArchiveOutputStream }
import scalariform.formatter.preferences._
import sys.process._

val Version = "2.15.3"

lazy val commonSettings = Seq(
  organization := "at.logic.gapt",
  homepage := Some( url( "https://logic.at/gapt/" ) ),
  organizationHomepage := homepage.value,
  licenses += ( "GPL-3.0" -> url( "http://www.gnu.org/licenses/gpl-3.0.html" ) ),
  startYear := Some( 2008 ),
  version := Version,
  autoAPIMappings := true,

  scmInfo := Some( ScmInfo(
    browseUrl = url( "https://github.com/gapt/gapt" ),
    connection = "scm:git:https://github.com/gapt/gapt.git",
    devConnection = Some( "scm:git:git@github.com:gapt/gapt.git" ) ) ),
  bintrayOrganization := Some( "gapt" ),

  scalaVersion := "2.13.0",
  scalacOptions in Compile ++= Seq(
    "-deprecation",
    "-language:postfixOps",
    "-language:implicitConversions",
    "-feature",
    "-unchecked" ),

  javaOptions ++= Seq( "-Xss40m", "-Xmx1g" ),
  fork := true,
  baseDirectory in run := file( "." ),

  sourcesInBase := false // people like to keep scripts lying around
) ++ scalariformSettings

lazy val scalariformSettings =
  Seq( scalariformPreferences := scalariformPreferences.value
    .setPreference( AlignParameters, true )
    .setPreference( AlignSingleLineCaseStatements, true )
    .setPreference( DoubleIndentConstructorArguments, true )
    .setPreference( SpaceInsideParentheses, true ) )

val specs2Version = "4.7.1"
lazy val testSettings = Seq(
  testOptions in Test += Tests.Argument( TestFrameworks.Specs2, "junitxml", "console" ),
  javaOptions in Test += "-Xmx2g",
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
    fork in console := true,
    initialCommands in console := IO.read( resourceDirectory.in( cli, Compile ).value / "gapt-cli-prelude.scala" ),

    bintrayReleaseOnPublish := false,
    packagedArtifacts := Map(),

    inConfig( BuildSbtConfig )( SbtScalariform.configScalariformSettings ++ scalariformSettings ),
    sourceDirectories in ( BuildSbtConfig, scalariformFormat ) := Seq( baseDirectory.value ),
    includeFilter in ( BuildSbtConfig, scalariformFormat ) := ( "*.sbt": FileFilter ),

    apiURL := Some( url( "https://logic.at/gapt/api/" ) ),
    scalacOptions in ( ScalaUnidoc, unidoc ) ++= Seq(
      "-doc-title", "gapt",
      "-doc-version", version.value,
      "-doc-source-url", s"https://github.com/gapt/gapt/blob/${"git rev-parse HEAD" !!}/€{FILE_PATH}.scala",
      "-doc-root-content", ( baseDirectory.value / "doc" / "rootdoc.txt" ).getAbsolutePath,
      "-sourcepath", baseDirectory.value.getAbsolutePath,
      "-skip-packages", "ammonite:ammonite.ops",
      "-diagrams",
      "-implicits", "-implicits-show-all",
      "-skip-packages", "scala" ),

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
    mainClass in assembly := Some( "gapt.cli.CLIMain" ),
    aggregate in assembly := false,
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
    } )

lazy val core = project.in( file( "core" ) ).
  settings( commonSettings: _* ).
  settings(
    name := "gapt",
    description := "General Architecture for Proof Theory",

    scalacOptions in Compile += "-Xfatal-warnings",

    libraryDependencies ++= Seq(
      "org.scala-lang.modules" %% "scala-parallel-collections" % "0.2.0",
      "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2",
      "org.scala-lang" % "scala-reflect" % scalaVersion.value,
      "org.parboiled" %% "parboiled" % "2.1.8",
      "com.lihaoyi" %% "fastparse" % "2.1.3",
      "com.lihaoyi" %% "sourcecode" % "0.1.7",
      "org.typelevel" %% "cats-free" % "2.1.0",
      "org.scala-lang.modules" %% "scala-xml" % "1.2.0",
      "org.scala-lang.modules" %% "scala-parallel-collections" % "0.2.0",
      "org.apache.commons" % "commons-lang3" % "3.9",
      "com.lihaoyi" %% "ammonite-ops" % "2.0.4",
      "de.uni-freiburg.informatik.ultimate" % "smtinterpol" % "2.5",
      "com.github.scopt" %% "scopt" % "3.7.1",
      "org.ow2.sat4j" % "org.ow2.sat4j.core" % "2.3.5",
      "org.ow2.sat4j" % "org.ow2.sat4j.maxsat" % "2.3.5" ),

    // UI
    libraryDependencies ++= Seq(
      "org.scala-lang.modules" %% "scala-swing" % "2.1.1",
      "com.itextpdf" % "itextpdf" % "5.5.13.1",
      "org.scilab.forge" % "jlatexmath" % "1.0.7" ),

    // JSON serialization
    libraryDependencies += "org.json4s" %% "json4s-native" % "3.6.7",
    libraryDependencies ++= Seq(
      "io.circe" %% "circe-core",
      "io.circe" %% "circe-generic",
      "io.circe" %% "circe-parser",
      "io.circe" %% "circe-generic-extras" ).map( _ % "0.12.1" ) )

lazy val examples = project.in( file( "examples" ) ).
  dependsOn( core ).
  settings( commonSettings: _* ).
  settings(
    name := "gapt-examples",
    unmanagedSourceDirectories in Compile := Seq( baseDirectory.value ),
    resourceDirectory in Compile := baseDirectory.value,
    excludeFilter in ( Compile, unmanagedResources ) := {
      val target = ( baseDirectory.value / "target" ).getCanonicalPath
      new SimpleFileFilter( _.getCanonicalPath startsWith target )
    } || "*.scala" )

lazy val tests = project.in( file( "tests" ) ).
  dependsOn( core, examples ).
  settings( commonSettings: _* ).
  settings( testSettings: _* ).
  disablePlugins( JUnitXmlReportPlugin ).
  settings(
    testForkedParallel := true,
    bintrayReleaseOnPublish := false,
    packagedArtifacts := Map() )

lazy val userManual = project.in( file( "doc" ) ).
  dependsOn( cli ).
  settings( commonSettings: _* ).
  settings(
    unmanagedSourceDirectories in Compile := Seq( baseDirectory.value ),
    bintrayReleaseOnPublish := false,
    packagedArtifacts := Map() )

lazy val cli = project.in( file( "cli" ) ).
  dependsOn( core, examples ).
  settings( commonSettings: _* ).
  settings(
    mainClass := Some( "gapt.cli.CLIMain" ),
    scalacOptions in Compile += "-Xfatal-warnings",
    libraryDependencies ++= Seq(
      "org.scala-lang" % "scala-compiler" % scalaVersion.value ),
    bintrayReleaseOnPublish := false,
    packagedArtifacts := Map() )

addCommandAlias( "format", "; scalariformFormat ; buildsbt:scalariformFormat" )

lazy val testing = project.in( file( "testing" ) ).
  dependsOn( core, examples ).
  settings( commonSettings: _* ).
  settings(
    name := "gapt-testing",
    description := "gapt extended regression tests",
    scalacOptions in Compile += "-Xfatal-warnings",
    bintrayReleaseOnPublish := false,
    packagedArtifacts := Map() )

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

