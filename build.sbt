import java.io.ByteArrayOutputStream

import org.apache.commons.compress.archivers.tar.{ TarArchiveEntry, TarArchiveOutputStream }
import com.typesafe.sbt.SbtScalariform._
import scalariform.formatter.preferences._

val Version = "2.2-SNAPSHOT"

lazy val commonSettings = Seq(
  organization := "at.logic.gapt",
  homepage := Some( url( "https://logic.at/gapt/" ) ),
  organizationHomepage := homepage.value,
  licenses += ( "GPL-3.0" -> url( "http://www.gnu.org/licenses/gpl-3.0.html" ) ),
  startYear := Some( 2008 ),
  version := Version,

  scmInfo := Some( ScmInfo(
    browseUrl = url( "https://github.com/gapt/gapt" ),
    connection = "scm:git:https://github.com/gapt/gapt.git",
    devConnection = Some( "scm:git:git@github.com:gapt/gapt.git" )
  ) ),

  scalaVersion := "2.11.8",
  scalacOptions in Compile ++= Seq(
    "-deprecation",
    "-language:postfixOps",
    "-language:implicitConversions",
    "-feature",
    "-unchecked"
  ),

  // scalaz-stream is not on maven.org
  resolvers += "Scalaz Bintray Repo" at "http://dl.bintray.com/scalaz/releases",

  javaOptions ++= Seq( "-Xss40m", "-Xmx1g" ),
  fork := true,
  baseDirectory in run := file( "." ),

  sourcesInBase := false // people like to keep scripts lying around

) ++ publishSettings ++ defaultScalariformSettings :+
  ( ScalariformKeys.preferences := ScalariformKeys.preferences.value
    .setPreference( AlignParameters, true )
    .setPreference( AlignSingleLineCaseStatements, true )
    .setPreference( DoubleIndentClassDeclaration, true )
    .setPreference( SpaceInsideParentheses, true ) )

val specs2Version = "3.8.3"
lazy val testSettings = Seq(
  testOptions in Test += Tests.Argument( TestFrameworks.Specs2, "junitxml", "console" ),
  libraryDependencies ++= Seq(
    "org.specs2" %% "specs2-core" % specs2Version,
    "org.specs2" %% "specs2-junit" % specs2Version, // needed for junitxml output
    "org.specs2" %% "specs2-matcher" % specs2Version
  ) map ( _ % Test )
)

lazy val publishSettings =
  if ( Version endsWith "-SNAPSHOT" ) {
    Seq(
      bintrayReleaseOnPublish := false,
      publishTo := Some( "Artifactory Realm" at "http://oss.jfrog.org/artifactory/oss-snapshot-local/" ),
      credentials := {
        Credentials.loadCredentials( bintrayCredentialsFile.value ) match {
          case Right( bintrayCreds ) =>
            Seq( Credentials( "Artifactory Realm", "oss.jfrog.org", bintrayCreds.userName, bintrayCreds.passwd ) )
          case Left( error ) => Seq()
        }
      }
    )
  } else {
    Seq( bintrayOrganization := Some( "gapt" ) )
  }

lazy val BuildSbtConfig = config( "buildsbt" ) extend Compile

lazy val root = project.in( file( "." ) ).
  aggregate( core, examples, tests, userManual, cli, testing ).
  dependsOn( core, examples, cli ).
  settings( commonSettings: _* ).
  settings( unidocSettings: _* ).
  settings(
    fork in console := true,
    initialCommands in console := IO.read( resourceDirectory.in( cli, Compile ).value / "gapt-cli-prelude.scala" ),

    bintrayReleaseOnPublish := false,
    packagedArtifacts := Map(),

    inConfig( BuildSbtConfig )( configScalariformSettings ++ commonSettings ),
    sourceDirectories in ( BuildSbtConfig, scalariformFormat ) := Seq( baseDirectory.value ),
    includeFilter in ( BuildSbtConfig, scalariformFormat ) := ( "*.sbt": FileFilter ),

    apiURL := Some( url( "https://logic.at/gapt/api/" ) ),
    autoAPIMappings := true,
    scalacOptions in ( ScalaUnidoc, UnidocKeys.unidoc ) ++= Seq(
      "-doc-title", "gapt",
      "-doc-version", version.value,
      "-doc-source-url", s"https://github.com/gapt/gapt/blob/${"git rev-parse HEAD" !!}/€{FILE_PATH}.scala",
      "-sourcepath", baseDirectory.value.getAbsolutePath,
      "-diagrams",
      "-implicits", "-implicits-show-all",
      "-skip-packages", "scala"
    ),

    scripts := {
      val runJVMOptions = javaOptions.value ++ Seq( "-cp", Path.makeString(
        Attributed.data( fullClasspath.in( cli, Compile ).value )
      ) )
      def mkScript( file: File, extraArgs: String* ) = {
        IO.write(
          file,
          s"#!/bin/sh\njava ${( runJVMOptions ++ extraArgs ).mkString( " " )} ${"\"$@\""}\n"
        )
        file.setExecutable( true )
      }
      (
        mkScript( target.value / "run" ),
        mkScript( target.value / "viper", "at.logic.gapt.provers.viper.Viper" ),
        mkScript( target.value / "escargot", "at.logic.gapt.provers.escargot.Escargot" ),
        mkScript( target.value / "cli", "at.logic.gapt.cli.CLIMain" )
      )
    },

    // Release stuff
    aggregate in assembly := false,
    releaseDist := {
      val baseDir = file( "." )
      val version = Keys.version.value
      val apidocs = doc.in( ScalaUnidoc, UnidocKeys.unidoc ).value

      val archiveFile = file( "." ) / "target" / s"gapt-$version.tar.gz"

      Process( List( "latexmk", "-pdf", "user_manual.tex" ), baseDir / "doc" ) !

      val filesToIncludeAsIs = List(
        "COPYING", "gapt.sh", "include.sh", "examples"
      )
      val entries = List( ( assembly.value, s"gapt-$version.jar" ) ) ++
        filesToIncludeAsIs.flatMap { fn => recursiveListFiles( baseDir / fn ) }
        .map { f => ( f, baseDir.toPath.relativize( f.toPath ) ) } ++
        List(
          ( baseDir / "doc/README.dist", "README" ),
          ( baseDir / "doc/user_manual.pdf", "user_manual.pdf" )
        ) ++
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
      val exitVal = new Fork( "java", Some( "at.logic.gapt.testing.evalCodeSnippetsInLatex" ) ).fork(
        ForkOptions(
          outputStrategy = Some( CustomOutput( out ) ),
          workingDirectory = Some( file( "." ) ),
          javaHome = javaHome.value,
          runJVMOptions = javaOptions.value ++ Seq( "-cp", Path.makeString(
            Attributed.data( fullClasspath.in( userManual, Compile ).value )
          ) ),
          connectInput = false
        ),
        Seq( userManFn )
      ).exitValue()
      if ( exitVal == 0 ) IO.write( file( userManFn ), out.toByteArray )
    }
  )

lazy val core = project.in( file( "core" ) ).
  settings( commonSettings: _* ).
  settings(
    name := "gapt",
    description := "General Architecture for Proof Theory",

    libraryDependencies ++= Seq(
      "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.4",
      "org.scala-lang" % "scala-reflect" % scalaVersion.value,
      "org.parboiled" %% "parboiled" % "2.1.3",
      "com.lihaoyi" %% "fastparse" % "0.3.7",
      "com.googlecode.kiama" %% "kiama" % "1.8.0",
      "com.lihaoyi" %% "sourcecode" % "0.1.1",
      "org.scalaz" %% "scalaz-core" % "7.2.3",
      "org.scala-lang.modules" %% "scala-xml" % "1.0.5",
      "org.apache.commons" % "commons-lang3" % "3.4",
      "org.slf4j" % "slf4j-api" % "1.7.21",
      "org.slf4j" % "slf4j-log4j12" % "1.7.21",
      "org.ow2.sat4j" % "org.ow2.sat4j.core" % "2.3.5",
      "org.ow2.sat4j" % "org.ow2.sat4j.maxsat" % "2.3.5"
    ),

    // UI
    libraryDependencies ++= Seq(
      "org.scala-lang.modules" %% "scala-swing" % "2.0.0-M2",
      "com.itextpdf" % "itextpdf" % "5.5.9",
      "org.scilab.forge" % "jlatexmath" % "1.0.2"
    )
  )

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
    } || "*.scala",
    sourceDirectories in ( Compile, scalariformFormat ) := unmanagedSourceDirectories.in( Compile ).value
  )

lazy val tests = project.in( file( "tests" ) ).
  dependsOn( core, examples ).
  settings( commonSettings: _* ).
  settings( testSettings: _* ).
  disablePlugins( JUnitXmlReportPlugin ).
  settings(
    testForkedParallel := true,
    bintrayReleaseOnPublish := false,
    packagedArtifacts := Map()
  )

lazy val userManual = project.in( file( "doc" ) ).
  dependsOn( cli ).
  settings( commonSettings: _* ).
  settings(
    unmanagedSourceDirectories in Compile := Seq( baseDirectory.value ),
    sourceDirectories in ( Compile, scalariformFormat ) := unmanagedSourceDirectories.in( Compile ).value,
    bintrayReleaseOnPublish := false,
    packagedArtifacts := Map()
  )

lazy val cli = project.in( file( "cli" ) ).
  dependsOn( core, examples ).
  settings( commonSettings: _* ).
  settings(
    mainClass := Some( "at.logic.cli.CLIMain" ),

    libraryDependencies ++= Seq(
      "org.scala-lang" % "scala-compiler" % scalaVersion.value
    ),

    bintrayReleaseOnPublish := false,
    packagedArtifacts := Map()
  )

addCommandAlias( "format", "; scalariformFormat ; test:scalariformFormat ; buildsbt:scalariformFormat" )

lazy val testing = project.in( file( "testing" ) ).
  dependsOn( core, examples ).
  settings( commonSettings: _* ).
  settings(
    name := "gapt-testing",
    description := "gapt extended regression tests",

    bintrayReleaseOnPublish := false,
    packagedArtifacts := Map(),

    libraryDependencies += "org.json4s" %% "json4s-native" % "3.3.0"
  )

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

