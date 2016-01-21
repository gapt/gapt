import java.io.ByteArrayOutputStream

import org.apache.commons.compress.archivers.tar.{TarArchiveEntry, TarArchiveOutputStream}
import com.typesafe.sbt.SbtScalariform._
import scalariform.formatter.preferences._

val Version = "2.1-SNAPSHOT"

lazy val commonSettings = Seq(
  organization := "at.logic.gapt",
  homepage := Some(url("https://logic.at/gapt/")),
  organizationHomepage := homepage.value,
  licenses += ("GPL-3.0" -> url("http://www.gnu.org/licenses/gpl-3.0.html")),
  startYear := Some(2008),
  version := Version,

  scmInfo := Some(ScmInfo(
    browseUrl = url("https://github.com/gapt/gapt"),
    connection = "scm:git:https://github.com/gapt/gapt.git",
    devConnection = Some("scm:git:git@github.com:gapt/gapt.git")
  )),

  scalaVersion := "2.11.7",
  scalacOptions in Compile ++= Seq("-deprecation", "-language:postfixOps", "-language:implicitConversions", "-feature"),
  testOptions in Test += Tests.Argument(TestFrameworks.Specs2, "junitxml", "console"),
  libraryDependencies ++= testDependencies map(_ % Test),

  // scalaz-stream is not on maven.org
  resolvers += "Scalaz Bintray Repo" at "http://dl.bintray.com/scalaz/releases",

  javaOptions ++= Seq("-Xss40m", "-Xmx1g"),
  fork := true,
//  fork in Test := true,

  sourcesInBase := false // people like to keep scripts lying around

) ++ defaultScalariformSettings :+
  (ScalariformKeys.preferences := ScalariformKeys.preferences.value
    .setPreference(AlignParameters, true)
    .setPreference(AlignSingleLineCaseStatements, true)
    .setPreference(DoubleIndentClassDeclaration, true)
    .setPreference(SpaceInsideParentheses, true))

lazy val publishSettings =
  if (Version endsWith "-SNAPSHOT") {
    Seq(
      bintrayReleaseOnPublish := false,
      publishTo := Some("Artifactory Realm" at "http://oss.jfrog.org/artifactory/oss-snapshot-local/"),
      credentials := {
        Credentials.loadCredentials(bintrayCredentialsFile.value) match {
          case Right(bintrayCreds) =>
            Seq(Credentials("Artifactory Realm", "oss.jfrog.org", bintrayCreds.userName, bintrayCreds.passwd))
          case Left(error) => Seq()
        }
      }
    )
  } else {
    Seq(bintrayOrganization := Some("gapt"))
  }

lazy val root = (project in file(".")).
  settings(commonSettings: _*).
  settings(publishSettings: _*).
  disablePlugins(JUnitXmlReportPlugin).
  settings(
    name := "gapt",
    description := "General Architecture for Proofs",

    scalacOptions in (Compile, doc) ++= Seq(
      "-doc-title", "gapt",
      "-doc-version", version.value,
      "-doc-source-url", s"https://github.com/gapt/gapt/blob/${"git rev-parse HEAD" !!}/€{FILE_PATH}.scala",
      "-sourcepath", baseDirectory.value.getAbsolutePath,
      "-diagrams",
      "-implicits"
    ),

    mainClass := Some("at.logic.cli.CLIMain"),

    fork in console := true,
    initialCommands in console := IO.read((resourceDirectory in Compile).value / "gapt-cli-prelude.scala"),

    unmanagedSourceDirectories in Compile += baseDirectory.value / "examples",
    sourceDirectories in (Compile, scalariformFormat) += baseDirectory.value / "examples",

    // Release stuff
    test in assembly := {}, // don't execute test when assembling jar
    releaseDist := {
      val baseDir = baseDirectory.value
      val version = Keys.version.value
      val apidocs = (doc in Compile).value

      val archiveFile = target.value / s"gapt-$version.tar.gz"

      Process(List("latexmk", "-pdf", "user_manual.tex"), baseDir / "doc") !

      val filesToIncludeAsIs = List(
        "COPYING", "gapt.sh", "include.sh", "examples")
      val entries = List((assembly.value, s"gapt-$version.jar")) ++
        filesToIncludeAsIs.flatMap{fn => recursiveListFiles(baseDir / fn)}
          .map{f => (f, baseDir.toPath.relativize(f.toPath))} ++
        List((baseDir / "doc/README.dist", "README"),
             (baseDir / "doc/user_manual.pdf", "user_manual.pdf")) ++
          recursiveListFiles(apidocs).map{f => f -> s"apidocs/${apidocs.toPath.relativize(f.toPath)}"}

      val archiveStem = s"gapt-$version"

      IO.gzipFileOut(archiveFile) { gzipOut =>
        val tarOut = new TarArchiveOutputStream(gzipOut)
        tarOut.setLongFileMode(TarArchiveOutputStream.LONGFILE_POSIX)

        entries.foreach { case (file, pathInArchive) =>
          val tarEntry = new TarArchiveEntry(file, s"$archiveStem/$pathInArchive")
          if (file.canExecute) tarEntry.setMode(BigInt("755", 8).toInt)
          tarOut.putArchiveEntry(tarEntry)
          IO.transfer(file, tarOut)
          tarOut.closeArchiveEntry()
        }

        tarOut.close()
      }

      archiveFile
    },

    evalUserManual := {
      val userManFn = "doc/user_manual.tex"
      val out = new ByteArrayOutputStream
      val exitVal = new Fork("java", Some("at.logic.gapt.testing.evalCodeSnippetsInLatex")).fork(ForkOptions(
        outputStrategy = Some(CustomOutput(out)),
        workingDirectory = Some(file(".")),
        javaHome = javaHome.value,
        runJVMOptions = javaOptions.value ++ Seq("-cp", Path.makeString(Attributed.data((fullClasspath in Test).value))),
        connectInput = false),
        Seq(userManFn)).exitValue()
      if (exitVal == 0) IO.write(file(userManFn), out.toByteArray)
    },

    testForkedParallel in Test := true,

    libraryDependencies ++= Seq(
      "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.4",
      "org.parboiled" %% "parboiled" % "2.1.0",
      "org.scalaz" %% "scalaz-core" % "7.2.0",
      "org.scala-lang.modules" %% "scala-xml" % "1.0.5",
      "org.apache.commons" % "commons-lang3" % "3.4",
      "org.slf4j" % "slf4j-api" % "1.7.13",
      "org.slf4j" % "slf4j-log4j12" % "1.7.13",
      "xml-resolver" % "xml-resolver" % "1.2",
      "org.ow2.sat4j" % "org.ow2.sat4j.core" % "2.3.5",
      "org.ow2.sat4j" % "org.ow2.sat4j.maxsat" % "2.3.5"),

    // UI
    libraryDependencies ++= Seq(
      "org.scala-lang" % "scala-compiler" % scalaVersion.value,
      "jline" % "jline" % "2.13",
      "org.scala-lang.modules" %% "scala-swing" % "2.0.0-M2",
      "com.itextpdf" % "itextpdf" % "5.5.8",
      "org.scilab.forge" % "jlatexmath" % "1.0.2")
  )

addCommandAlias("format", "; scalariformFormat ; test:scalariformFormat ; testing/scalariformFormat ; testing/test:scalariformFormat")

lazy val testing = (project in file("testing")).
  dependsOn(root).
  settings(commonSettings: _*).
  disablePlugins(JUnitXmlReportPlugin).
  settings(
    name := "gapt-testing",
    description := "gapt extended regression tests",

    libraryDependencies += "org.json4s" %% "json4s-native" % "3.2.11",

    baseDirectory in run := file(".")
  )

lazy val releaseDist = TaskKey[File]("release-dist", "Creates the release tar ball.")

lazy val evalUserManual = TaskKey[Unit]("eval-user-manual", "Evaluates the snippets in the user manual.")

lazy val testDependencies = Seq(
  "org.specs2" %% "specs2-core" % "3.7",
  "org.specs2" %% "specs2-junit" % "3.7",  // needed for junitxml output
  "org.specs2" %% "specs2-matcher" % "3.7")

def recursiveListFiles(f: File): Seq[File] =
  if (f.isDirectory)
    IO.listFiles(f).flatMap(recursiveListFiles)
  else
    Seq(f)

