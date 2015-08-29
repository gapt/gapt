import org.apache.commons.compress.archivers.tar.{TarArchiveEntry, TarArchiveOutputStream}
import scalariform.formatter.preferences._

lazy val commonSettings = Seq(
  organization := "at.logic.gapt",
  organizationHomepage := Some(url("https://gapt.github.io/")),
  licenses += ("GNU GPL v3", url("http://www.gnu.org/licenses/gpl.html")),
  startYear := Some(2008),
  version := "1.10-SNAPSHOT",

  scalaVersion := "2.11.7",
  scalacOptions in (Compile, doc) ++= Seq("-diagrams","-implicits"),
  testOptions in Test += Tests.Argument(TestFrameworks.Specs2, "junitxml", "console"),
  libraryDependencies ++= testDependencies map(_ % Test),

  // scalaz-stream is not on maven.org
  resolvers += "Scalaz Bintray Repo" at "http://dl.bintray.com/scalaz/releases",

  sourcesInBase := false // people like to keep scripts lying around

) ++ defaultScalariformSettings :+
  (ScalariformKeys.preferences := ScalariformKeys.preferences.value
    .setPreference(AlignParameters, true)
    .setPreference(AlignSingleLineCaseStatements, true)
    .setPreference(DoubleIndentClassDeclaration, true)
    .setPreference(SpaceInsideParentheses, true))

lazy val root = (project in file(".")).
  settings(commonSettings: _*).
  disablePlugins(JUnitXmlReportPlugin).
  settings(
    name := "gapt",
    description := "General Architecture for Proofs",

    mainClass := Some("at.logic.cli.CLIMain"),

    sourceGenerators in Compile += Def.task {
      Seq("ProofSequences.scala", "FormulaSequences.scala") map { fn =>
        val dest = (sourceManaged in Compile).value / fn
        IO.copyFile(baseDirectory.value / "examples" / fn, dest)
        dest
      }
    }.taskValue,

    // Release stuff
    test in assembly := {}, // don't execute test when assembling jar
    releaseDist := {
      val baseDir = baseDirectory.value
      val version = Keys.version.value
      val apidocs = (doc in Compile).value

      val archiveFile = target.value / s"gapt-$version.tar.gz"

      Process(List("latexmk", "-pdf", "user_manual.tex"), baseDir / "doc") !

      val filesToIncludeAsIs = List(
        "COPYING", "cli.sh", "gui.sh", "atp.sh", "include.sh", "examples")
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

    javaOptions in Test += "-Xss20m",
    fork in Test := true,
    testForkedParallel in Test := true,

    libraryDependencies ++= Seq(
      "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.4",
      "org.scala-lang.modules" %% "scala-xml" % "1.0.5",
      "org.apache.commons" % "commons-lang3" % "3.4",
      "org.slf4j" % "slf4j-api" % "1.7.12",
      "org.slf4j" % "slf4j-log4j12" % "1.7.12",
      "xml-resolver" % "xml-resolver" % "1.2",
      "org.ow2.sat4j" % "org.ow2.sat4j.core" % "2.3.5",
      "org.ow2.sat4j" % "org.ow2.sat4j.maxsat" % "2.3.5"),

    // UI
    libraryDependencies ++= Seq(
      "org.scala-lang" % "scala-compiler" % scalaVersion.value,
      "jline" % "jline" % "2.13",
      "org.scala-lang.modules" %% "scala-swing" % "2.0.0-M2",
      "com.itextpdf" % "itextpdf" % "5.5.6",
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

    baseDirectory in run := file("."),
    javaOptions ++= Seq("-Xmx2g", "-Xss20m"),
    fork := true
  )

lazy val releaseDist = TaskKey[File]("release-dist", "Creates the release tar ball.")

lazy val testDependencies = Seq(
  "org.specs2" %% "specs2-core" % "3.6.4",
  "org.specs2" %% "specs2-junit" % "3.6.4",  // needed for junitxml output
  "org.specs2" %% "specs2-matcher" % "3.6.4")

def oneJvmPerTest(tests: Seq[TestDefinition]) =
  tests map { test =>
    new Tests.Group(
      name = test.name,
      tests = Seq(test),
      runPolicy = Tests.SubProcess(ForkOptions()))
  }

def recursiveListFiles(f: File): List[File] =
  if (f.isDirectory)
    IO.listFiles(f).toList.flatMap(recursiveListFiles)
  else
    List(f)

