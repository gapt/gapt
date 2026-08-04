import geny.Readable.InputStreamReadable
import java.io.ByteArrayOutputStream

import org.apache.commons.compress.archivers.tar.{TarArchiveEntry, TarArchiveOutputStream}
import sys.process._
import xerial.sbt.Sonatype.sonatypeCentralHost

val Version = "2.20.0-SNAPSHOT"

Global / onChangedBuildSource := ReloadOnSourceChanges
Global / semanticdbEnabled := true
Global / semanticdbVersion := scalafixSemanticdb.revision
lazy val commonSettings = Seq(
  organization := "at.logic.gapt",
  homepage := Some(url("https://logic.at/gapt/")),
  organizationHomepage := homepage.value,
  licenses += ("GPL-3.0" -> url("http://www.gnu.org/licenses/gpl-3.0.html")),
  startYear := Some(2008),
  version := Version,
  autoAPIMappings := true,
  publishMavenStyle := true,
  publishTo := sonatypePublishToBundle.value,
  sonatypeCredentialHost := sonatypeCentralHost,
  sonatypeProfileName := "at.logic",
  scmInfo := Some(ScmInfo(
    browseUrl = url("https://github.com/gapt/gapt"),
    connection = "scm:git:https://github.com/gapt/gapt.git",
    devConnection = Some("scm:git:git@github.com:gapt/gapt.git")
  )),
  scalaVersion := "3.8.2",
  developers := List(
    Developer(
      id = "fachammer",
      name = "Fabian Achammer",
      email = "fabian@achammer.dev",
      url = url("https://fabian.achammer.dev")
    ),
    Developer(
      id = "jvierling",
      name = "Jannik Vierling",
      email = "jannik.vierling@gmail.com",
      url = url("https://jvierling.github.io/")
    ),
    Developer(
      id = "shetzl",
      name = "Stefan Hetzl",
      email = "stefan.hetzl@tuwien.ac.at",
      url = url("http://dmg.tuwien.ac.at/hetzl/")
    ),
    Developer(
      id = "gebner",
      name = "Gabriel Ebner",
      email = "gebner@gebner.org",
      url = url("https://gebner.org/")
    )
  ),
  Compile / scalacOptions ++= Seq(
    "-deprecation",
    "-language:postfixOps",
    "-language:implicitConversions",
    "-feature",
    "-unchecked",
    "-explain",
    "-Wunused:imports,privates,locals,implicits"
  ),
  javaOptions ++= Seq("-Xss40m", "-Xmx1g"),
  fork := true,
  run / baseDirectory := file("."),
  sourcesInBase := false // people like to keep scripts lying around

)

val specs2Version = "4.16.0"
lazy val testSettings = Seq(
  Test / testOptions +=
    Tests.Argument(TestFrameworks.Specs2, "junitxml", "console"),
  Test / javaOptions += "-Xmx2g",
  libraryDependencies ++= Seq(
    "org.specs2" %% "specs2-core" % specs2Version,
    "org.specs2" %% "specs2-junit" %
      specs2Version, // needed for junitxml output
    "org.specs2" %% "specs2-matcher" % specs2Version
  ).map(_ % Test)
)

lazy val BuildSbtConfig = config("buildsbt").extend(Compile)

lazy val root = project.in(file("."))
  .aggregate(core, examples, tests, userManual, cli, testing)
  .dependsOn(core, examples, cli).settings(commonSettings: _*)
  .enablePlugins(ScalaUnidocPlugin).settings(
    console / initialCommands := IO.read(
      (cli / Compile / resourceDirectory).value / "gapt-cli-prelude.scala"
    ),
    publish / skip := true,
    packagedArtifacts := Map(),
    apiURL := Some(url("https://logic.at/gapt/api/")),
    ScalaUnidoc / unidoc / scalacOptions ++= Seq(
      "-doc-title",
      "gapt",
      "-doc-version",
      version.value,
      "-doc-source-url",
      s"https://github.com/gapt/gapt/blob/${("git rev-parse HEAD" !!).strip}/€{FILE_PATH}.scala",
      "-doc-root-content",
      (baseDirectory.value / "doc" / "rootdoc.txt").getAbsolutePath,
      "-sourcepath",
      baseDirectory.value.getAbsolutePath,
      "-skip-by-id:ammonite:ammonite.ops:scala"
    ),
    dependencyOverrides ++= dependencyConflictResolutions,
    scripts := {
      val runJVMOptions = javaOptions.value ++ Seq(
        "-cp",
        Path.makeString(Attributed.data(
          (cli / Compile / fullClasspath).value ++
            (testing / Compile / fullClasspath).value distinct
        ))
      )
      def mkScript(file: File, extraArgs: String*) = {
        IO.write(
          file,
          s"#!/bin/sh\njava ${(runJVMOptions ++ extraArgs).mkString(" ")} ${"\"$@\""}\n"
        )
        file.setExecutable(true)
      }
      (
        mkScript(target.value / "run"),
        mkScript(target.value / "test-cut-intro", "gapt.testing.testCutIntro"),
        mkScript(
          target.value / "test-pi2-cut-intro",
          "gapt.testing.testPi2CutIntro"
        ),
        mkScript(target.value / "test-induction", "gapt.testing.testInduction"),
        mkScript(target.value / "viper", "gapt.provers.viper.Viper"),
        mkScript(target.value / "escargot", "gapt.provers.escargot.Escargot"),
        mkScript(target.value / "slakje", "gapt.provers.slakje.Slakje"),
        mkScript(target.value / "cli", "gapt.cli.CLIMain")
      )
    },

    // Release stuff
    assembly / mainClass := Some("gapt.cli.CLIMain"),
    assembly / aggregate := false,
    releaseDist := {
      val baseDir = file(".")
      val version = Keys.version.value
      val apidocs = (ScalaUnidoc / unidoc / doc).value

      val archiveFile = file(".") / "target" / s"gapt-$version.tar.gz"

      Process(
        List("latexmk", "-pdf", "-silent", "user_manual.tex"),
        baseDir / "doc"
      ) !

      val filesToIncludeAsIs = List(
        "COPYING",
        "gapt.sh",
        "slakje.sh",
        "escargot.sh",
        "viper.sh",
        "include.sh",
        "examples"
      )
      val entries = List((assembly.value, s"gapt-$version.jar")) ++
        filesToIncludeAsIs.flatMap { fn => recursiveListFiles(baseDir / fn) }
          .map { f => (f, baseDir.toPath.relativize(f.toPath)) } ++ List(
          (baseDir / "doc/README.dist", "README"),
          (baseDir / "doc/user_manual.pdf", "user_manual.pdf")
        ) ++ recursiveListFiles(apidocs).map { f =>
          f -> s"apidocs/${apidocs.toPath.relativize(f.toPath)}"
        }

      val archiveStem = s"gapt-$version"

      IO.gzipFileOut(archiveFile) { gzipOut =>
        val tarOut = new TarArchiveOutputStream(gzipOut)
        tarOut.setLongFileMode(TarArchiveOutputStream.LONGFILE_POSIX)

        entries.foreach {
          case (file, pathInArchive) =>
            val tarEntry =
              new TarArchiveEntry(file, s"$archiveStem/$pathInArchive")
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
      val exitVal = new Fork("java", Some("gapt.doc.evalCodeSnippets")).fork(
        ForkOptions(
          javaHome = javaHome.value,
          outputStrategy = Some(CustomOutput(out)),
          bootJars = Vector(),
          workingDirectory = Some(new java.io.File(".")),
          runJVMOptions = Vector() ++ javaOptions.value ++ Seq(
            "-cp",
            Path.makeString(
              Attributed.data((userManual / Compile / fullClasspath).value)
            )
          ),
          connectInput = false,
          envVars = envVars.value
        ),
        Seq(userManFn)
      ).exitValue()
      if (exitVal == 0) IO.write(file(userManFn), out.toByteArray)
      else
        throw new Exception(s"evalUserManual failed with exit code ${exitVal}")
    },
    prooVerDist := (cli / ProoVerCLI / prooVerDist).value
  )

val dependencyConflictResolutions = Seq("com.lihaoyi" %% "geny" % "1.0.0")

lazy val core = project.in(file("core")).settings(commonSettings: _*).settings(
  name := "gapt",
  description := "General Architecture for Proof Theory",
  libraryDependencies ++= Seq(
    "org.scala-lang.modules" %% "scala-parallel-collections" % "1.0.4",
    "org.scala-lang.modules" %% "scala-parser-combinators" % "2.1.1",
    "org.parboiled" %% "parboiled" % "2.4.0",
    "com.lihaoyi" %% "fastparse" % "3.0.2",
    "com.lihaoyi" %% "sourcecode" % "0.4.2",
    "org.typelevel" %% "cats-free" % "2.7.0",
    "org.scala-lang.modules" %% "scala-xml" % "2.1.0",
    "org.apache.commons" % "commons-lang3" % "3.12.0",
    "com.lihaoyi" %% "os-lib" % "0.9.3",
    "com.lihaoyi" %% "pprint" % "0.9.0",
    "de.uni-freiburg.informatik.ultimate" % "smtinterpol" % "2.5",
    "com.github.scopt" %% "scopt" % "4.0.1",
    "org.ow2.sat4j" % "org.ow2.sat4j.core" % "2.3.6",
    "org.ow2.sat4j" % "org.ow2.sat4j.maxsat" % "2.3.6"
  ),
  dependencyOverrides ++= dependencyConflictResolutions,
  // UI
  libraryDependencies ++= Seq(
    "org.scala-lang.modules" %% "scala-swing" % "3.0.0",
    "com.itextpdf" % "itextpdf" % "5.5.13.3",
    "org.scilab.forge" % "jlatexmath" % "1.0.7"
  ),

  // JSON serialization
  libraryDependencies += "org.json4s" %% "json4s-native" % "4.0.5",
  libraryDependencies ++= Seq(
    "io.circe" %% "circe-core",
    "io.circe" %% "circe-generic",
    "io.circe" %% "circe-parser"
  ).map(_ % "0.14.6")
)

lazy val examples = project.in(file("examples")).dependsOn(core)
  .settings(commonSettings: _*).settings(
    name := "gapt-examples",
    Compile / unmanagedSourceDirectories := Seq(baseDirectory.value),
    Compile / resourceDirectory := baseDirectory.value,
    Compile / unmanagedResources / excludeFilter := {
      val target = (baseDirectory.value / "target").getCanonicalPath
      new SimpleFileFilter(_.getCanonicalPath.startsWith(target))
    } || "*.scala",
    dependencyOverrides ++= dependencyConflictResolutions,
    Compile / run / connectInput := true,
    Compile / run / outputStrategy := Some(StdoutOutput)
  )

lazy val tests = project.in(file("tests")).dependsOn(core, examples)
  .settings(commonSettings: _*).settings(testSettings: _*)
  .disablePlugins(JUnitXmlReportPlugin).settings(
    testForkedParallel := true,
    publish / skip := true,
    packagedArtifacts := Map(),
    dependencyOverrides ++= dependencyConflictResolutions
  )

lazy val userManual = project.in(file("doc")).dependsOn(cli)
  .settings(commonSettings: _*).settings(
    Compile / unmanagedSourceDirectories := Seq(baseDirectory.value),
    publish / skip := true,
    packagedArtifacts := Map(),
    dependencyOverrides ++= dependencyConflictResolutions
  )

lazy val prooVerDistBaseDir = settingKey[File]("prooVerDistBaseDir")
lazy val prooVerDistOutDir = settingKey[File]("prooVerDistOutDir")
lazy val prooVerJarName = settingKey[String]("prooVerJarName")
lazy val prooVerAppName = settingKey[String]("prooVerAppName")
lazy val prooVerDistResources = settingKey[File]("prooVerDistResources")
lazy val prooVerZip = settingKey[File]("prooVerZip")

lazy val MainCLI = config("Main")
lazy val ProoVerCLI = config("ProoVerCLI")
lazy val cli = project.in(file("cli")).dependsOn(core, examples)
  .settings(commonSettings: _*)
  .settings(testSettings: _*)
  .configs(ProoVerCLI)
  .settings(
    inConfig(MainCLI)(baseAssemblySettings ++ Seq(
      assembly / mainClass := Some("gapt.cli.CLIMain")
    )),
    inConfig(ProoVerCLI)(baseAssemblySettings ++ Seq(
      assembly / mainClass := Some("gapt.cli.prooVerCLI"),
      assembly / assemblyOutputPath := target.value / "gapt-prooVer-cli.jar",
      Test / test := (Test / test).dependsOn(prooVerDistNoTest).value,
      prooVerDistBaseDir := file(".") / "target",
      prooVerDistOutDir := prooVerDistBaseDir.value / "ProoVer",
      prooVerZip := prooVerDistBaseDir.value / "gapt-ProoVer.zip",
      prooVerJarName := "gapt.jar",
      prooVerAppName := "gapt-check",
      prooVerDistResources := file(".") / "cli" / "ProoVer",
      prooVerDistNoTest := {
        val log = streams.value.log

        val jar = assembly.value
        val baseDir = prooVerDistBaseDir.value
        val out = prooVerDistOutDir.value
        val jarName = prooVerJarName.value
        val appName = prooVerAppName.value
        val distResources = prooVerDistResources.value
        val zip = prooVerZip.value

        IO.delete(out)
        IO.copyDirectory(distResources, out)
        IO.copyFile(jar, out / jarName)
        IO.write(
          out / appName,
          s"""|#!/usr/bin/env sh
              |DIR="$$(cd "$$(dirname "$$0")" && pwd)"
              |exec java -Xss128m -Xms4g -Xmx128g -jar "$$DIR/$jarName" "$$@"
        """.stripMargin.strip
        )
        (out / appName).setExecutable(true)

        log.info(s"Created ProoVer distribution folder: ${out.getAbsolutePath}")

        IO.delete(zip)
        zipDist(out, zip)

        log.info(s"Created zip: ${zip.getAbsolutePath}")

        zip
      },
      prooVerDist := {
        val log = streams.value.log
        val out = prooVerDistOutDir.value
        val zip = prooVerZip.value
        val appName = prooVerAppName.value

        IO.delete(out)

        val unzipDirectory = target.value / "smoke-ProoVer"
        IO.delete(unzipDirectory)

        log.info(s"Unzipping $zip to $unzipDirectory for smoke test")
        unzip(zip, unzipDirectory)

        assert(unzipDirectory.exists(), s"unzip directory $unzipDirectory does not exist")

        val unzipSamplesDirectory = unzipDirectory / "samples"
        log.info(s"Running smoke tests on $unzipDirectory")
        try {
          val sampleTestFiles = Seq("COR000+1", "EVL000+1", "TMO000+1")
          for (sampleTestFile <- sampleTestFiles) {
            val claimedSampleSolution = IO.read(unzipSamplesDirectory / "Solutions" / s"$sampleTestFile.out").strip()
            val output = Process(Seq(
              "sh",
              (unzipDirectory / appName).getAbsolutePath,
              (unzipSamplesDirectory / s"$sampleTestFile.s").getAbsolutePath
            )).!!.strip
            assert(output == claimedSampleSolution, s"""on sample file $sampleTestFile: output "$output" does not match expected output "$claimedSampleSolution"""")
          }
        } finally {
          IO.delete(unzipDirectory)
        }

        log.info(s"Smoke test successful")

        zip
      }
    )),
    Compile / scalacOptions += "-Werror",
    libraryDependencies ++= Seq(
      "org.scala-lang" %% "scala3-compiler" % scalaVersion.value,
      "org.scala-lang" %% "scala3-repl" % scalaVersion.value
    ),
    Compile / run / outputStrategy := Some(StdoutOutput),
    packagedArtifacts := Map(),
    publish / skip := true,
    dependencyOverrides ++= dependencyConflictResolutions
  )

addCommandAlias("format", "scalafmtAll; scalafmtSbt")
addCommandAlias("checkFormat", "scalafmtCheckAll; scalafmtSbtCheck")

lazy val testing = project.in(file("testing")).dependsOn(core, examples)
  .settings(commonSettings: _*).settings(
    name := "gapt-testing",
    description := "gapt extended regression tests",
    Compile / scalacOptions += "-Werror",
    publish / skip := true,
    packagedArtifacts := Map(),
    dependencyOverrides ++= dependencyConflictResolutions,
    run / fork := true,
    run / connectInput := true
  )

lazy val releaseDist =
  TaskKey[File]("release-dist", "Creates the release tar ball.")

lazy val evalUserManual = TaskKey[Unit](
  "eval-user-manual",
  "Evaluates the snippets in the user manual."
)

lazy val scripts = TaskKey[Unit]("scripts", "Creates scripts in target/")
lazy val prooVerDistNoTest = TaskKey[File]("prooVerDistNoTest", "Creates the zip archive for the prooVer competition without performing smoke tests")
lazy val prooVerDist = TaskKey[File]("prooVerDist", "Creates the zip archive for the prooVer competition and performs smoke tests")

def recursiveListFiles(f: File): Seq[File] =
  if (f.getName == "target") Seq()
  else if (f.isDirectory) IO.listFiles(f).flatMap(recursiveListFiles)
  else Seq(f)

def zipDist(sourceDir: File, zipFile: File): Unit = {
  import java.io._
  import java.nio.file.Files
  import org.apache.commons.compress.archivers.zip._
  val zos = new ZipArchiveOutputStream(zipFile)
  try {
    Path
      .allSubpaths(sourceDir)
      .foreach {
        case (file, relativePath) =>
          val entry = new ZipArchiveEntry(file, relativePath)

          if (file.isFile) {
            // preserve executable bit
            if (Files.isExecutable(file.toPath))
              entry.setUnixMode(0x1ed) // 0755

            zos.putArchiveEntry(entry)
            val in = new BufferedInputStream(new FileInputStream(file))
            try in.transferTo(zos)
            finally in.close()
            zos.closeArchiveEntry()
          }
      }
    zos.finish()
  } finally {
    zos.close()
  }
}

def unzip(zipFile: File, targetDir: File): Unit = {
  import java.io._
  import java.nio.file.Files
  import scala.collection.JavaConverters._
  import org.apache.commons.compress.archivers.zip._

  assert(!targetDir.exists(), s"target directory $targetDir already exists")
  IO.createDirectory(targetDir)

  val zip = new ZipFile(zipFile.file)
  try {
    zip.getEntries.asScala.foreach { entry =>
      val outFile = targetDir / entry.getName

      if (entry.isDirectory) {
        IO.createDirectory(outFile)
      } else {
        IO.createDirectory(outFile.getParentFile)
        val in = zip.getInputStream(entry)
        try {
          val out = new FileOutputStream(outFile)
          try {
            in.transferTo(out)
          } finally {
            out.close()
          }
        } finally {
          in.close()
        }
      }
    }
  } finally {
    zip.close()
  }
}
