name := "gapt"
description := "General Architecture for Proofs"
organization := "at.logic.gapt"
organizationHomepage := Some(url("https://code.google.com/p/gapt/"))
licenses +=("GNU GPL v3", url("http://www.gnu.org/licenses/gpl.html"))
startYear := Some(2008)
version := "1.9"

// Build config
scalaVersion := "2.11.4"
mainClass := Some("at.logic.cli.CLIMain")
test in assembly := {} // don't execute test when assembling jar

// Start each test class in a separate JVM, otherwise resolutionSchemaParserTest and nTapeTest fail.
{
  def oneJvmPerTest(tests: Seq[TestDefinition]) =
    tests map { test =>
      new Tests.Group(
        name = test.name,
        tests = Seq(test),
        runPolicy = Tests.SubProcess(ForkOptions()))
    }
  testGrouping in Test <<= definedTests in Test map oneJvmPerTest
}

// Dependencies

libraryDependencies ++= Seq(
  "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.2",
  "org.scala-lang.modules" %% "scala-xml" % "1.0.2",
  "org.apache.commons" % "commons-lang3" % "3.0",
  "org.slf4j" % "slf4j-api" % "1.6.6",
  "org.slf4j" % "slf4j-log4j12" % "1.6.6")

// UI
libraryDependencies ++= Seq(
  "org.scala-lang" % "scala-compiler" % scalaVersion.value,
  "jline" % "jline" % "2.12",
  "org.scala-lang.modules" %% "scala-swing" % "1.0.1",
  "org.jgrapht" % "jgrapht-jdk1.5" % "0.7.3",
  "com.itextpdf" % "itextpdf" % "5.1.3",
  "org.scilab.forge" % "jlatexmath" % "1.0.2")

// Tests
libraryDependencies ++= Seq(
  "junit" % "junit" % "4.10",
  "org.specs2" %% "specs2-core" % "2.4.12",
  "org.specs2" %% "specs2-matcher" % "2.4.12",
  "org.specs2" %% "specs2-mock" % "2.4.12",
  "org.specs2" %% "specs2-junit" % "2.4.12",
  "org.scalacheck" %% "scalacheck" % "1.11.6") map(_ % Test)
