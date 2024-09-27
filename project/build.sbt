resolvers += Classpaths.sbtPluginReleases
logLevel := Level.Warn

libraryDependencies += "org.apache.commons" % "commons-compress" % "1.21"

addSbtPlugin("org.scoverage" %% "sbt-scoverage" % "2.0.9")

// Provides an assembly task which produces a fat jar with all dependencies included.
addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "1.2.0")

addSbtPlugin("com.github.sbt" % "sbt-unidoc" % "0.5.0")

addSbtPlugin("org.xerial.sbt" % "sbt-sonatype" % "3.9.13")

addSbtPlugin("com.github.sbt" % "sbt-pgp" % "2.1.2")

addSbtPlugin("org.scalameta" % "sbt-scalafmt" % "2.5.2")
