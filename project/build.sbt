resolvers += Classpaths.sbtPluginReleases
logLevel := Level.Warn

libraryDependencies += "org.apache.commons" % "commons-compress" % "1.10"

addSbtPlugin("org.scoverage" %% "sbt-scoverage" % "1.0.4")  // coveralls doesn't work with 1.1.0
addSbtPlugin("org.scoverage" % "sbt-coveralls" % "1.0.0")

// Provides an assembly task which produces a fat jar with all dependencies included.
addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "0.14.0")

addSbtPlugin("org.scalariform" % "sbt-scalariform" % "1.5.1")

addSbtPlugin("me.lessis" % "bintray-sbt" % "0.3.0")
