resolvers += Classpaths.sbtPluginReleases

libraryDependencies += "org.apache.commons" % "commons-compress" % "1.9"

addSbtPlugin("org.scoverage" %% "sbt-scoverage" % "1.0.4")

addSbtPlugin("org.scoverage" % "sbt-coveralls" % "1.0.0.BETA1")
