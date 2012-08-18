import sbt._

class BuildProject(info: ProjectInfo) extends DefaultProject(info) {

val mavenLocal = "Local Maven Repository" at
"file://"+Path.userHome+"/.m2/repository"

override def outputPath = "target"


}
