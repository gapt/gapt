package at.logic.gapt.formats
import language.existentials

import better.files._

case class ClasspathInputFile( fileName: String, clazz: Class[_] = classOf[ClasspathInputFile] ) extends InputFile {

  def read = clazz.getClassLoader.getResourceAsStream( fileName ).content.mkString

}
