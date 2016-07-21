package at.logic.gapt.formats
import language.existentials

case class ClasspathInputFile( fileName: String, clazz: Class[_] = classOf[ClasspathInputFile] ) extends InputFile {

  def read = io.Source.fromInputStream( clazz.getClassLoader.getResourceAsStream( fileName ) ).mkString

}
