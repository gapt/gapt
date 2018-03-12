package gapt.formats

import ammonite.ops._

import scala.sys.process

trait InputFile {
  def read: String
  def fileName: String
}
object InputFile {
  @deprecated( "Disambiguate file names from strings by using FilePath(\"proof.s\")", since = "2.3" )
  implicit def fromFileName( fileName: String ): OnDiskInputFile = fromPath( FilePath( fileName ) )
  implicit def fromPath( file: FilePath ): OnDiskInputFile = OnDiskInputFile( Path( file, pwd ) )
  def fromString( content: String ) = StringInputFile( content )
  implicit def fromJavaFile( file: java.io.File ): OnDiskInputFile = OnDiskInputFile( Path( file ) )
  implicit def fromInputStream( stream: java.io.InputStream ): InputFile =
    StringInputFile( read ! stream )
}
case class StringInputFile( content: String ) extends InputFile {
  def fileName = "<string>"
  def read = content
}
case class OnDiskInputFile( file: Path ) extends InputFile {
  def fileName = file.toString
  def read = ammonite.ops.read ! file
}

case class StdinInputFile( content: String ) extends InputFile {
  def fileName = "<stdin>"
  def read = content
}
object StdinInputFile {
  def apply(): StdinInputFile = StdinInputFile( read( process.stdin ) )
}

case class ClasspathInputFile( fileName: String, classLoader: ClassLoader ) extends InputFile {
  def read = ammonite.ops.read ! classLoader.getResourceAsStream( fileName )
}
object ClasspathInputFile {
  def apply( fileName: String ): ClasspathInputFile =
    ClasspathInputFile( fileName, Thread.currentThread.getContextClassLoader )
  def apply( fileName: String, relativeToClass: Class[_] ): ClasspathInputFile =
    ClasspathInputFile( fileName, relativeToClass.getClassLoader )
}
