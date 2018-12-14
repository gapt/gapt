package gapt.formats

import java.io.InputStream

import ammonite.ops._

import scala.io.Codec
import scala.sys.process

trait InputFile {
  def read: String
  def fileName: String
}
object InputFile {
  implicit def fromPath( file: FilePath ): OnDiskInputFile = OnDiskInputFile( Path( file, pwd ) )
  def fromString( content: String ) = StringInputFile( content )
  implicit def fromJavaFile( file: java.io.File ): OnDiskInputFile = OnDiskInputFile( Path( file ) )
  implicit def fromInputStream( stream: java.io.InputStream ): InputFile =
    StringInputFile( readStream( stream ) )
  implicit def fromFileName( fileName: String ): InputFile = fromPath( FilePath( fileName ) )

  def readStream( stream: InputStream ): String =
    scala.io.Source.fromInputStream( stream )( Codec.UTF8 ).mkString
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
  def apply(): StdinInputFile = StdinInputFile( InputFile.readStream( process.stdin ) )
}

case class ClasspathInputFile( fileName: String, classLoader: ClassLoader ) extends InputFile {
  def read = InputFile.readStream( classLoader.getResourceAsStream( fileName ) )
}
object ClasspathInputFile {
  def apply( fileName: String ): ClasspathInputFile =
    ClasspathInputFile( fileName, Thread.currentThread.getContextClassLoader )
  def apply( fileName: String, relativeToClass: Class[_] ): ClasspathInputFile =
    ClasspathInputFile( fileName, relativeToClass.getClassLoader )
}
