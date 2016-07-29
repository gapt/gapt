package at.logic.gapt.formats

import better.files._

trait InputFile {
  def read: String
  def fileName: String
}
object InputFile {
  implicit def fromFileName( fileName: String ): OnDiskInputFile = OnDiskInputFile( fileName.toFile )
  implicit def fromFile( file: File ): OnDiskInputFile = OnDiskInputFile( file )
  def fromString( content: String ) = StringInputFile( content )
  implicit def fromJavaFile( file: java.io.File ): OnDiskInputFile = OnDiskInputFile( file.toScala )
  implicit def fromInputStream( stream: java.io.InputStream ): InputFile =
    StringInputFile( stream.content.mkString )
}
case class StringInputFile( content: String ) extends InputFile {
  def fileName = "<string>"
  def read = content
}
case class OnDiskInputFile( file: File ) extends InputFile {
  def fileName = file.pathAsString
  def read = file.contentAsString
}
