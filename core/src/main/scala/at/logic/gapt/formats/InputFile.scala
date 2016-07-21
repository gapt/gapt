package at.logic.gapt.formats

import java.io.File

trait InputFile {
  def read: String
  def fileName: String
}
object InputFile {
  implicit def fromFileName( fileName: String ): OnDiskInputFile = OnDiskInputFile( fileName )
  def fromString( content: String ) = StringInputFile( content )
  implicit def fromFile( file: File ): OnDiskInputFile = OnDiskInputFile( file.getAbsolutePath )
}
case class StringInputFile( content: String ) extends InputFile {
  def fileName = "<string>"
  def read = content
}
case class OnDiskInputFile( fileName: String ) extends InputFile {
  def read = io.Source.fromFile( fileName ).mkString
}
