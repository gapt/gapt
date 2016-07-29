package at.logic.gapt.utils

import better.files._

object withTempFile {
  def apply[T]( block: File => T ): T = {
    val tempFile = File.newTemporaryFile( "gapt-", ".tmp" )
    try block( tempFile ) finally tempFile.delete()
  }

  def fromString[T]( content: String )( block: File => T ): T =
    withTempFile { file =>
      file overwrite content
      block( file )
    }
}
