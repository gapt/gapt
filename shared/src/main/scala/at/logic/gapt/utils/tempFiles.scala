package at.logic.gapt.utils

import java.io.{ FileWriter, File }

object withTempFile {
  def apply[T]( block: String => T ): T = {
    val tempFile = File.createTempFile( "gapt-", ".tmp" )
    tempFile.deleteOnExit()
    try block( tempFile getAbsolutePath ) finally tempFile.delete()
  }

  def fromString[T]( content: String )( block: String => T ): T =
    withTempFile { fileName =>
      val w = new FileWriter( fileName )
      try w.write( content ) finally w.close()
      block( fileName )
    }
}
