package gapt.utils

import os._

object withTempFile {
  def apply[T]( block: Path => T ): T = {
    val tempFile = temp( prefix = "gapt-" )
    try block( tempFile ) finally remove(tempFile)
  }

  def fromString[T]( content: String )( block: Path => T ): T =
    withTempFile { file =>
      write.over( file, content )
      block( file )
    }
}
