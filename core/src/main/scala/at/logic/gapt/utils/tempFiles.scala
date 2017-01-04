package at.logic.gapt.utils

import ammonite.ops._

object withTempFile {
  def apply[T]( block: Path => T ): T = {
    val tempFile = tmp( prefix = "gapt-" )
    try block( tempFile ) finally rm ! tempFile
  }

  def fromString[T]( content: String )( block: Path => T ): T =
    withTempFile { file =>
      write.over( file, content )
      block( file )
    }
}
