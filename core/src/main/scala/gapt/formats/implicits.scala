package gapt.formats

import ammonite.ops._

object implicits {
  implicit def stringToFile( s: String ): InputFile = OnDiskInputFile( Path( FilePath( s ), pwd ) )
}
