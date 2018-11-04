package gapt.formats

import ammonite.ops._

object implicits {
  implicit def stringToPath( s: String ): Path = Path( FilePath( s ), pwd )
}
