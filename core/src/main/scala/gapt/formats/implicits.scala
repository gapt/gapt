package gapt.formats

import os._

object implicits {
  implicit def stringToPath( s: String ): Path = Path( FilePath( s ), pwd )
}
