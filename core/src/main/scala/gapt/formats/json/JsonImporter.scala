package gapt.formats.json

import gapt.formats.InputFile
import io.circe.Decoder
import io.circe.parser._

object JsonImporter {

  /**
   * Imports a value for which a Decoder exists from JSON.
   */
  def load[A: Decoder](file: InputFile): A =
    decode[A](file.read).toTry.get
}
