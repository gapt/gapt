package gapt.formats.json

import io.circe.Encoder

object JsonExporter {
  /**
   * Exports a value for which an Encoder exists to JSON.
   */
  def apply[A]( x: A )( implicit ev: Encoder[A] ): String = ev( x ).toString
}
