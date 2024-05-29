package gapt.formats.json

import gapt.utils.Doc
import io.circe.Encoder

object JsonExporter {

  /**
   * Exports a value for which an Encoder exists to JSON.
   */
  def apply[A](x: A)(implicit ev: Encoder[A]): Doc = JsonToDoc(ev(x))
}
