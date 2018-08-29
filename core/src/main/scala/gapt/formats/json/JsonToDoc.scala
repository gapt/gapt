package gapt.formats.json

import gapt.utils.Doc
import io.circe.{ Json, JsonNumber, JsonObject }
import gapt.utils.Doc._

/**
 * Converts a JSON value into a Doc.
 */
object JsonToDoc {
  def apply( json: Json ): Doc = json.foldWith( DocFolder ).group

  private object DocFolder extends Json.Folder[Doc] {
    override def onNull: Doc = "null"

    override def onBoolean( value: Boolean ): Doc = if ( value ) "true" else "false"

    override def onNumber( value: JsonNumber ): Doc = value.toString

    override def onString( value: String ): Doc = "\"" <> value <> "\""

    override def onArray( value: Vector[Json] ): Doc = {
      "[" <> ( line <> Doc.sep( value.map( _.foldWith( DocFolder ) ), "," <> line ) ).nest( 2 ) </> "]"
    }

    override def onObject( value: JsonObject ): Doc = {
      "{" <> ( line <> Doc.sep( value.toList.map( ( entryToDoc _ ).tupled ), "," <> line ) ).nest( 2 ) </> "}"
    }

    private def entryToDoc( key: String, value: Json ): Doc = {
      onString( key ) <+> ":" <+> value.foldWith( DocFolder )
    }
  }
}

