package gapt.formats.json

import gapt.utils.Doc
import io.circe.{Json, JsonNumber, JsonObject}
import gapt.utils.Doc._
import java.lang.StringBuilder

/**
 * Converts a JSON value into a Doc.
 */
object JsonToDoc {
  def apply(json: Json): Doc = json.foldWith(DocFolder).group

  private object DocFolder extends Json.Folder[Doc] {
    override def onNull: Doc = "null"

    override def onBoolean(value: Boolean): Doc = if (value) "true" else "false"

    override def onNumber(value: JsonNumber): Doc = value.toString

    override def onString(value: String): Doc = {
      val writer = new StringBuilder()

      writer.append('"')

      var i = 0
      var offset = 0

      while (i < value.length) {
        val c = value.charAt(i)

        if (
          (c == '"' || c == '\\' || c == '\b' || c == '\f' || c == '\n' || c == '\r' || c == '\t') ||
          Character.isISOControl(c)
        ) {
          writer.append(value, offset, i)
          writer.append('\\')
          c match {
            case '"'  => writer.append('"')
            case '\\' => writer.append('\\')
            case '\b' => writer.append('b')
            case '\f' => writer.append('f')
            case '\n' => writer.append('n')
            case '\r' => writer.append('r')
            case '\t' => writer.append('t')
            case control =>
              writer.append(String.format("u%04x", Integer.valueOf(control.toInt)))
          }
          offset = i + 1
        }

        i += 1
      }

      if (offset < i) writer.append(value, offset, i)
      writer.append('"')

      writer.toString
    }

    override def onArray(value: Vector[Json]): Doc = {
      ("[" <>
        (zeroWidthLine <> Doc.sep(value.map(_.foldWith(DocFolder)), "," <> line)).nest(2) <>
        zeroWidthLine <> "]").group
    }

    override def onObject(value: JsonObject): Doc = {
      ("{" <>
        (zeroWidthLine <> Doc.sep(value.toList.map((entryToDoc _).tupled), "," <> line)).nest(2) <>
        zeroWidthLine <> "}").group
    }

    private def entryToDoc(key: String, value: Json): Doc = {
      onString(key) <+> ":" <+> value.foldWith(DocFolder)
    }
  }
}
