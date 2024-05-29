package gapt.utils
import Doc._
import os.{Path, write}

import scala.language.implicitConversions

sealed trait Doc {

  /**
   * Concatenate two documents.
   */
  def <>(that: Doc): Doc = Concat(this, that)

  /**
   * Concatenate two documents with a space between them.
   */
  def <+>(that: Doc): Doc = this <> " " <> that

  /**
   * Concatenate two documents with a line break between them.
   *
   */
  def </>(that: Doc): Doc = this <> line <> that

  /**
   * Nest a document to `i` spaces of indentation.
   * @param i Then number of spaces to indent by.
   */
  def nest(i: Int): Doc = Nest(i, this)

  /**
   * Group a document such that it is displayed on one line
   * if possible.
   */
  def group: Doc = Group(this)

  /** Length of this document, if all Lines were printed as spaces. */
  private val flatSize: Int = this match {
    case Concat(a, b) => a.flatSize + b.flatSize
    case Nest(_, d)   => d.flatSize
    case Text(t)      => t.length
    case Line(orElse) => orElse.length
    case Group(a)     => a.flatSize
  }

  /** Whether this document contains a Line. */
  private val containsLine: Boolean = this match {
    case Line(_)      => true
    case Concat(a, b) => a.containsLine || b.containsLine
    case Nest(_, d)   => d.containsLine
    case Text(_)      => false
    case Group(a)     => a.containsLine
  }

  /** Number of characters until the first Line or the end of the document. */
  private val distToFirstLine: Int = this match {
    case Line(_)      => 0
    case Concat(a, b) => a.distToLine(b.distToFirstLine)
    case Nest(_, d)   => d.distToFirstLine
    case Text(t)      => t.length
    case Group(a)     => a.distToFirstLine
  }

  /**
   * Assume that we're followed by `afterwards` many characters and a Line.
   * How many characters until the first Line (or the end)?
   */
  private def distToLine(afterwards: Int): Int =
    if (containsLine) distToFirstLine else distToFirstLine + afterwards

  /**
   * Turn the document into a string.
   * @param lineWidth No line in the result string will exceed this length, unless it is unavoidable.
   */
  def render(lineWidth: Int): String = {
    val out = new StringBuilder
    var endOfLine = out.size + lineWidth
    def go(d: Doc, nest: Int, flatMode: Boolean, distToNextLine: Int): Unit =
      d match {
        case Concat(a, b) =>
          go(a, nest, flatMode, b.distToLine(distToNextLine))
          go(b, nest, flatMode, distToNextLine)
        case Nest(i, a) =>
          go(a, nest + i, flatMode, distToNextLine)
        case Text(t) =>
          out ++= t
        case Line(orElse) =>
          if (!flatMode) {
            out += '\n'
            endOfLine = out.size + lineWidth
            for (_ <- 0 until nest) out += ' '
          } else {
            out ++= orElse
          }
        case Group(a) =>
          go(a, nest, flatMode || out.size + a.flatSize + distToNextLine <= endOfLine, distToNextLine)
      }
    go(this, nest = 0, flatMode = false, distToNextLine = 0)
    out.result()
  }

  override def toString: String = render(80)

  def firstChar: Option[Char] = this match {
    case Concat(a, _) => a.firstChar
    case Nest(_, d)   => d.firstChar
    case Text(t)      => t.headOption
    case Line(_)      => None
    case Group(a)     => a.firstChar
  }

  /**
   * Writes the document to the specified file, replacing the current contents.
   */
  def writeToFile(file: Path): Unit = write.over(file, render(80))

}

object Doc {
  private case class Concat(a: Doc, b: Doc) extends Doc
  private case class Nest(i: Int, d: Doc) extends Doc
  private case class Text(t: String) extends Doc
  private case class Line(orElse: String) extends Doc
  private case class Group(a: Doc) extends Doc

  /**
   * A line break that is optionally replaced by a space.
   */
  def line: Doc = Line(" ")

  /**
   * Line break that is optionally replaced by nothing.
   */
  def zeroWidthLine: Doc = Line("")
  implicit def text(t: String): Doc = Text(t)

  /**
   * Concatenate a series of docs with a separator between them.
   */
  def sep(docs: Iterable[Doc], by: Doc): Doc =
    docs.reduceLeftOption(_ <> by <> _).getOrElse(Text(""))

  /**
   * Concatenate a series of docs with spaces between them.
   */
  def spread(cols: Iterable[Doc]): Doc = sep(cols, Text(" "))

  /**
   * Concatenate a series of docs with line breaks between them.
   */
  def stack(lines: Iterable[Doc]): Doc = sep(lines, line)

  /**
   * Groups a series of [[Doc]]s such that as many as possible will
   * be put on one line.
   * @param sep A separator between each pair of elements.
   */
  def wordwrap(ds: Iterable[Doc], sep: Doc = ""): Doc =
    ds.view.zipWithIndex.map { case (d, i) => if (i == 0) d else (sep <> line <> d).group }.reduceLeftOption(_ <> _).getOrElse("")

  /**
   * Groups a series of [[Doc]]s such that as many as possible will
   * be put on the first line, after which each one is put on a new line.
   * @param sep A separator between each pair of elements.
   */
  def wordwrap2(ds: Iterable[Doc], sep: Doc = ""): Doc =
    ds.reduceLeftOption((a, b) => (a <> sep </> b).group).getOrElse("")
}
