package gapt.prooftool

import java.awt.event.MouseEvent
import java.awt.{Color, Font}

import scala.collection.mutable
import gapt.proofs.{Sequent, SequentIndex, SequentProof}
import org.scilab.forge.jlatexmath.{TeXConstants, TeXFormula, TeXIcon}

import scala.swing._
import scala.swing.event.{MouseClicked, MouseEntered, MouseExited, WindowDeactivated}

object DrawSequent {

  /**
   * Draws a sequent that is part of a sequent proof.
   * @param parent The DrawSequentProof object that this belongs to.
   * @param seq The sequent to be displayed.
   * @param mainAuxIndices The indices of main and aux formulas. Relevant for hiding contexts.
   * @param cutAncestorIndices The indices of cut ancestors.
   * @param sequentElementRenderer The function that turns elements of the sequent into strings.
   * @tparam F The type of elements of the sequent.
   */
  def apply[F, T <: SequentProof[F, T]](
      parent: DrawSequentProof[F, T],
      seq: Sequent[F],
      mainAuxIndices: Set[SequentIndex],
      cutAncestorIndices: Set[SequentIndex],
      sequentElementRenderer: F => String
  ): DrawSequentInProof[F, T] = new DrawSequentInProof[F, T](parent, seq, mainAuxIndices, cutAncestorIndices, sequentElementRenderer)

  /**
   * Draws a sequent.
   * @param main The main Prooftool window that this belongs to.
   * @param seq The sequent to be displayed.
   * @param sequentElementRenderer The function that turns elements of the sequent into strings.
   * @tparam F The type of elements of the sequent.
   */
  def apply[F, M <: ProofToolViewer[_]](
      main: M,
      seq: Sequent[F],
      sequentElementRenderer: F => String
  ): DrawSequent[F, M] = new DrawSequent(main, seq, sequentElementRenderer)
}

/**
 * Draws a sequent.
 * @param main The main Prooftool window that this belongs to.
 * @param sequent The sequent to be displayed.
 * @param sequentElementRenderer The function that turns elements of the sequent into strings.
 * @tparam F The type of elements of the sequent.
 */
class DrawSequent[F, M <: ProofToolViewer[_]](
    val main: M,
    val sequent: Sequent[F],
    val sequentElementRenderer: F => String
) extends BoxPanel(Orientation.Horizontal) {
  opaque = false // Necessary to draw the proof properly

  val turnstileLabel = new LatexTurnstileLabel(main) // \u22a2

  val elementLabelSequent = sequent map { f => new LatexFormulaLabel(main, sequentElementRenderer(f)) }
  val commaLabelSequent = sequent map { _ => new CommaLabel(main) }

  contents ++= removeLast((elementLabelSequent.antecedent zip commaLabelSequent.antecedent) flatMap { case (x, y) => Seq(x, y) })
  contents += turnstileLabel
  contents ++= removeLast((elementLabelSequent.succedent zip commaLabelSequent.succedent) flatMap { case (x, y) => Seq(x, y) })

  def width() = size.width

  private def removeLast[S](xs: Seq[S]): Seq[S] = xs match {
    case Seq() => Seq()
    case _     => xs.init
  }
}

/**
 * Draws a sequent that is part of a sequent proof.
 *
 * Unlike the general DrawSequent class, this contains logic relating to main/aux formulas and cut ancestors.
 *
 * @param parent The DrawSequentProof object that this belongs to.
 * @param sequent The sequent to be displayed.
 * @param mainAuxIndices The indices of main and aux formulas. Relevant for hiding contexts.
 * @param cutAncestorIndices The indices of cut ancestors.
 * @param sequentElementRenderer The function that turns elements of the sequent into strings.
 * @tparam F The type of elements of the sequent.
 */
class DrawSequentInProof[F, T <: SequentProof[F, T]](
    val parent: DrawSequentProof[F, T],
    sequent: Sequent[F],
    val mainAuxIndices: Set[SequentIndex],
    val cutAncestorIndices: Set[SequentIndex],
    sequentElementRenderer: F => String
) extends DrawSequent[F, SequentProofViewer[F, T]](parent.main, sequent, sequentElementRenderer) {
  require(mainAuxIndices.forall { sequent.isDefinedAt }, s"End sequent $sequent of proof at ${parent.pos} is undefined for some indices in $mainAuxIndices.")
  require(
    cutAncestorIndices.forall { sequent.isDefinedAt },
    s"End sequent $sequent of proof at ${parent.pos}  is undefined for some indices in $cutAncestorIndices."
  )

  val pos = parent.pos
  val contextIndices = sequent.indices.toSet diff mainAuxIndices
  val mainAuxIndicesAnt = mainAuxIndices filter { _.isAnt }
  val mainAuxIndicesSuc = mainAuxIndices filterNot { _.isAnt }

  listenTo(main.publisher)

  reactions += {
    case HideSequentContexts =>
      for (i <- contextIndices) {
        elementLabelSequent(i).visible = false
        commaLabelSequent(i).visible = false
      }

      if (mainAuxIndicesAnt.size == 1)
        commaLabelSequent(mainAuxIndicesAnt.head).visible = false

      if (mainAuxIndicesSuc.size == 1)
        commaLabelSequent(mainAuxIndicesSuc.head).visible = false

    case ShowAllFormulas =>
      for (i <- contextIndices) {
        elementLabelSequent(i).visible = true
        commaLabelSequent(i).visible = true
      }

      if (mainAuxIndicesAnt.size == 1)
        commaLabelSequent(mainAuxIndicesAnt.head).visible = true

      if (mainAuxIndicesSuc.size == 1)
        commaLabelSequent(mainAuxIndicesSuc.head).visible = true

    case MarkCutAncestors =>
      for (i <- cutAncestorIndices)
        elementLabelSequent(i).mark()

    case UnmarkCutAncestors =>
      for (i <- cutAncestorIndices)
        elementLabelSequent(i).unmark()

    case MarkOccurrences(p, is) if p == pos =>
      for (i <- is)
        elementLabelSequent(i).mark()

    case UnmarkAllFormulas =>
      elementLabelSequent.foreach {
        _.resetMarkLevel()
      }
  }

  // Add reactions to formulas
  for ((f, i) <- elementLabelSequent.zipWithIndex) {
    f.reactions += {
      case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 && e.clicks == 1 =>
        gapt.prooftool.PopupMenu(main, f, pos, i, e.point.x, e.point.y)
    }
  }

}

/**
 * Creates Latex icons from strings.
 */
object LatexIcon {
  private val cache = mutable.Map[(String, Font), TeXIcon]()

  def clearCache() = this.synchronized(cache.clear())

  /**
   * Turns latex code into an icon.
   * @param latexText The Latex code to be rendered as an icon.
   * @param font The font.
   * @return An icon displaying latexText.
   */
  def apply(latexText: String, font: Font): TeXIcon = synchronized(cache.getOrElseUpdate(
    (latexText, font),
    new TeXFormula(latexText).createTeXIcon(TeXConstants.STYLE_DISPLAY, font.getSize().toFloat, TeXFormula.SANSSERIF)
  ))
}

object LatexLabel {

  /**
   * Factory for LatexLabels.
   * @param main The main window that the label will belong to.
   * @param latexText The text the label will display.
   */
  def apply(main: ProofToolViewer[_], latexText: String): LatexLabel = {
    if (latexText == ",")
      throw new IllegalArgumentException("Use `new CommaLabel(main)`")
    else if (latexText == "\\vdash")
      new LatexTurnstileLabel(main)
    else
      new LatexFormulaLabel(main, latexText)
  }
}

/**
 * A label displaying an icon that is rendered using Latex.
 * @param main The main Prooftool window that this belongs to.
 * @param latexText The latex code to be displayed.
 */
class LatexLabel(val main: ProofToolViewer[_], val latexText: String) extends Label("", null, Alignment.Center) {
  background = Color.white
  foreground = Color.black
  opaque = true
  def defaultBorder = Swing.EmptyBorder
  border = defaultBorder

  icon = LatexIcon(latexText, main.font)

  listenTo(main.publisher)

  reactions += {
    case FontChanged =>
      icon = LatexIcon(latexText, main.font)
      border = defaultBorder
  }
}

/**
 * LatexLabel for displaying formulas.
 *
 * The difference from plain LatexLabel is that it reacts to the mouse.
 * @param main The main Prooftool window that this belongs to.
 * @param latexText The latex code to be displayed.
 */
class LatexFormulaLabel(
    main: ProofToolViewer[_],
    latexText: String
) extends LatexLabel(main, latexText) {

  private var markLevel = 0

  def mark(): Unit = {
    markLevel += 1
    background = Color.GREEN
  }

  def unmark(): Unit = {
    markLevel = if (markLevel == 0) 0 else markLevel - 1
    assert(markLevel >= 0)

    if (markLevel == 0) background = Color.WHITE
  }

  def resetMarkLevel(): Unit = {
    markLevel = 0
    background = Color.WHITE
  }

  listenTo(mouse.moves, mouse.clicks)
  reactions += {
    case e: MouseEntered => foreground = Color.blue
    case e: MouseExited  => foreground = Color.black
    case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 && e.clicks == 2 =>
      val d = new Dialog {
        resizable = false
        peer.setUndecorated(true)
        contents = new TextField(latexText) {
          editable = false
          border = Swing.EmptyBorder(7)
          tooltip = "Select text and right-click to copy."
          font = font.deriveFont(Font.PLAIN, 14)
          listenTo(mouse.clicks)
          reactions += {
            case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 => copy()
          }
        }
        //  modal = true
        reactions += {
          case e: WindowDeactivated if e.source == this => dispose()
        }
      }
      d.location = locationOnScreen
      d.open()
  }
}

/**
 * Label for displaying commas.
 * @param main The main Prooftool window that this belongs to.
 */
class CommaLabel(val main: ProofToolViewer[_]) extends Label(",", icon0 = null, Alignment.Center) {
  def defaultBorder = Swing.EmptyBorder(font.getSize / 5, 2, 0, font.getSize / 5)
  border = defaultBorder
  font = main.font

  listenTo(main.publisher)

  reactions += {
    case FontChanged =>
      font = main.font
      border = defaultBorder
  }
}

/**
 * Latexlabel for displaying the turnstile symbol (u+22a2, ⊢)
 * @param main The main Prooftool window that this belongs to.
 */
class LatexTurnstileLabel(main: ProofToolViewer[_]) extends LatexLabel(main, "\\vdash") {
  override def defaultBorder = Swing.EmptyBorder(font.getSize / 6)
}
