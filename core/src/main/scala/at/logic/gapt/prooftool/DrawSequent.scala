package at.logic.gapt.prooftool

import at.logic.gapt.proofs.{ Sequent, SequentIndex }
import at.logic.gapt.expr._
import org.scilab.forge.jlatexmath.{ TeXConstants, TeXFormula, TeXIcon }
import java.awt.{ Color, Dimension, Font }
import java.awt.image.BufferedImage

import swing._
import event.{ MouseClicked, MouseEntered, MouseExited, WindowDeactivated }
import java.awt.event.MouseEvent

import at.logic.gapt.formats.latex.LatexExporter

import collection.mutable

object DrawSequent {
  def apply[T](
    main: ProofToolViewer[_],
    seq:  Sequent[T], ft: Font,
    mainAuxIndices:     Set[SequentIndex],
    cutAncestorIndices: Set[SequentIndex],
    t_renderer:         T => String
  ): DrawSequent[T] = new DrawSequent[T]( main, seq, mainAuxIndices, cutAncestorIndices, ft, t_renderer )

  def apply[T](
    main:       ProofToolViewer[_],
    seq:        Sequent[T],
    ft:         Font,
    t_renderer: T => String
  ): DrawSequent[T] = DrawSequent( main, seq, ft, Set(), Set(), t_renderer )
}

class DrawSequent[T](
    main:                         ProofToolViewer[_],
    val sequent:                  Sequent[T],
    val mainAuxIndices:           Set[SequentIndex],
    val cutAncestorIndices:       Set[SequentIndex],
    val ft:                       Font,
    val sequent_element_renderer: T => String
) extends FlowPanel {
  opaque = false // Necessary to draw the proof properly
  hGap = 0 // no gap between components

  val contextIndices = sequent.indices.toSet diff mainAuxIndices

  val turnstileLabel = LatexLabel( main, ft, "\\vdash" ) // \u22a2

  val elementLabelSequent = sequent map { f => LatexLabel( main, ft, sequent_element_renderer( f ), Color.WHITE ) }
  val commaLabelSequent = sequent map { _ => LatexLabel( main, ft, "," ) }

  contents ++= removeLast( ( elementLabelSequent.antecedent zip commaLabelSequent.antecedent ) flatMap { case ( x, y ) => Seq( x, y ) } )
  contents += turnstileLabel
  contents ++= removeLast( ( elementLabelSequent.succedent zip commaLabelSequent.succedent ) flatMap { case ( x, y ) => Seq( x, y ) } )

  // FIXME: figure out why + 10?  Is it the Label adding an inset?  Is the FlowPanel adding gaps?
  // It probably comes from the commas, which we render as JLabels and not as TeXIcons...
  val width = contents.map( _.asInstanceOf[LatexLabel].myicon.getIconWidth ).sum + 30
  val height = contents.map( _.asInstanceOf[LatexLabel].myicon.getIconHeight ).max + font.getSize / 2
  preferredSize = new Dimension( width, height )
  maximumSize = new Dimension( Int.MaxValue, height )

  listenTo( main.publisher )

  reactions += {
    case HideSequentContexts =>
      for ( i <- contextIndices ) {
        elementLabelSequent( i ).visible = false
        commaLabelSequent( i ).visible = false
      }

    case ShowAllFormulas =>
      for ( i <- contextIndices ) {
        elementLabelSequent( i ).visible = true
        commaLabelSequent( i ).visible = true
      }

    case MarkCutAncestors =>
      for ( i <- cutAncestorIndices )
        elementLabelSequent( i ).background = Color.GREEN

    case UnmarkCutAncestors =>
      for ( i <- cutAncestorIndices )
        elementLabelSequent( i ).background = Color.WHITE
  }

  private def removeLast[T]( xs: Seq[T] ): Seq[T] = xs match {
    case Seq() => Seq()
    case _     => xs.init
  }
}

object LatexLabel {
  private val cache = mutable.Map[( String, Font ), TeXIcon]()

  def clearCache() = this.synchronized( cache.clear() )

  def apply( main: ProofToolViewer[_], font: Font, latexText: String, color: Color = Color.white ): LatexLabel = {
    val icon = this.synchronized( cache.getOrElseUpdate(
      ( latexText, font ),
      new TeXFormula( latexText ).
        createTeXIcon( TeXConstants.STYLE_DISPLAY, font.getSize, TeXFormula.SANSSERIF )
    ) )
    new LatexLabel( main, font, latexText, icon, color )
  }
}

class LatexLabel(
  main:          ProofToolViewer[_],
  val ft:        Font,
  val latexText: String,
  val myicon:    TeXIcon,
  color:         Color
)
    extends Label( "", myicon, Alignment.Center ) {
  background = color
  foreground = Color.black
  font = ft
  opaque = true
  yLayoutAlignment = 0.5
  if ( latexText == "," ) {
    border = Swing.EmptyBorder( font.getSize / 5, 2, 0, font.getSize / 5 )
    icon = null
    text = latexText
  }
  if ( latexText == "\\vdash" ) border = Swing.EmptyBorder( font.getSize / 6 )

  listenTo( mouse.moves, mouse.clicks, main.publisher )
  reactions += {
    case e: MouseEntered => foreground = Color.blue
    case e: MouseExited  => foreground = Color.black
    case e: MouseClicked if e.peer.getButton == MouseEvent.BUTTON3 && e.clicks == 2 =>
      val d = new Dialog {
        resizable = false
        peer.setUndecorated( true )
        contents = new TextField( latexText ) {
          editable = false
          border = Swing.EmptyBorder( 7 )
          tooltip = "Select text and right-click to copy."
          font = font.deriveFont( Font.PLAIN, 14 )
          listenTo( mouse.clicks )
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
