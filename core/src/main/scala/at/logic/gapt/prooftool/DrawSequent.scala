package at.logic.gapt.prooftool

import at.logic.gapt.proofs.Sequent
import at.logic.gapt.expr._
import org.scilab.forge.jlatexmath.{ TeXConstants, TeXFormula, TeXIcon }
import java.awt.{ Color, Dimension, Font }
import java.awt.image.BufferedImage

import swing._
import event.{ MouseClicked, MouseEntered, MouseExited, WindowDeactivated }
import java.awt.event.MouseEvent

import at.logic.gapt.formats.latex.LatexUIRenderer.formulaToLatexString

import collection.mutable

object DrawSequent {
  def apply[T <: HOLFormula]( main: ProofToolViewer[_], sequent: Sequent[T], visibility: Sequent[Boolean], colors: Sequent[Color], ft: Font ) =
    new DrawSequent[T]( main, sequent, visibility, colors, ft, x => formulaToLatexString( x, true ) )

  /*
  def apply[T <: LabelledFormula]( main: ProofToolViewer[_], sequent: Sequent[T], visibility: Sequent[Boolean], colors: Sequent[Color], ft: Font ) =
    new DrawSequent[T]( main, sequent, visibility, colors, ft, x => formulaToLatexString( x._2, true ) )
    */

  //used by DrawClList to draw FSequents
  def apply[T]( main: ProofToolViewer[_], seq: Sequent[T], ft: Font, visibility: Sequent[Boolean], colors: Sequent[Color], t_renderer: T => String )( implicit dummyImplicit: DummyImplicit ): DrawSequent[T] = {
    /*
    val visibility = if ( str.isEmpty )
      seq map { _ => true }
    else
      seq map { f => t_renderer( f ) contains str }
    val colors = seq map { _ => Color.white }
      */
    new DrawSequent[T]( main, seq, visibility, colors, ft, t_renderer )
  }

  //used by DrawClList to draw FSequents
  def apply[T]( main: ProofToolViewer[_], seq: Sequent[T], ft: Font, str: String, t_renderer: T => String )( implicit dummyImplicit: DummyImplicit ): DrawSequent[T] = {
    val visibility = if ( str.isEmpty )
      seq map { _ => true }
    else
      seq map { f => t_renderer( f ) contains str }
    val colors = seq map { _ => Color.white }
    new DrawSequent[T]( main, seq, visibility, colors, ft, t_renderer )
  }

  //used by DrawProof
  //  def apply( main: ProofToolViewer[_], seq: OccSequent, ft: Font, vis_occ: Option[Set[FormulaOccurrence]] ): DrawSequent[HOLFormula] = {
  //    val visibility = vis_occ match {
  //      case None        => seq map { fo => true }
  //      case Some( set ) => seq map { fo => set contains fo }
  //    }
  //    val colors = seq map { fo => Color.white }
  //    DrawSequent[HOLFormula]( main, seq.toHOLSequent, visibility, colors, ft )
  //  }

  def formulaToLabel( main: ProofToolViewer[_], f: HOLFormula, ft: Font ): LatexLabel = LatexLabel( main, ft, formulaToLatexString( f ) )

}

class DrawSequent[T](
    main:                         ProofToolViewer[_],
    val sequent:                  Sequent[T],
    val visibility:               Sequent[Boolean],
    val colors:                   Sequent[Color],
    val ft:                       Font,
    val sequent_element_renderer: T => String
) extends FlowPanel {
  opaque = false // Necessary to draw the proof properly
  hGap = 0 // no gap between components

  listenTo( main.publisher )

  private var first = true
  for ( ( f, v, c ) <- zip3( sequent, visibility, colors ).antecedent ) {
    if ( v ) {
      if ( !first ) contents += LatexLabel( main, ft, "," )
      else first = false
      contents += LatexLabel( main, ft, sequent_element_renderer( f ), c )
    }
  }
  contents += LatexLabel( main, ft, "\\vdash" ) // \u22a2
  first = true
  for ( ( f, v, c ) <- zip3( sequent, visibility, colors ).succedent ) {
    if ( v ) {
      if ( !first ) contents += LatexLabel( main, ft, "," )
      else first = false
      contents += LatexLabel( main, ft, sequent_element_renderer( f ), c )
    }
  }

  // FIXME: figure out why + 10?  Is it the Label adding an inset?  Is the FlowPanel adding gaps?
  val width = contents.map( _.asInstanceOf[LatexLabel].myicon.getIconWidth ).sum + 10
  val height = contents.map( _.asInstanceOf[LatexLabel].myicon.getIconHeight ).max + 10
  maximumSize = new Dimension( width, height )

  private def zip3[A, B, C]( seq1: Sequent[A], seq2: Sequent[B], seq3: Sequent[C] ): Sequent[( A, B, C )] = ( ( seq1 zip seq2 ) zip seq3 ) map { x => ( x._1._1, x._1._2, x._2 ) }
}

object LatexLabel {
  private val cache = mutable.Map[( String, Font ), TeXIcon]()

  def clearCache() = this.synchronized( cache.clear() )

  def apply( main: ProofToolViewer[_], font: Font, latexText: String, color: Color = Color.white ): LatexLabel = {
    val key = ( latexText, font )
    this.synchronized( {
      val icon = cache.getOrElseUpdate( key, {
        val formula = try {
          new TeXFormula( latexText )
        } catch {
          case e: Exception =>
            throw new Exception( "Could not create formula " + latexText + ": " + e.getMessage, e )
        }
        val myicon = formula.createTeXIcon( TeXConstants.STYLE_DISPLAY, font.getSize )
        val myimage = new BufferedImage( myicon.getIconWidth, myicon.getIconHeight, BufferedImage.TYPE_INT_ARGB )
        val g2 = myimage.createGraphics()
        g2.setColor( Color.white )
        g2.fillRect( 0, 0, myicon.getIconWidth, myicon.getIconHeight )
        myicon.paintIcon( null, g2, 0, 0 )
        myicon
      } )
      new LatexLabel( main, font, latexText, icon, color )
    } )
  }
}

class LatexLabel( main: ProofToolViewer[_], val ft: Font, val latexText: String, val myicon: TeXIcon, var color: Color )
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
    /*case ChangeFormulaColor( set, color, reset ) =>
      if ( set.contains( fo ) ) background = color
      else if ( reset ) background = Color.white*/
  }
}
