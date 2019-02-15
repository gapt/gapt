package gapt.prooftool

import java.awt.{ Color, Font }
import Font._

import gapt.proofs.{ HOLSequent, Sequent }
import gapt.expr._
import gapt.expr.formula.Formula
import gapt.formats.latex.LatexExporter

import scala.swing.{ Component, FlowPanel, GridPanel, Label }

class DrawList(
    val main: ListViewer,
    val list: List[Any] ) extends GridPanel( 0, 1 ) {
  background = new Color( 255, 255, 255 )

  var first = true
  for ( x <- list ) {
    if ( first ) {
      first = false
      val component = drawMember( x )
      contents += component
    } else {
      contents += new Label( ";" ) { font = main.font }
      val component = drawMember( x )
      contents += component
    }
  }

  def drawMember[T]( x: Any ): Component = x match {
    case s: Sequent[t] if s.nonEmpty =>
      s.elements.head match {
        case _: Formula =>
          DrawSequent( main, s.asInstanceOf[HOLSequent], ( x: Formula ) => LatexExporter( x ) )
      }

    case ( f1: Expr, f2: Expr ) => drawDefinition( f1, f2 )
    case _ => new Label( x.toString ) {
      background = new Color( 255, 255, 255 )
      opaque = true
      font = main.font
    }
  }

  def drawDefinition( f1: Expr, f2: Expr ) = new FlowPanel {
    background = new Color( 255, 255, 255 )
    opaque = false

    val label1 = expressionToLabel( f1 )
    val label2 = expressionToLabel( f2 )

    contents += label1
    contents += new Label( " := " ) { font = main.font }
    contents += label2

    def expressionToLabel( e: Expr ): LatexLabel = LatexLabel( main, LatexExporter( e ) )
  }
}
