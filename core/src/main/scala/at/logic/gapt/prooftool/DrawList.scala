package at.logic.gapt.prooftool

import java.awt.{ Color, Font }
import Font._

import at.logic.gapt.proofs.lksk.LKskProof.{ LabelledFormula, LabelledSequent }
import at.logic.gapt.proofs.{ HOLSequent, Sequent }
import at.logic.gapt.expr._
import at.logic.gapt.formats.latex.LatexExporter

import scala.swing.{ Component, FlowPanel, GridPanel, Label }

class DrawList(
    main:         ListViewer,
    val list:     List[Any],
    val fontSize: Int
) extends GridPanel( 0, 1 ) {
  background = new Color( 255, 255, 255 )

  val ft = new Font( SANS_SERIF, PLAIN, fontSize )
  var first = true
  for ( x <- list ) {
    if ( first ) {
      first = false
      val component = drawMember( x )
      contents += component
    } else {
      contents += new Label( ";" ) { font = ft }
      val component = drawMember( x )
      contents += component
    }
  }

  def drawMember[T]( x: Any ): Component = x match {
    case s: Sequent[t] if s.nonEmpty => {
      s.elements.head match {
        case _: HOLFormula =>
          DrawSequent( main, s.asInstanceOf[HOLSequent], ft, ( x: HOLFormula ) => LatexExporter( x ) )
      }
    }
    case ( f1: LambdaExpression, f2: LambdaExpression ) => drawDefinition( f1, f2, ft )
    case _ => new Label( x.toString ) {
      background = new Color( 255, 255, 255 )
      opaque = true
      font = ft
    }
  }

  def drawDefinition( f1: LambdaExpression, f2: LambdaExpression, ft: Font ) = new FlowPanel {
    background = new Color( 255, 255, 255 )
    opaque = false

    val label1 = expressionToLabel( f1 )
    val label2 = expressionToLabel( f2 )

    contents += label1
    contents += new Label( " := " ) { font = ft }
    contents += label2

    def expressionToLabel( e: LambdaExpression ): LatexLabel = LatexLabel( main, ft, LatexExporter( e ) )
  }
}
