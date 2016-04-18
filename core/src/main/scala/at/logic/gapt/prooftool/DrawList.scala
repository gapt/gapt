package at.logic.gapt.prooftool

import java.awt.{ Font, Color }
import Font._
import at.logic.gapt.proofs.lkskNew.LKskProof.{ LabelledSequent, LabelledFormula }
import at.logic.gapt.proofs.{ Sequent, HOLSequent }
import at.logic.gapt.expr._
import scala.swing.{ Component, FlowPanel, GridPanel, Label }
import at.logic.gapt.formats.latex.LatexUIRenderer.{ formulaToLatexString, labelledFormulaToLatexString }

class DrawList(
    main:         ListViewer,
    val list:     List[Any],
    val fontSize: Int
) extends GridPanel( 0, 1 ) {
  background = new Color( 255, 255, 255 )
  private var str: String = ""
  initialize()

  def search_=( string: String ) {
    str = string
    contents.clear()
    initialize()
  }
  def search = str

  def initialize() {
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
      case s: Sequent[T] if s.nonEmpty => {
        val colors = s map { _ => Color.white }

        s.elements.head match {
          case _: LabelledFormula =>
            DrawSequent[LabelledFormula]( main, s.asInstanceOf[LabelledSequent], ft, str, ( x: LabelledFormula ) => labelledFormulaToLatexString( x ) )
          case _: HOLFormula =>
            DrawSequent[HOLFormula]( main, s.asInstanceOf[HOLSequent], ft, str, ( x: HOLFormula ) => formulaToLatexString( x ) )
        }
      }
      case ( f1: LambdaExpression, f2: LambdaExpression ) => drawDefinition( f1, f2, ft )
      case _ => new Label( x.toString ) {
        background = new Color( 255, 255, 255 )
        opaque = true
        font = ft
        if ( !str.isEmpty && text.contains( str ) ) background = new Color( 0, 255, 0 )
      }
    }
  }

  def drawDefinition( f1: LambdaExpression, f2: LambdaExpression, ft: Font ) = new FlowPanel {
    background = new Color( 255, 255, 255 )
    opaque = false

    val label1 = expressionToLabel( f1 )
    val label2 = expressionToLabel( f2 )

    if ( !str.isEmpty && label1.latexText.contains( str ) ) label1.background = new Color( 0, 255, 0 )
    if ( !str.isEmpty && label2.latexText.contains( str ) ) label2.background = new Color( 0, 255, 0 )

    contents += label1
    contents += new Label( " := " ) { font = ft }
    contents += label2

    def expressionToLabel( e: LambdaExpression ): LatexLabel = LatexLabel( main, ft, formulaToLatexString( e ) )
  }
}
