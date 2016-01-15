package at.logic.gapt.formats.latex

import at.logic.gapt.expr.{ FOLConst, LambdaExpression }
import at.logic.gapt.formats.arithmetic.HOLTermArithmeticalExporter
import at.logic.gapt.formats.writers.FileWriter
import at.logic.gapt.proofs.lkOld.base._
import at.logic.gapt.proofs.lkOld.getTypeInformation
import at.logic.gapt.proofs.lksk.LabelledOccSequent

// TODO: Martin - please clean this up.
object exportSequentListLatex {
  def apply( ls: List[OccSequent], outputFile: String ) = {
    // maps original types and definitions of abstractions
    val sectionsPre = ( "Types", getTypeInformation( ls ).toList.sortWith( ( x, y ) => x.toString < y.toString ) ) :: Nil

    val sections = try {
      // convert to fol and obtain map of definitons
      val imap = Map[LambdaExpression, String]()
      val iid = new {
        var idd = 0;

        def nextId = {
          idd = idd + 1; idd
        }
      }
      /*
             val cs = ls.map(x => Sequent(
             x.antecedent.map(y => reduceHolToFol(y.asInstanceOf[LambdaExpression],imap,iid).asInstanceOf[FOLFormula]),
             x.succedent.map(y => reduceHolToFol(y.asInstanceOf[LambdaExpression],imap,iid).asInstanceOf[FOLFormula])
             ))*/
      ( "Definitions", imap.toList.map( x => ( x._1, FOLConst( x._2 ) ) ) ) :: sectionsPre
    } catch {
      case _: Exception => sectionsPre
    }
    ( new FileWriter( outputFile ) with SequentsListLatexExporter with HOLTermArithmeticalExporter ).exportSequentList( ls map ( _.toHOLSequent ), sections ).close
  }
}

object exportLabelledSequentListLatex {
  def apply( ls: List[LabelledOccSequent], outputFile: String ) = {
    // maps original types and definitions of abstractions
    val sections = ( "Types", getTypeInformation( ls ).toList.sortWith( ( x, y ) => x.toString < y.toString ) ) :: Nil
    ( new FileWriter( outputFile ) with LabelledSequentsListLatexExporter with HOLTermArithmeticalExporter ).exportSequentList( ls, sections ).close
  }
}

