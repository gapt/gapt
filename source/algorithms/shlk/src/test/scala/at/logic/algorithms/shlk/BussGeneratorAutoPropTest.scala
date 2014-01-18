package at.logic.algorithms.shlk

import at.logic.calculi.lk.propositionalRules.{Axiom, NegLeftRule}
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.base.{Sequent, FSequent}
import at.logic.algorithms.shlk._

import at.logic.language.hol._

import java.io.File.separator
import scala.io._
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.execute.Success
import at.logic.language.lambda.types.Ti
import at.logic.algorithms.lk._


@RunWith(classOf[JUnitRunner])
class BussGeneratorAutoPropTest extends SpecificationWithJUnit {
  implicit val factory = defaultFormulaOccurrenceFactory
  import at.logic.language.schema._
  "BussGeneratorAutoPropTest" should {
    "continue autopropositional" in {

      //println("\n\nBuss generator Examples")
      val a = HOLConst(new ConstantStringSymbol("a"), Ti())

      val Pc1 = Atom(new ConstantStringSymbol("Pc1"), a::Nil)
      val Pc2 = Atom(new ConstantStringSymbol("Pc2"), a::Nil)
      val Pd1 = Atom(new ConstantStringSymbol("Pd1"), a::Nil)
      val Pd2 = Atom(new ConstantStringSymbol("Pd2"), a::Nil)
      val Pc1_or_Pd1 = at.logic.language.hol.Or(Pc1, Pd1)
      val imp_Pc1_or_Pd1_Pc2 = at.logic.language.hol.Imp(Pc1_or_Pd1, Pc2)
      val imp_Pc1_or_Pd1_Pd2 = at.logic.language.hol.Imp(Pc1_or_Pd1, Pd2)
      val imp_Pc1_or_Pd1_Pc2__or__imp_Pc1_or_Pd1_Pd2 = at.logic.language.hol.Or(imp_Pc1_or_Pd1_Pc2, imp_Pc1_or_Pd1_Pd2)
//      val fs = FSequent(imp_Pc1_or_Pd1_Pc2__or__imp_Pc1_or_Pd1_Pd2 :: Pc1_or_Pd1 :: Nil , Pc2::Pd2::Nil)
      val fs = BussTautology(2)
      val bussGen = solve.solvePropositional(fs)

      Success()
    }
  }
}

object BussTautology {
  def apply( n: Int ) : FSequent = FSequent( Ant( n ), c( n )::d( n )::Nil )

  val a = HOLConst(new ConstantStringSymbol("a"), Ti())

  def c( i: Int ) = Atom( new ConstantStringSymbol("c_" + i), a::Nil )
  def d( i: Int ) = Atom( new ConstantStringSymbol("d_" + i), a::Nil )
  def F( i: Int ) : HOLFormula =  if ( i == 1 )
                                      Or( c( 1 ), d( 1 ) )
                                  else
                                      And( F( i - 1 ), Or( c( i ), d( i ) ) )
  def A( i: Int ) = if ( i == 1 )  c( 1 )
                    else Imp( F( i - 1 ), c( i ) )
  def B( i: Int ) = if ( i == 1 )  d( 1 )
                    else Imp( F( i - 1 ), d( i ) )

  // the antecedens of the final sequent
  def Ant( i: Int ) : List[HOLFormula] = if ( i == 0 ) Nil else Or( A( i ), B( i ))::Ant( i - 1 )
}
