/** 
 * Description: 
**/

package at.logic.algorithms.lk

import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher

import at.logic.language.hol._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.lk.propositionalRules._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.calculi.occurrences._

class RegularizationTest extends SpecificationWithJUnit {
  "Regularization" should {
    "apply correctly to a simple proof" in {
      val x = HOLVar( "x", i )
      val px = Atom( "P", x::Nil )
      val px_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(px, Nil)
      val s = Sequent( px_occ::Nil, px_occ::Nil )
      val ax1 = Axiom( px::Nil, px::Nil )
      val ax2 = Axiom( px::Nil, px::Nil )
      val proof = CutRule( ax1, ax2, ax1.root.succedent.head, ax2.root.antecedent.head )
      val p_s = regularize( proof )
      def manOf[T: Manifest](t: T): Manifest[T] = manifest[T] 
      val type1 = p_s._1.root.succedent.head.formula.getFreeAndBoundVariables
      println(type1.toString)
      val type2 = s.succedent.head.formula.getFreeAndBoundVariables
      println(type2.toString)
      p_s._1.root must beEqual( s )
    }
  }
}
