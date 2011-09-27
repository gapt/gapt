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
import at.logic.language.lambda.substitutions.Substitution
import at.logic.calculi.lk.base.types._

class SubstitutionTest extends SpecificationWithJUnit {
  "Substitutions" should {
    "apply correctly to a simple proof" in {
      val x = HOLVar( "x", i )
      val px = Atom( "P", x::Nil )
      val s = new FSequent( px::Nil, px::Nil )
      val ax1 = Axiom( px::Nil, px::Nil )
      val ax2 = Axiom( px::Nil, px::Nil )
      val proof = CutRule( ax1, ax2, ax1.root.succedent.toList.head, ax2.root.antecedent.toList.head )
      val a = HOLConst( new ConstantStringSymbol( "a" ), i )
      val f = HOLConst( new ConstantStringSymbol( "f" ), i -> i )
      val fa = HOLApp( f, a )
      val subst = Substitution[HOLExpression]( x, fa )
      val p_s = applySubstitution( proof, subst )
      val pfa = Atom( "P", fa::Nil )
      val new_seq = new FSequent( pfa::Nil, pfa::Nil )
      val seq = p_s._1.root.toFSequent
      seq must beEqual( new_seq )
    }
  }
}
