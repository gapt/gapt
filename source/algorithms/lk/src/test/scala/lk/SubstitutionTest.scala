/** 
 * Description: 
**/

package at.logic.algorithms.lk

import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher

import at.logic.language.hol.propositions._
import at.logic.language.hol._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.lk.propositionalRules._
import at.logic.language.hol.substitutions.Substitution
import at.logic.language.lambda.substitutions.SingleSubstitution
import at.logic.language.lambda.types.Definitions._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.typedLambdaCalculus._

class SubstitutionTest extends SpecificationWithJUnit {
  "Substitutions" should {
    val x = HOLVar( "x", i )
    val Px = Atom( "P", x::Nil )
    val s = Sequent( Px::Nil, Px::Nil )
    val ax1 = Axiom( s )._1
    val ax2 = Axiom( s )._1
    val proof = CutRule( ax1, ax2, ax1.root.succedent.toList.first, ax2.root.antecedent.toList.first )
    val a = HOLConst( new ConstantStringSymbol( "a" ), i )
    val f = HOLConst( new ConstantStringSymbol( "f" ), i -> i )
    val fa = HOLApp( f, a )
    val ssubst = SingleSubstitution( x, fa )
    val subst = Substitution( ssubst::Nil )

    "apply correctly to a simple proof" in {
      val p_s = applySubstitution( proof, subst )
      val Pfa = Atom( "P", fa::Nil )
      val new_seq = Sequent( Pfa::Nil, Pfa::Nil )
      p_s._1.root.getSequent must beEqual( new_seq )
    }
  }
}
