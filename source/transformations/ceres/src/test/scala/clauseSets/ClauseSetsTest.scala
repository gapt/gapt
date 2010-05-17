/** 
 * Description: 
**/

package at.logic.transformations.ceres.clauseSets

import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher

import scala.xml._

import at.logic.language.hol._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base.Sequent
import at.logic.transformations.ceres.struct._

class ClauseSetsTest extends SpecificationWithJUnit {
  /*
  // commented out --- we need to construct formula occurrences, but they
     are abstract and the factory is private to LK
  "ClauseSets" should {
    "- transform a Struct into a standard clause set" in {
      val a = HOLVarFormula( "a" )
      val b = HOLVarFormula( "b" )
      val c = HOLVarFormula( "c" )
      val d = HOLVarFormula( "d" )

      val struct = Times(Plus(A(a), A(b)), Plus(A(c), A(d)))
      val cs = StandardClauseSet.transformStructToClauseSet( struct ).getSequent
      cs must verify( clauses => clauses.forall( seq => seq.multisetEquals( Sequent( Nil, a::c::Nil ) ) ||
                                 seq.multisetEquals( Sequent( Nil, a::d::Nil ) ) ||
                                 seq.multisetEquals( Sequent( Nil, b::c::Nil ) ) ||
                                 seq.multisetEquals( Sequent( Nil, b::d::Nil ) ) ) )
    }
  }
  */
}
