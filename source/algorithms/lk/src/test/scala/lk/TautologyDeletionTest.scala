/** 
 * Description: 
**/

package at.logic.algorithms.misc

import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher

import at.logic.language.hol.propositions._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.calculi.lk.base.Sequent
import scala.collection.immutable.EmptySet

class TautologyDeletionTest extends SpecificationWithJUnit {
  "TautologyDeletion" should {
    "correctly delete tautologous sequents" in {
      val a = HOLVarFormula( "a" )
      val b = HOLVarFormula( "b" )
      val s1 = Sequent( a::Nil, a::Nil )
      val s2 = Sequent( b::a::b::Nil, b::b::b::a::b::Nil )
      val s3 = Sequent( a::Nil, b::Nil )
      val s4 = Sequent( b::Nil, a::Nil )
      val list = s1::s2::s3::s4::Nil
      val dlist = deleteTautologies( list )
      dlist.size must beEqual( 2 )
    }
  }
}
