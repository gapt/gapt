/** 
 * Description: 
**/

package at.logic.transformations.ceres.clauseSets

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import scala.xml._
import scala.io._
import java.io.File.separator
import at.logic.language.hol._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base.Sequent
import at.logic.transformations.ceres.struct._
import java.io.{FileInputStream, InputStreamReader}
import at.logic.algorithms.shlk._

@RunWith(classOf[JUnitRunner])
class ClauseSetsTest extends SpecificationWithJUnit {

  // commented out --- we need to construct formula occurrences, but they
  //   are abstract and the factory is private to LK
  "ClauseSets" should {
    "- transform a Struct into a standard clause set" in {
//      val a = HOLVarFormula( "a" )
//      val b = HOLVarFormula( "b" )
//      val c = HOLVarFormula( "c" )
//      val d = HOLVarFormula( "d" )
//
//      val struct = Times(Plus(A(a), A(b)), Plus(A(c), A(d)))
//      val cs = StandardClauseSet.transformStructToClauseSet( struct ).getSequent
//      cs must verify( clauses => clauses.forall( seq => seq.multisetEquals( Sequent( Nil, a::c::Nil ) ) ||
//                                 seq.multisetEquals( Sequent( Nil, a::d::Nil ) ) ||
//                                 seq.multisetEquals( Sequent( Nil, b::c::Nil ) ) ||
//                                 seq.multisetEquals( Sequent( Nil, b::d::Nil ) ) ) )
      ok
    }
    "test the schematic struct" in {
      val s = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "journal_example.lks"))
      val map = ParseQMON.parseProof(s)
      println(Console.GREEN+"\n\n-------- schematic struct --------\n\n"+Console.RESET)
      val p = map.get("\\varphi").get._2.get("root").get
      println(StructCreators.extract(p))

      ok
    }
  }

}
