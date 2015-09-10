/*
 * SimpleResolutionParserTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.formats.simple

import at.logic.gapt.proofs.HOLSequent
import org.specs2.mutable._
import at.logic.gapt.expr._
import at.logic.gapt.formats.readers.StringReader
import at.logic.gapt.proofs.resolutionOld._
import at.logic.gapt.expr._

class SimpleResolutionParserTest extends Specification {
  //  private class MyParser(input: String) extends StringReader(input) with SimpleResolutionParserHOL
  private class MyParser2( input: String ) extends StringReader( input ) with SimpleResolutionParserFOL

  val pa = HOLAtom( Const( "p", Ti -> To ), Const( "a", Ti ) :: Nil )
  val pfx = HOLAtom( Const( "p", Ti -> To ), HOLFunction( Const( "f", Ti -> Ti ), Var( "x", Ti ) :: Nil ) :: Nil )
  val px = HOLAtom( Const( "p", Ti -> To ), Var( "x", Ti ) :: Nil )
  val pffa = HOLAtom( Const( "p", Ti -> To ), HOLFunction( Const( "f", Ti -> Ti ), HOLFunction( Const( "f", Ti -> Ti ), Const( "a", Ti ) :: Nil ) :: Nil ) :: Nil )

  val pa_fol = FOLAtom( "P", FOLConst( "a" ) :: Nil )
  val pfx_fol = FOLAtom( "P", FOLFunction( "f", FOLVar( "x" ) :: Nil ) :: Nil )
  val px_fol = FOLAtom( "P", FOLVar( "x" ) :: Nil )
  val pffa_fol = FOLAtom( "P", FOLFunction( "f", FOLFunction( "f", FOLConst( "a" ) :: Nil ) :: Nil ) :: Nil )

  def clause_to_lists( cl: OccClause ): ( Seq[HOLFormula], Seq[HOLFormula] ) = ( cl.negative map ( _.formula ), cl.positive map ( _.formula ) )

  "SimpleResolutionParser" should {
    /*
    "return an empty clause when given ." in {
      (new MyParser(".").getClauseList) must beEqualTo (Clause(Nil,Nil)::Nil)
    }
    "return an empty list when given nothing" in {
      (new MyParser("").getClauseList) must beEqualTo (Nil)
    }
    "return the correct clause of p(a)." in {
      (new MyParser("p(a:i).").getClauseList) must beEqualTo (Clause(Nil,pa::Nil)::Nil)
    }
    "return the correct clause of p(f(x))." in {
      (new MyParser("p(f(x:i):i).").getClauseList) must beEqualTo (Clause(Nil,pfx::Nil)::Nil)
    }
    "return the correct clause of -p(x)." in {
      (new MyParser("-p(x:i).").getClauseList) must beEqualTo (Clause(px::Nil,Nil)::Nil)
    }
    "return the correct clause of -p(x) | p(f(x))" in {
      (new MyParser("-p(x:i) | p(f(x:i):i).").getClauseList) must beEqualTo (Clause(px::Nil,pfx::Nil)::Nil)
    }
    "return the correct clauses for p(a). -p(x) | p(f(x)). -p(f(f(a)))." in {
      (new MyParser("p(a:i). -p(x:i) | p(f(x:i):i). -p(f(f(a:i):i):i).").getClauseList) must beEqualTo (Clause(Nil,pa::Nil)::Clause(px::Nil,pfx::Nil)::Clause(pffa::Nil,Nil)::Nil)
    }
    */
    "return an empty clause when given ." in {
      ( new MyParser2( "." ).getClauseList ) must beEqualTo( Seq( HOLSequent( Nil, Nil ) ) )
    }
    "return an empty list when given nothing" in {
      ( new MyParser2( "" ).getClauseList ) must beEqualTo( Nil )
    }
    "return the correct clause of -p(x). fol" in {
      ( new MyParser2( "-P(x)." ).getClauseList ) must beEqualTo( Seq( HOLSequent( px_fol :: Nil, Nil ) ) )
    }
    "return the correct clauses for p(a). -p(x) | p(f(x)). -p(f(f(a))). in fol" in {
      ( new MyParser2( "P(a). -P(x) | P(f(x)). -P(f(f(a)))." ).getClauseList ) must beEqualTo( Seq( HOLSequent( Nil, pa_fol :: Nil ), HOLSequent( px_fol :: Nil, pfx_fol :: Nil ), HOLSequent( pffa_fol :: Nil, Nil ) ) )
    }
    /*
    "return the correct clause for p(x) | -p(x) in hol" in {
      (new MyParser("p(x:i) | -p(x:i).").getClauseList) must beEqualTo (Clause(px::Nil,px::Nil)::Nil)
    }*/
    "return the correct clause for p(x) | -p(x) in fol" in {
      ( new MyParser2( "P(x) | -P(x)." ).getClauseList ) must beEqualTo( Seq( HOLSequent( px_fol :: Nil, px_fol :: Nil ) ) )
    }

    /*
    "manage to parse a complex term" in {
      val str = """p(x_10:i,m(x_3:i,m(m(p(x_4:i,one:i):i,p(x_5:i,one:i):i):i):i):i):i"""
      (new MyParser("e("+str+","+str+").").getClauseList) mustNot throwA [Exception]
    }*/
  }
}

