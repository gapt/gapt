/*
 * SimpleHOLParser.scala
 *
 */

package at.logic.gapt.proofs.shlk

import java.io.InputStreamReader

import at.logic.gapt.formats.shlk_parsing.SHLK
import at.logic.gapt.expr._
import at.logic.gapt.expr.schema._
import at.logic.gapt.proofs.lkOld._
import org.specs2.execute.Success
import org.specs2.mutable._

class SimpleSLKParserTest extends Specification {
  "SimpleSLKParser" should {

    "parse correctly a SLK-proof" in {
      val var3 = SchemaAtom( Var( "x3", To ), Nil )
      val var4 = SchemaAtom( Var( "x4", To ), Nil )
      val ax1 = Axiom( var3 :: Nil, var3 :: Nil )
      val ax2 = Axiom( var4 :: Nil, var4 :: Nil )
      val negl = NegLeftRule( ax1, var3 )
      val proof = OrLeftRule( negl, ax2, var3, var4 )

      val A0 = IndexedPredicate( "A", IntZero() )
      val i = IntVar( "i" )
      val Ai2 = IndexedPredicate( "A", Succ( Succ( i ) ) )
      val Ai = IndexedPredicate( "A", Succ( i ) )
      val f1 = And( A0, BigAnd( i, Ai, IntZero(), Succ( i ) ) )
      val ax11 = Axiom( A0 :: Nil, A0 :: Nil )

      val s = new InputStreamReader( getClass.getClassLoader.getResourceAsStream( "shlk-adder.lks" ) )

      val map = SHLK.parseProof( s )

      Success()

    }
  }
}
