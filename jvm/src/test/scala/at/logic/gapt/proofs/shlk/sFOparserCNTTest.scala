/*
* sFOParserCNTTest.scala
*
*/

package at.logic.gapt.proofs.shlk

import java.io.InputStreamReader

import at.logic.gapt.formats.shlk_parsing.sFOParserCNT
import at.logic.gapt.expr._
import at.logic.gapt.expr.schema._
import at.logic.gapt.proofs.lkOld._
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import org.specs2.execute.Success
import org.specs2.mutable._

class sFOparserCNTTest extends Specification {
  "sFOparserCNT" should {

    "parse correctly David's proof " in {
      skipped( "has eigenvariable condition errors" )

      val A0 = IndexedPredicate( "A", IntZero() )
      val i = IntVar( "i" )
      val k = IntVar( "k" )
      val Ai2 = IndexedPredicate( "A", Succ( Succ( i ) ) )
      val Ai = IndexedPredicate( "A", Succ( i ) )
      val f1 = And( A0, BigAnd( i, Ai, IntZero(), Succ( i ) ) )
      val ax11 = Axiom( A0 :: Nil, A0 :: Nil )

      val s = new InputStreamReader( getClass.getClassLoader.getResourceAsStream( "David.lks" ) )

      val map = sFOParserCNT.parseProof( s )

      val p1 = map.get( "\\mu" ).get._2.get( "root" ).get
      val p2 = map.get( "\\rho" ).get._2.get( "root" ).get
      val p3 = map.get( "\\zeta" ).get._2.get( "root" ).get
      val p4 = map.get( "\\omega" ).get._2.get( "root" ).get
      val p5 = map.get( "\\xi" ).get._2.get( "root" ).get
      val p6 = map.get( "\\varphi" ).get._2.get( "root" ).get

      val cc2: FormulaOccurrence = p2.root.antecedent.tail.tail.head
      val cc_zeta_1: FormulaOccurrence = p3.root.succedent.head
      val cc_zeta_2: FormulaOccurrence = p3.root.antecedent.tail.tail.head
      val cc4: FormulaOccurrence = p4.root.succedent.head
      val cc_xi_1: FormulaOccurrence = p5.root.antecedent.last
      val cc_xi_2: FormulaOccurrence = p5.root.succedent.head
      val cc_xi_3: FormulaOccurrence = p5.root.antecedent.tail.head
      val cc6 = p6.root.antecedent.tail.head :: p6.root.antecedent.last :: Nil

      Success()

    }
  }
}

