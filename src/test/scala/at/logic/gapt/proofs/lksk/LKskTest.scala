/*
 * LKskTest.scala
 *
 */

package at.logic.gapt.proofs.lksk

import at.logic.gapt.proofs.HOLSequent
import org.specs2.mutable._

import at.logic.gapt.expr._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lkOld.{ OrLeftRule, Axiom => LKAxiom, _ }
import TypeSynonyms._
import at.logic.gapt.proofs.occurrences.FOFactory

class LKskTest extends Specification {
  val c1 = Var( "a", Ti -> To )
  val v1 = Var( "x", Ti )
  val f1 = HOLAtom( c1, v1 :: Nil )
  val c2 = Var( "b", Ti -> To )
  val v2 = Var( "c", Ti )
  val f2 = HOLAtom( c1, v1 :: Nil )
  val f3 = HOLAtom( Var( "e", To ) )
  val ax = Axiom.createDefault( new HOLSequent( f1 :: Nil, f1 :: Nil ), Tuple2( ( EmptyLabel() + f2 ) :: Nil, EmptyLabel() :: Nil ) )
  val a1 = ax._1 // Axiom return a pair of the proof and a mapping and we want only the proof here
  val a2 = ( Axiom.createDefault( new HOLSequent( f1 :: Nil, f1 :: Nil ), Tuple2( ( EmptyLabel() + f2 ) :: Nil, ( EmptyLabel() + f3 ) :: Nil ) ) )._1

  "The factories/extractors for LKsk" should {
    "work for Axioms" in {
      "- Formula occurrences have correct formulas" in {
        a1.root.antecedent.head must beLike { case o: LabelledFormulaOccurrence => ok }
        a1.root.antecedent.head.factory must beLike { case o: FOFactory => ok }
        a1 must beLike { case Axiom( o ) => o.antecedent.toArray.apply( 0 ).formula == f1 && o.succedent.toArray.apply( 0 ).formula == f1 must_== true }
      }
    }
    "work for OrLeftRule" in {
      val a = OrLeftRule( a1, a2, f1, f2 )
      a.prin.head.factory must beLike { case o: FOFactory => ok }
      a.prin.head must beLike { case o: LabelledFormulaOccurrence => ok }
    }
  }
}
