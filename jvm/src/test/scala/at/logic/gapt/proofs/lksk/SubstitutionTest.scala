package at.logic.gapt.proofs.lksk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lksk.TypeSynonyms._
import at.logic.gapt.proofs.lksk._
import org.specs2.mutable._

class SubstitutionTest extends Specification {
  "Substitutions" should {
    val f = Const( "f", Ti -> Ti )
    val y = Var( "y", Ti )
    val x = Var( "x", Ti )
    val a = Var( "a", Ti )
    val fa = App( f, a )
    val R = Const( "R", Ti -> ( Ti -> To ) )
    val Rafa = HOLAtom( R, a :: fa :: Nil )
    val exyRay = Ex( y, HOLAtom( R, a :: y :: Nil ) )
    val allxexy = All( x, Ex( y, HOLAtom( R, x :: y :: Nil ) ) )

    val ax = Axiom.createDefault( new HOLSequent( Rafa :: Nil, Rafa :: Nil ), Tuple2( ( EmptyLabel() + a ) :: Nil, EmptyLabel() :: Nil ) )
    val r1 = ExistsSkLeftRule( ax._1, ax._2._1.head, exyRay, fa )
    val r2 = ForallSkLeftRule( r1, r1.prin.head, allxexy, a, true )
    r2.root.antecedent.toList.head must beLike { case o: LabelledFormulaOccurrence => ok }
    r2.root.succedent.toList.head must beLike { case o: LabelledFormulaOccurrence => ok }

    "work for an axiom" in {
      val P = Const( "P", Ti -> To )
      val Px = HOLAtom( P, x :: Nil )
      val c: LambdaExpression = Const( "c", Ti )
      val Pc = HOLAtom( P, c :: Nil )

      val a = Axiom.createDefault( new HOLSequent( Px :: Nil, Px :: Nil ), Tuple2( ( EmptyLabel() + x ) :: Nil, ( EmptyLabel() + y ) :: Nil ) )
      val subst = Substitution( x, c )
      val r = applySubstitution( a._1, subst )
      r._1.root.succedent.toList.head must beLike { case o: LabelledFormulaOccurrence => o.skolem_label == ( EmptyLabel() + y ) && o.formula == Pc must_== true }
      r._1.root.antecedent.toList.head must beLike { case o: LabelledFormulaOccurrence => o.skolem_label == ( EmptyLabel() + c ) && o.formula == Pc must_== true }
    }

    "apply correctly to a simple proof" in {
      val c = Const( "c", Ti )
      val g = Const( "g", Ti -> Ti )
      val gc = App( g, c )
      val fgc = App( f, gc )
      val R = Const( "R", Ti -> ( Ti -> To ) )
      val Rgcfgc = HOLAtom( R, gc :: fgc :: Nil )
      val exyRgcy = Ex( y, HOLAtom( R, gc :: y :: Nil ) )
      val subst = Substitution( a, gc ) // a <- g(c)

      val p_s = applySubstitution( r2, subst )
      p_s._1.root.antecedent.toList.head must beLike { case o: LabelledFormulaOccurrence => o.skolem_label == EmptyLabel() && o.formula == allxexy must_== true }
      p_s._1.root.succedent.toList.head must beLike { case o: LabelledFormulaOccurrence => o.skolem_label == EmptyLabel() && o.formula == Rgcfgc must_== true }
    }
  }
}
