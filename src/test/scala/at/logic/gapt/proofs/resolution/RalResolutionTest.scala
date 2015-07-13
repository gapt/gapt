package at.logic.gapt.proofs.resolution.ral

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.base.HOLSequent
import at.logic.gapt.proofs.lksk.LabelledOccSequent
import at.logic.gapt.proofs.lksk.TypeSynonyms.{ Label, EmptyLabel }
import at.logic.gapt.expr.hol._
import org.specs2.mutable._

/**
 * Created by marty on 9/10/14.
 */
class RalResolutionTest extends Specification {
  "Ral resolution" should {
    "work on simple proofs" in {
      val x = Var( "X", To )
      val p = HOLAtom( Const( "P", To ), Nil )
      val exx = Ex( x, x.asInstanceOf[HOLFormula] )
      val root = HOLSequent( Nil, List( exx ) )
      val labels: ( List[Label], List[Label] ) = ( List[Label](), List[Label]( EmptyLabel() ) )

      val i1 = InitialSequent( root, labels )
      val i2 = ForallT( i1, i1.root.l_succedent( 0 ), x )
      val i3 = Sub( i2, Substitution( x, And( p, Neg( p ) ) ) )
      val i4 = AndT1( i3, i3.root.l_succedent( 0 ) )
      val i5 = AndT2( i3, i3.root.l_succedent( 0 ) )
      val i6 = NegT( i5, i5.root.l_succedent( 0 ) )
      val i7 = Cut( i4, i6, List( i4.root.l_succedent( 0 ) ), List( i6.root.l_antecedent( 0 ) ) )

      i7.root.toHOLSequent must_== ( HOLSequent( Nil, Nil ) )
      ok
    }

    "work on non-idempotent substitutions" in {
      val x = Var( "x", Ti )
      val fx = HOLFunction( Const( "f", Ti -> Ti ), x :: Nil )
      val px = HOLAtom( Const( "P", Ti -> To ), List( x ) )
      val pfx = HOLAtom( Const( "P", Ti -> To ), List( fx ) )

      val sub = Substitution( x, fx )

      val root = HOLSequent( Nil, List( px ) )
      val labels: ( List[Label], List[Label] ) = ( List[Label](), List[Label]( EmptyLabel() ) )

      val i1 = InitialSequent( root, labels )
      val i2 = Sub( i1, sub )
      i2.root.succedent( 0 ).formula must_== ( pfx )
      ok
    }
  }

}
