package at.logic.gapt.examples

import at.logic.gapt.expr.FOLAtom
import at.logic.gapt.proofs.ceres.Projections
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base.LKProof
import at.logic.gapt.proofs.lkNew.lkOld2New

object philsci {
  def apply(): ( LKProof, LKProof ) = {
    val p1 = FOLAtom( "B" )
    val p2 = FOLAtom( "A" )
    val q = FOLAtom( "C" )
    val r1 = Axiom( p1 :: Nil, p1 :: Nil )
    val r1_ = Axiom( p1 :: Nil, p1 :: Nil )
    val r2 = Axiom( p2 :: Nil, p2 :: Nil )
    val r3 = Axiom( q :: Nil, q :: Nil )
    val r4 = OrLeftRule( r2, r1, r2.root.antecedent( 0 ), r1.root.antecedent( 0 ) )
    val r5 = NegLeftRule( r4, r4.root.succedent( 1 ) )
    val r6 = ImpRightRule( r5, r5.root.antecedent( 1 ), r5.root.succedent( 0 ) )

    val r7 = NegLeftRule( r1_, r1_.root.succedent( 0 ) )
    val r8 = NegRightRule( r7, r7.root.antecedent( 0 ) )
    val r9 = WeakeningLeftRule( r3, p2 )
    val r10 = ImpLeftRule( r8, r9, r8.root.succedent( 0 ), r9.root.antecedent( 1 ) )
    val r11 = CutRule( r6, r10, r6.root.succedent( 0 ), r10.root.antecedent( 2 ) )

    val proj = Projections( lkOld2New( r11 ) ).toList
    //TODO: switch to CERES
    //    val acnf1 = CutRule( proj( 0 ), proj( 1 ), proj( 0 ).root.succedent( 1 ), proj( 1 ).root.antecedent( 0 ) )
    //    val acnf2 = ContractionLeftRule( acnf1, acnf1.root.antecedent( 2 ), acnf1.root.antecedent( 4 ) )
    //    val acnf3 = ContractionRightRule( acnf2, acnf2.root.succedent( 1 ), acnf2.root.succedent( 2 ) )
    //    val acnf4 = ContractionLeftRule( acnf3, acnf3.root.antecedent( 0 ), acnf3.root.antecedent( 3 ) )
    //    val acnf5 = ContractionLeftRule( acnf4, acnf4.root.antecedent( 0 ), acnf4.root.antecedent( 1 ) )
    //( r11, acnf5 )
    ( r11, r11 )
  }

}
