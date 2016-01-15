package at.logic.gapt.examples

import at.logic.gapt.expr.FOLAtom
import at.logic.gapt.proofs.{ Suc, Ant }
import at.logic.gapt.proofs.ceres.Projections
import at.logic.gapt.proofs.lk._

object philsci {
  def apply(): ( LKProof, LKProof ) = {
    val p1 = FOLAtom( "B" )
    val p2 = FOLAtom( "A" )
    val q = FOLAtom( "C" )
    val r1 = LogicalAxiom( p1 )
    val r2 = LogicalAxiom( p2 )
    val r3 = LogicalAxiom( q )
    val r4 = OrLeftRule( r2, Ant( 0 ), r1, Ant( 0 ) )
    val r5 = NegLeftRule( r4, Suc( 1 ) )
    val r6 = ImpRightRule( r5, Ant( 0 ), Suc( 0 ) )

    val r7 = NegLeftRule( r1, Suc( 0 ) )
    val r8 = NegRightRule( r7, Ant( 1 ) )
    val r9 = WeakeningLeftRule( r3, p2 )
    val r10 = ImpLeftRule( r8, Suc( 0 ), r9, Ant( 0 ) )
    val r11 = CutRule( r6, Suc( 0 ), r10, Ant( 0 ) )

    val proj = Projections( r11 ).toList
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
