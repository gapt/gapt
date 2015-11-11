package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.base.beSyntacticFSequentEqual
import at.logic.gapt.proofs.{ Suc, Ant }
import org.specs2.mutable._

class ReductiveCutEliminationTest extends Specification {

  "rank-reduction on strong quantifier rules" in {
    val p = FOLAtomConst( "p", 1 )
    val q = FOLAtom( "q" )
    val x = FOLVar( "x" )

    val proof = ( ProofBuilder
      c LogicalAxiom( p( x ) )
      c LogicalAxiom( q )
      b ( ImpLeftRule( _, Suc( 0 ), _, Ant( 0 ) ) )
      u ( ForallLeftRule( _, Ant( 0 ), p( x ) --> q, x, x ) )
      u ( ExistsLeftRule( _, Ant( 1 ), x, x ) )

      c LogicalAxiom( q )
      c LogicalAxiom( p( x ) )
      b ( ImpLeftRule( _, Suc( 0 ), _, Ant( 0 ) ) )

      b ( CutRule( _, Suc( 0 ), _, Ant( 1 ) ) ) qed )

    val proof_ = ReductiveCutElimination( proof )

    proof_.endSequent must beSyntacticFSequentEqual( proof.endSequent )
  }

}
