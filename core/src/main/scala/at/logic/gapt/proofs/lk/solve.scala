package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.provers.OneShotProver

/**
 * Bottom-up construction of sequent calculus proofs.
 *
 * Currently supports propositional logic as well as proof construction using expansion trees.
 */
object solve {
  /**
   * Main method for solving propositional sequents
   *
   * @param seq: sequent to prove
   * @return a proof if there is one
   */
  def solvePropositional( seq: HOLSequent ): Option[LKProof] =
    at.logic.gapt.proofs.lk.solvePropositional( seq ).toOption

}

object LKProver extends OneShotProver {
  def getLKProof( seq: HOLSequent ): Option[LKProof] = solve.solvePropositional( seq )
}

object AtomicExpansion {

  def apply( fs: HOLSequent ): LKProof =
    WeakeningMacroRule( apply( fs.antecedent intersect fs.succedent head ), fs )

  def apply( f: HOLFormula ): LKProof = f match {
    case a: HOLAtom  => LogicalAxiom( a )

    case Bottom()    => WeakeningRightRule( BottomAxiom, Bottom() )
    case Top()       => WeakeningLeftRule( TopAxiom, Top() )

    case Neg( l )    => NegLeftRule( NegRightRule( apply( l ), Ant( 0 ) ), Suc( 0 ) )

    case And( l, r ) => AndLeftRule( AndRightRule( apply( l ), Suc( 0 ), apply( r ), Suc( 0 ) ), Ant( 0 ), Ant( 1 ) )
    case Or( l, r )  => OrRightRule( OrLeftRule( apply( l ), Ant( 0 ), apply( r ), Ant( 0 ) ), Suc( 0 ), Suc( 1 ) )
    case Imp( l, r ) => ImpRightRule( ImpLeftRule( apply( l ), Suc( 0 ), apply( r ), Ant( 0 ) ), Ant( 1 ), Suc( 0 ) )

    case All( x, l ) => ForallRightRule( ForallLeftRule( apply( l ), Ant( 0 ), l, x, x ), Suc( 0 ), x, x )
    case Ex( x, l )  => ExistsLeftRule( ExistsRightRule( apply( l ), Suc( 0 ), l, x, x ), Ant( 0 ), x, x )
  }

  def apply( p: LKProof ): LKProof = new LKVisitor[Unit] {
    override def visitLogicalAxiom( proof: LogicalAxiom, otherArg: Unit ) =
      ( AtomicExpansion( proof.A ), OccConnector( proof.endSequent ), otherArg )
  }.apply( p, () )

}
