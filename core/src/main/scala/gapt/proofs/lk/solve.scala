package gapt.proofs.lk

import gapt.expr._
import gapt.proofs._
import gapt.proofs.context.mutable.MutableContext
import gapt.provers.OneShotProver
import gapt.utils.Maybe

object LKProver extends OneShotProver {
  def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = solvePropositional( seq ).toOption
}

object EquationalLKProver extends OneShotProver {
  def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = solveQuasiPropositional( seq ).toOption
}

object AtomicExpansion {

  def apply( f: Formula ): LKProof = f match {
    case a: Atom     => LogicalAxiom( a )

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
      ( AtomicExpansion( proof.A ), SequentConnector( proof.endSequent ) )
  }.apply( p, () )

}
