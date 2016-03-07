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

  def apply( p: LKProof ): LKProof = p match {
    case ReflexivityAxiom( _ ) | TopAxiom | BottomAxiom | TheoryAxiom( _ ) => p
    case LogicalAxiom( f ) => apply( f )

    //structural rules
    case ContractionLeftRule( subProof, aux1, aux2 ) => ContractionLeftRule( apply( subProof ), aux1, aux2 )
    case ContractionRightRule( subProof, aux1, aux2 ) => ContractionRightRule( apply( subProof ), aux1, aux2 )

    case WeakeningLeftRule( subProof, main ) => WeakeningLeftRule( apply( subProof ), main )
    case WeakeningRightRule( subProof, main ) => WeakeningRightRule( apply( subProof ), main )

    case CutRule( subProof1, aux1, subProof2, aux2 ) => CutRule( apply( subProof1 ), aux1, apply( subProof2 ), aux2 )

    //Unary Logical rules
    case NegLeftRule( subProof, aux ) => NegLeftRule( apply( subProof ), aux )
    case NegRightRule( subProof, aux ) => NegRightRule( apply( subProof ), aux )

    case ImpRightRule( subProof, aux1, aux2 ) => ImpRightRule( apply( subProof ), aux1, aux2 )
    case OrRightRule( subProof, aux1, aux2 ) => OrRightRule( apply( subProof ), aux1, aux2 )
    case AndLeftRule( subProof, aux1, aux2 ) => AndLeftRule( apply( subProof ), aux1, aux2 )

    //Binary Logical Rules
    case ImpLeftRule( subProof1, aux1, subProof2, aux2 ) => ImpLeftRule( apply( subProof1 ), aux1, apply( subProof2 ), aux2 )
    case OrLeftRule( subProof1, aux1, subProof2, aux2 ) => OrLeftRule( apply( subProof1 ), aux1, apply( subProof2 ), aux2 )
    case AndRightRule( subProof1, aux1, subProof2, aux2 ) => AndRightRule( apply( subProof1 ), aux1, apply( subProof2 ), aux2 )

    //Quantifier Rules
    case ForallLeftRule( subProof, aux, formula, term, v ) => ForallLeftRule( apply( subProof ), aux, formula, term, v )
    case ExistsRightRule( subProof, aux, formula, term, v ) => ExistsRightRule( apply( subProof ), aux, formula, term, v )

    case ForallRightRule( subProof, aux, eigen, quant ) => ForallRightRule( apply( subProof ), aux, eigen, quant )
    case ExistsLeftRule( subProof, aux, eigen, quant ) => ExistsLeftRule( apply( subProof ), aux, eigen, quant )

    //equality and definitions
    case EqualityLeftRule( subProof, eq, aux, pos ) => EqualityLeftRule( apply( subProof ), eq, aux, pos )
    case EqualityRightRule( subProof, eq, aux, pos ) => EqualityRightRule( apply( subProof ), eq, aux, pos )

    case DefinitionLeftRule( subProof, aux, main ) => DefinitionLeftRule( apply( subProof ), aux, main )
    case DefinitionRightRule( subProof, aux, main ) => DefinitionRightRule( apply( subProof ), aux, main )

    case InductionRule( cases, main ) => InductionRule( cases map { c => c.copy( apply( c.proof ) ) }, main )
  }

}
