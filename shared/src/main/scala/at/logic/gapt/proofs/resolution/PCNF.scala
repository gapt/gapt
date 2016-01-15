package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs._

/**
 * Given a sequent s and a clause a in CNF(-s), PCNF computes an LK proof of a subsequent of s ++ a containing at least a
 */
object PCNF {
  /**
   * @param s a sequent not containing strong quantifiers
   * @param a a clause in the CNF of -s
   * @return an LK proof of a subsequent of s ++ a containing at least a
   */
  def apply( s: HOLSequent, a: HOLClause ): LKProof =
    ( for (
      ( f, idx ) <- s.zipWithIndex.elements;
      cnfClause <- if ( idx isAnt ) CNFp.toClauseList( f ) else CNFn.toFClauseList( f );
      if cnfClause == a
    ) yield {
      val pcnf = if ( idx isAnt ) PCNFp( f, cnfClause ) else PCNFn( f, cnfClause )
      ContractionMacroRule( pcnf, s ++ a, strict = false )
    } ) head

  /**
   * assuming a in CNFn(f) we give a proof of a :+ f
   */
  private def PCNFn( f: HOLFormula, a: HOLClause ): LKProof = f match {
    case Top()                  => TopAxiom
    case atom @ HOLAtom( _, _ ) => LogicalAxiom( atom )
    case Neg( f2 )              => NegRightRule( PCNFp( f2, a ), f2 )
    case And( f1, f2 )          => AndRightRule( PCNFn( f1, a ), f1, PCNFn( f2, a ), f2 )
    case Or( f1, f2 ) if containsClauseN( f1, a ) =>
      OrRightRule( WeakeningRightRule( PCNFn( f1, a ), f2 ), f1, f2 )
    case Or( f1, f2 ) if containsClauseN( f2, a ) =>
      OrRightRule( WeakeningRightRule( PCNFn( f2, a ), f1 ), f1, f2 )
    case Imp( f1, f2 ) if containsClauseP( f1, a ) =>
      ImpRightRule( WeakeningRightRule( PCNFp( f1, a ), f2 ), f )
    case Imp( f1, f2 ) if containsClauseN( f2, a ) =>
      ImpRightRule( WeakeningLeftRule( PCNFn( f2, a ), f1 ), f )
    case Ex( v, f2 ) => ExistsRightRule( PCNFn( f2, a ), f, v )
    case _           => throw new IllegalArgumentException( s"Cannot construct PCNFn of $a from $f" )
  }

  /**
   * assuming a in CNFp(f) we give a proof of f +: a
   */
  private def PCNFp( f: HOLFormula, a: HOLClause ): LKProof = f match {
    case Bottom()               => BottomAxiom
    case atom @ HOLAtom( _, _ ) => LogicalAxiom( atom )
    case Neg( f2 )              => NegLeftRule( PCNFn( f2, a ), f2 )
    case And( f1, f2 ) if containsClauseP( f1, a ) =>
      AndLeftRule( WeakeningLeftRule( PCNFp( f1, a ), f2 ), f1, f2 )
    case And( f1, f2 ) if containsClauseP( f2, a ) =>
      AndLeftRule( WeakeningLeftRule( PCNFp( f2, a ), f1 ), f1, f2 )
    case Or( f1, f2 ) =>
      OrLeftRule( PCNFp( f1, a ), f1, PCNFp( f2, a ), f2 )
    case Imp( f1, f2 ) =>
      ImpLeftRule( PCNFn( f1, a ), f1, PCNFp( f2, a ), f2 )
    case All( v, f2 ) => ForallLeftRule( PCNFp( f2, a ), f, v )
    case _            => throw new IllegalArgumentException( s"Cannot construct PCNFp of $a from $f" )
  }

  def containsClauseN( formula: HOLFormula, clause: HOLSequent ): Boolean =
    CNFn.toFClauseList( formula ) exists { _ isSubMultisetOf clause }
  def containsClauseP( formula: HOLFormula, clause: HOLSequent ): Boolean =
    CNFp.toClauseList( formula ) exists { _ isSubMultisetOf clause }
}

