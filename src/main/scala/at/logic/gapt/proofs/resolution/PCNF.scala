package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs.lkNew._
import at.logic.gapt.proofs.{ Sequent, HOLClause, HOLSequent }

/**
 * Given a sequent s and a clause a in CNF(-s), PCNF computes an LK proof of s ++ a
 *
 * Note about checking containment up to variables renaming:
 * we compute the variable renaming from the lk proof to the resolution proof for a specific clause. We cannot apply it to the formula in s
 * as it might be quantified over this variables so we apply it to the resulted lk proof. We must apply it as otherwise the substitution in
 * the resolution to lk transformation will not be applied to these clauses. In the weakenings application at the end of this method we try
 * to apply it to the formulas as well as if it is quantified over these variables, it will be also quantified in the proof so no damage
 * done.
 */
object PCNF {
  /**
   * @param s a sequent not containing strong quantifiers
   * @param a a clause in the CNF of -s
   * @return an LK proof of s ++ a
   */
  def apply( s: HOLSequent, a: HOLClause ): LKProof = {

    // compute formula
    val form = if ( s.antecedent.nonEmpty )
      s.succedent.foldLeft( s.antecedent.reduceLeft( ( f1, f2 ) => And( f1, f2 ) ) )( ( f1, f2 ) => And( f1, Neg( f2 ) ) )
    else
      s.succedent.tail.foldLeft( Neg( s.succedent.head ) )( ( f1, f2 ) => And( f1, Neg( f2 ) ) )

    val nLine = sys.props( "line.separator" )

    // compute CNF and confirm a <- CNF(-s) up to variable renaming
    val cnf = CNFp.toClauseList( form )
    var sub = Substitution()
    var subi = Substitution()
    val op = cnf.find( y => ( getVariableRenaming( y, a ), getVariableRenaming( a, y ) ) match {
      case ( Some( s ), Some( si ) ) =>
        sub = s; subi = si; true
      case _ => false
    } )
    val ( p, f, inAntecedent ) = op match {
      case Some( f2 ) => {
        // find the right formula and compute the proof
        s.antecedent.find( x => containsMatchingClause( f2, CNFp.toClauseList( x ) ) ) match {
          case Some( f3 ) => {
            ( applySubstitution( sub )( PCNFp( f3, a, subi ) ), f3, true )
          }
          case _ => {
            val f3 = s.succedent.find( x => containsMatchingClause( f2, CNFn.toFClauseList( x ) ) ).get
            ( applySubstitution( sub )( PCNFn( f3, a, subi ) ), f3, false )
          }
        }
      }
      case None =>
        // check for tautology
        a.positive.find( p => a.negative.exists( n => n == p ) ) match {
          case Some( f ) => ( Axiom( a.negative, a.positive ), f.asInstanceOf[HOLFormula], false )
          case _ =>
            // check for reflexivity
            a.positive.find( f => f match {
              case Eq( a, b ) if a == b => true
              case _                    => false
            } ) match {
              case Some( f ) => ( Axiom( List(), List( f ) ), f.asInstanceOf[HOLFormula], false )
              case _         => throw new IllegalArgumentException( s"Clause [$a] is not reflexivity and not contained in CNF(-s) [${cnf.mkString( ";" + nLine )}]" )
            }
        }
    }

    WeakeningContractionMacroRule( p, s compose a, strict = true )
  }

  def containsMatchingClause( what: HOLClause, where: List[HOLClause] ): Boolean = {
    //TODO: check for symmetry applications during prover9's cnf construction
    where.find( _ equals what ).isDefined
  }

  /**
   * assuming a in CNFn(f) we give a proof of a :+ f
   */
  private def PCNFn( f: HOLFormula, a: HOLClause, sub: Substitution ): LKProof = f match {
    case Top()                  => TopAxiom
    case atom @ HOLAtom( _, _ ) => LogicalAxiom( atom )
    case Neg( f2 )              => NegRightRule( PCNFp( f2, a, sub ), f2 )
    case And( f1, f2 )          => AndRightRule( PCNFn( f1, a, sub ), f1, PCNFn( f2, a, sub ), f2 )
    case Or( f1, f2 ) if containsClauseN( f1, a map { sub( _ ) } ) =>
      OrRightMacroRule( PCNFn( f1, a, sub ), f1, f2 )
    case Or( f1, f2 ) if containsClauseN( f2, a map { sub( _ ) } ) =>
      OrRightMacroRule( PCNFn( f2, a, sub ), f1, f2 )
    case Imp( f1, f2 ) if containsClauseP( f1, a map { sub( _ ) } ) =>
      ImpRightRule( WeakeningRightRule( PCNFp( f1, a, sub ), f2 ), f )
    case Imp( f1, f2 ) if containsClauseN( f2, a map { sub( _ ) } ) =>
      ImpRightRule( WeakeningLeftRule( PCNFn( f2, a, sub ), f1 ), f )
    case Ex( v, f2 ) => ExistsRightRule( PCNFn( f2, a, sub ), f, v )
    case _           => throw new IllegalArgumentException( s"Cannot construct PCNFn of $a from $f under $sub" )
  }

  /**
   * assuming a in CNFp(f) we give a proof of f +: a
   */
  private def PCNFp( f: HOLFormula, a: HOLClause, sub: Substitution ): LKProof = f match {
    case Bottom()               => BottomAxiom
    case atom @ HOLAtom( _, _ ) => LogicalAxiom( atom )
    case Neg( f2 )              => NegLeftRule( PCNFn( f2, a, sub ), f2 )
    case And( f1, f2 ) if containsClauseP( f1, a map { sub( _ ) } ) =>
      AndLeftMacroRule( PCNFp( f1, a, sub ), f1, f2 )
    case And( f1, f2 ) if containsClauseP( f2, a map { sub( _ ) } ) =>
      AndLeftMacroRule( PCNFp( f2, a, sub ), f1, f2 )
    case Or( f1, f2 ) =>
      OrLeftRule( PCNFp( f1, a, sub ), f1, PCNFp( f2, a, sub ), f2 )
    case Imp( f1, f2 ) =>
      ImpLeftRule( PCNFn( f1, a, sub ), f1, PCNFp( f2, a, sub ), f2 )
    case All( v, f2 ) => ForallLeftRule( PCNFp( f2, a, sub ), f, v )
    case _            => throw new IllegalArgumentException( s"Cannot construct PCNFp of $a from $f under $sub" )
  }

  def getVariableRenaming( f1: HOLClause, f2: HOLClause ): Option[Substitution] = syntacticMatching( f1.toFormula, f2.toFormula )

  def containsClauseN( formula: HOLFormula, clause: HOLSequent ): Boolean =
    CNFn.toFClauseList( formula ) exists { _ isSubMultisetOf clause }
  def containsClauseP( formula: HOLFormula, clause: HOLSequent ): Boolean =
    CNFp.toClauseList( formula ) exists { _ isSubMultisetOf clause }

  // applying sub to a clause
  def as( a: HOLClause, sub: Substitution ): HOLClause = HOLClause( a.negative.map( f => sub( f ) ), a.positive.map( f => sub( f ) ) )
}

