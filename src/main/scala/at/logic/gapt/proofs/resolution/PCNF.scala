package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr.hol._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.{ applySubstitution => applySub }
import at.logic.gapt.proofs.lk.base.{ HOLSequent, LKProof }
import at.logic.gapt.proofs.resolution.robinson.RobinsonResolutionProof

/**
 * Given a formula f and a clause a in CNF(-f), PCNF computes a proof of s o a (see logic.at/ceres for the definition of o)
 * Note about checking containment up to variables renaming:
 * we compute the variable renaming from the lk proof to the resolution proof for a specific clause. We cannot apply it to the formula in s
 * as it might be quantified over this variables so we apply it to the resulted lk proof. We must apply it as otherwise the substitution in
 * the resolution to lk transformation will not be applied to these clauses. In the weakenings application at the end of this method we try
 * to apply it to the formulas as well as if it is quantified over these variables, it will be also quantified in the proof so no damage
 * done.
 */
case class ResolutionException( msg: String, proofs: List[RobinsonResolutionProof], clauses: List[HOLClause] )
  extends Exception( "Resolution Exception: " + msg )

object PCNF {
  /**
   * @param s a sequent not containing strong quantifiers
   * @param a a clause in the CNF of -s
   * @return an LK proof of s o a (see logic.at/ceres for the definition of o)
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
            ( applySub( PCNFp( f3, a, subi ), sub )._1, f3, true )
          }
          case _ => {
            val f3 = s.succedent.find( x => containsMatchingClause( f2, CNFn.toFClauseList( x ) ) ).get
            ( applySub( PCNFn( f3, a, subi ), sub )._1, f3, false )
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
              case _         => throw new ResolutionException( "Clause [" + a.toString + "] is not reflexivity and not contained in CNF(-s) [" + nLine + cnf.mkString( ";" + nLine ) + nLine + "]", Nil, a :: cnf.toList )
            }
        }
    }

    ContractionMacroRule( p, s compose a, strict = false )
  }

  def containsMatchingClause( what: HOLClause, where: List[HOLClause] ): Boolean = {
    //TODO: check for symmetry applications during prover9's cnf construction
    where.find( _ equals what ).isDefined
  }

  /**
   * assuming a in CNF^-^(f) we give a proof of a o (|- f)
   * @param f
   * @param a
   * @return
   */
  private def PCNFn( f: HOLFormula, a: HOLClause, sub: Substitution ): LKProof = f match {
    case Top()     => Axiom( Nil, List( f ) )
    case Neg( f2 ) => NegRightRule( PCNFp( f2, a, sub ), f2 )
    case And( f1, f2 ) => {
      AndRightRule( PCNFn( f1, a, sub ), PCNFn( f2, a, sub ), f1, f2 )
    }
    case Or( f1, f2 ) =>
      if ( containsSubsequent( CNFn.toFClauseList( f1 ), as( a, sub ) ) ) OrRight1Rule( PCNFn( f1, a, sub ), f1, f2 )
      else if ( containsSubsequent( CNFn.toFClauseList( f2 ), as( a, sub ) ) ) OrRight2Rule( PCNFn( f2, a, sub ), f1, f2 )
      else throw new IllegalArgumentException( "clause: " + as( a, sub ) + " is not found in CNFs of ancestors: "
        + CNFn.toFClauseList( f1 ) + " or " + CNFn.toFClauseList( f2 ) + " of formula " + f )
    case Imp( f1, f2 ) => {
      if ( containsSubsequent( CNFp.toClauseList( f1 ), as( a, sub ) ) ) ImpRightRule( WeakeningRightRule( PCNFp( f1, a, sub ), f2 ), f1, f2 )
      else if ( containsSubsequent( CNFn.toFClauseList( f2 ), as( a, sub ) ) ) ImpRightRule( WeakeningLeftRule( PCNFn( f2, a, sub ), f1 ), f1, f2 )
      else throw new IllegalArgumentException( "clause: " + as( a, sub ) + " is not found in CNFs of ancestors: "
        + CNFp.toClauseList( f1 ) + " or " + CNFn.toFClauseList( f2 ) + " of formula " + f )
    }
    case Ex( v, f2 )     => ExistsRightRule( PCNFn( f2, a, sub ), f2, f, v.asInstanceOf[Var] )
    case HOLAtom( _, _ ) => Axiom( List( f ), List( f ) )
    case _               => throw new IllegalArgumentException( "unknown head of formula: " + a.toString )
  }

  /**
   * assuming a in CNF^+^(f) we give a proof of a o (f |-)
   * @param f
   * @param a
   * @return
   */
  private def PCNFp( f: HOLFormula, a: HOLClause, sub: Substitution ): LKProof = f match {
    case Bottom()  => Axiom( List( f ), Nil )
    case Neg( f2 ) => NegLeftRule( PCNFn( f2, a, sub ), f2 )
    case And( f1, f2 ) =>
      if ( containsSubsequent( CNFp.toClauseList( f1 ), as( a, sub ) ) ) AndLeft1Rule( PCNFp( f1, a, sub ), f1, f2 )
      else if ( containsSubsequent( CNFp.toClauseList( f2 ), as( a, sub ) ) ) AndLeft2Rule( PCNFp( f2, a, sub ), f1, f2 )
      else throw new IllegalArgumentException( "clause: " + as( a, sub ) + " is not found in CNFs of ancestors: "
        + CNFp.toClauseList( f1 ) + " or " + CNFp.toClauseList( f2 ) + " of formula " + f )
    case Or( f1, f2 ) => {
      OrLeftRule( PCNFp( f1, a, sub ), PCNFp( f2, a, sub ), f1, f2 )
    }
    case Imp( f1, f2 ) => {
      ImpLeftRule( PCNFn( f1, a, sub ), PCNFp( f2, a, sub ), f1, f2 )
    }
    case All( v, f2 )    => ForallLeftRule( PCNFp( f2, a, sub ), f2, f, v.asInstanceOf[Var] )
    case HOLAtom( _, _ ) => Axiom( List( f ), List( f ) )
    case _               => throw new IllegalArgumentException( "unknown head of formula: " + a.toString )
  }

  def getVariableRenaming( f1: HOLClause, f2: HOLClause ): Option[Substitution] = {
    if ( f1.negative.size != f2.negative.size || f1.positive.size != f2.positive.size ) None
    else {
      val pairs = ( f1.negative.asInstanceOf[Seq[LambdaExpression]].zip( f2.negative.asInstanceOf[Seq[LambdaExpression]] )
        ++ f1.positive.asInstanceOf[Seq[LambdaExpression]].zip( f2.positive.asInstanceOf[Seq[LambdaExpression]] ) )
      try {
        val sub = pairs.foldLeft( Substitution() )( ( sb, p ) => Substitution( sb.map ++ computeSub( p ).map ) )
        if ( pairs.forall( p => sub( p._1 ) == p._2 ) ) Some( sub ) else None
      } catch {
        case e: Exception => None
      }
    }
  }
  def computeSub( p: ( LambdaExpression, LambdaExpression ) ): Substitution = ( p._1, p._2 ) match {
    case ( Var( a, _ ), Var( b, _ ) ) if a == b => Substitution()
    case ( v1: Var, v2: Var )                   => Substitution( v1, v2 )
    case ( c1: Const, c2: Const )               => Substitution()
    case ( App( a1, b1 ), App( a2, b2 ) ) =>
      val s1 = computeSub( a1, a2 )
      val s2 = computeSub( b1, b2 )
      Substitution( s1.map ++ s2.map )
    case ( Abs( v1, a1 ), Abs( v2, a2 ) ) => Substitution( computeSub( a1, a2 ).map - v1 )
    case _                                => throw new Exception()
  }

  def containsSubsequent( set: List[HOLClause], fc: HOLClause ): Boolean = {
    val fs = fc
    val r = set.filter( x => ( x diff fs ).isEmpty )
    r.nonEmpty
  }

  // applying sub to a clause
  def as( a: HOLClause, sub: Substitution ): HOLClause = HOLClause( a.negative.map( f => sub( f ) ), a.positive.map( f => sub( f ) ) )
}

