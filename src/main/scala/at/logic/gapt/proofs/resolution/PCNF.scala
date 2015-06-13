package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr.hol._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.{ applySubstitution => applySub }
import at.logic.gapt.proofs.lk.base.{ FSequent, LKProof }
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
case class ResolutionException( msg: String, proofs: List[RobinsonResolutionProof], clauses: List[FClause] )
  extends Exception( "Resolution Exception: " + msg )

object PCNF {
  /**
   * @param s a sequent not containing strong quantifiers
   * @param a a clause in the CNF of -s
   * @return an LK proof of s o a (see logic.at/ceres for the definition of o)
   */
  def apply( s: FSequent, a: FClause ): LKProof = {

    // compute formula
    val form = if ( s.antecedent.nonEmpty )
      s.succedent.foldLeft( s.antecedent.reduceLeft( ( f1, f2 ) => And( f1, f2 ) ) )( ( f1, f2 ) => And( f1, Neg( f2 ) ) )
    else
      s.succedent.tail.foldLeft( Neg( s.succedent.head ) )( ( f1, f2 ) => And( f1, Neg( f2 ) ) )

    // compute CNF and confirm a <- CNF(-s) up to variable renaming
    val cnf = CNFp.toFClauseList( form )
    var sub = Substitution()
    var subi = Substitution()
    val op = cnf.find( y => getVariableRenaming( y, a ) match {
      case Some( s ) => { sub = s; subi = getVariableRenaming( a, y ).get; true }
      case _         => false
    } )
    val ( p, f, inAntecedent ) = op match {
      case Some( f2 ) => {
        // find the right formula and compute the proof
        s.antecedent.find( x => containsMatchingClause( f2, CNFp.toFClauseList( x ) ) ) match {
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
        a.pos.find( p => a.neg.exists( n => n == p ) ) match {
          case Some( f ) => ( Axiom( a.neg, a.pos ), f.asInstanceOf[HOLFormula], false )
          case _ =>
            // check for reflexivity
            a.pos.find( f => f match {
              case Eq( a, b ) if a == b => true
              case _                    => false
            } ) match {
              case Some( f ) => ( Axiom( List(), List( f ) ), f.asInstanceOf[HOLFormula], false )
              case _         => throw new ResolutionException( "Clause [" + a.toString + "] is not reflexivity and not contained in CNF(-s) [\n" + cnf.mkString( ";\n" ) + "\n]", Nil, a :: cnf.toList )
            }
        }
    }

    //val missing_literals = s diff p.root.toFSequent
    val p1 = if ( inAntecedent ) {
      WeakeningMacroRule( p, FSequent( sub( f ) :: Nil, Nil ) compose a.toFSequent )
    } else {
      WeakeningMacroRule( p, FSequent( Nil, sub( f ) :: Nil ) compose a.toFSequent )
    }
    val p2 = ContractionMacroRule( p1, s compose a.toFSequent, strict = false )
    p2

    // apply contractions on the formulas of a, since we duplicate the context on every binary rule
    //introduceContractions(p_,a)
  }

  def containsMatchingClause( what: FClause, where: List[FClause] ): Boolean = {
    //TODO: check for symmetry applications during prover9's cnf construction
    where.find( _ equals what ).isDefined
  }

  def introduceContractions( resp: LKProof, s: FClause ): LKProof = {
    // for each formula F in s, count its occurrences in s and resp and apply contractions on resp until we reach the same number
    val p1 = s.neg.toSet.foldLeft( resp )( ( p, f ) =>
      ( ( 1 ).to( p.root.antecedent.filter( _.formula == f ).size - s.neg.filter( _ == f ).size ) ).foldLeft( p )( ( q, n ) =>
        ContractionLeftRule( q, f.asInstanceOf[HOLFormula] ) ) )
    val p2 = s.pos.toSet.foldLeft( p1 )( ( p, f ) =>
      ( ( 1 ).to( p.root.succedent.filter( _.formula == f ).size - s.pos.filter( _ == f ).size ) ).foldLeft( p )( ( q, n ) =>
        ContractionRightRule( q, f.asInstanceOf[HOLFormula] ) ) )
    p2
  }

  /**
   * assuming a in CNF^-^(f) we give a proof of a o (|- f)
   * @param f
   * @param a
   * @return
   */
  private def PCNFn( f: HOLFormula, a: FClause, sub: Substitution ): LKProof = f match {
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
      if ( containsSubsequent( CNFp.toFClauseList( f1 ), as( a, sub ) ) ) ImpRightRule( WeakeningRightRule( PCNFp( f1, a, sub ), f2 ), f1, f2 )
      else if ( containsSubsequent( CNFn.toFClauseList( f2 ), as( a, sub ) ) ) ImpRightRule( WeakeningLeftRule( PCNFn( f2, a, sub ), f1 ), f1, f2 )
      else throw new IllegalArgumentException( "clause: " + as( a, sub ) + " is not found in CNFs of ancestors: "
        + CNFp.toFClauseList( f1 ) + " or " + CNFn.toFClauseList( f2 ) + " of formula " + f )
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
  private def PCNFp( f: HOLFormula, a: FClause, sub: Substitution ): LKProof = f match {
    case Bottom()  => Axiom( List( f ), Nil )
    case Neg( f2 ) => NegLeftRule( PCNFn( f2, a, sub ), f2 )
    case And( f1, f2 ) =>
      if ( containsSubsequent( CNFp.toFClauseList( f1 ), as( a, sub ) ) ) AndLeft1Rule( PCNFp( f1, a, sub ), f1, f2 )
      else if ( containsSubsequent( CNFp.toFClauseList( f2 ), as( a, sub ) ) ) AndLeft2Rule( PCNFp( f2, a, sub ), f1, f2 )
      else throw new IllegalArgumentException( "clause: " + as( a, sub ) + " is not found in CNFs of ancestors: "
        + CNFp.toFClauseList( f1 ) + " or " + CNFp.toFClauseList( f2 ) + " of formula " + f )
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

  def getVariableRenaming( f1: FClause, f2: FClause ): Option[Substitution] = {
    if ( f1.neg.size != f2.neg.size || f1.pos.size != f2.pos.size ) None
    else {
      val pairs = ( f1.neg.asInstanceOf[Seq[LambdaExpression]].zip( f2.neg.asInstanceOf[Seq[LambdaExpression]] )
        ++ f1.pos.asInstanceOf[Seq[LambdaExpression]].zip( f2.pos.asInstanceOf[Seq[LambdaExpression]] ) )
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

  def containsSubsequent( set: List[FClause], fc: FClause ): Boolean = {
    val fs = fc.toFSequent
    val r = set.filter( x => ( x.toFSequent diff fs ).isEmpty )
    r.nonEmpty
  }

  // applying sub to a clause
  def as( a: FClause, sub: Substitution ): FClause = FClause( a.neg.map( f => sub( f ) ), a.pos.map( f => sub( f ) ) )
}

