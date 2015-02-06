package at.logic.algorithms.resolution

import scala.collection.immutable.HashMap
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.resolution.robinson._
import at.logic.language.fol.{ Equation => FOLEquation, FOLTerm, FOLFormula, FOLExpression, Substitution }
import at.logic.calculi.resolution.{ FClause, Clause }
import at.logic.algorithms.lk.{ applySubstitution => applySub, CleanStructuralRules, CloneLKProof }
import at.logic.provers.atp.SearchDerivation

/**
 *  Sometimes, we have a resolution refutation R of a set of clauses C
 *  and want a refutation R' of a set C' such that C implies C'.
 *
 *  This algorithm tries to obtain R' by trying to replace clauses c
 *  from C in R by derivations of C from C' in the following way:
 *
 *  - If c is in C', do nothing.
 *  - Otherwise, try to derive c from C' by paramodulation and symmetry (prover9 often needs
 *    this, and the check is usually fast),
 *  - Otherwise, try to derive c from C' by propositional resolution.
 *
 *  If none of this works, we issue a warning and keep the clause c. If no warning is issued
 *  and the algorithm terminates, the result is the desired R'.
 */

object fixDerivation extends at.logic.utils.logging.Logger {

  private def getSymmetryMap( to: FClause, from: FSequent ) = {
    var err = false

    def createMap( from: Seq[FOLFormula], to: Seq[FOLFormula] ) = {
      from.foldLeft( HashMap[FOLFormula, FOLFormula]() )( ( map, from_f ) => {
        val to_f = to.find( to_f => ( from_f == to_f ) || ( ( from_f, to_f ) match {
          case ( FOLEquation( from_l, from_r ), FOLEquation( to_l, to_r ) ) if from_l == to_r && from_r == to_l => true
          case _ => false
        } ) )

        if ( to_f != None )
          map + ( ( from_f, to_f.get ) )
        else {
          err = true
          map
        }
      } )
    }

    val avail_pos = from.succedent.map( f => f.asInstanceOf[FOLFormula] )
    val avail_neg = from.antecedent.map( f => f.asInstanceOf[FOLFormula] )

    val neg_map = createMap( avail_neg, to.neg.map( _.asInstanceOf[FOLFormula] ) )
    val pos_map = createMap( avail_pos, to.pos.map( _.asInstanceOf[FOLFormula] ) )

    if ( err )
      None
    else
      Some( ( neg_map, pos_map ) )
  }

  def canDeriveBySymmetry( to: FClause, from: FSequent ) = getSymmetryMap( to, from ) match {
    case Some( _ ) => true
    case None      => false
  }

  private def applySymm( p: RobinsonResolutionProof, f: FOLFormula, pos: Boolean ) =
    {
      val ( left, right ) = f match {
        case FOLEquation( l, r ) => ( l, r )
      }
      val newe = FOLEquation( right, left )
      val refl = FOLEquation( left, left )
      val s = Substitution()

      if ( pos ) {
        val irefl = InitialClause( Nil, refl :: Nil )
        Paramodulation( p, irefl, f, refl, newe, s, pos )
      } else {
        val init = InitialClause( newe :: Nil, newe :: Nil )
        val init2 = InitialClause( newe :: Nil, newe :: Nil )
        val eq1 = Paramodulation( init, p, newe, f, refl, s, pos )
        val eq2 = Paramodulation( init2, eq1, newe, refl, newe, s, pos )
        Factor( eq2, newe, 3, pos, s )
      }
    }

  private def deriveBySymmetry( to: FClause, from: FSequent ) = {
    val ( neg_map, pos_map ) = getSymmetryMap( to, from ).get

    val init = InitialClause( from.antecedent.map( _.asInstanceOf[FOLFormula] ), from.succedent.map( _.asInstanceOf[FOLFormula] ) )
    val s_neg = neg_map.keySet.foldLeft( init )( ( p, f ) => f match {
      case FOLEquation( _, _ ) if neg_map( f ) != f => applySymm( p, f, false )
      case _                                        => p
    } )

    pos_map.keySet.foldLeft( s_neg )( ( p, f ) => f match {
      case FOLEquation( _, _ ) if pos_map( f ) != f => applySymm( p, f, true )
      case _                                        => p
    } )
  }

  private def isReflexivity( c: FClause ) =
    c.pos.exists( a => a match {
      case FOLEquation( x, y ) if x == y => true
      case _                             => false
    } )

  private def isTautology( c: FClause ) = c.pos.exists( a => c.neg.exists( b => a == b ) )

  // NOTE: What if the symmetric clause found is a tautology?
  private def handleInitialClause( cls: FClause, cs: Seq[FSequent] ) = {
    // If cls is in cs, do nothing
    val cls_sequent = FSequent(
      cls.neg.map( f => f.asInstanceOf[FOLFormula] ),
      cls.pos.map( f => f.asInstanceOf[FOLFormula] ) )

    if ( cs.contains( cls_sequent ) || isReflexivity( cls ) || isTautology( cls ) ) InitialClause( cls )
    else
      cs.find( c => canDeriveBySymmetry( cls, c ) ) match {
        case Some( c ) => deriveBySymmetry( cls, c )
        case None => SearchDerivation( cs, cls_sequent, true ) match {
          case Some( d ) => {
            val ret = d.asInstanceOf[RobinsonResolutionProof]
            if ( ret.root.toFClause != cls ) {
              // TODO: add appropriate rules to derive cls --- SearchDerivation only yields
              // a derivation of a clause subsuming cls, not cls itself!
              // Until this is fixed, we just return the original clause, not the derivation
              // constructed above.

              InitialClause( cls )
            } else
              ret
          }
          case None => {
            warn( "Could not derive " + cls + " from " + cs + " by symmetry or propositional resolution" )
            InitialClause( cls )
          }
        }
      }
  }

  def apply( p: RobinsonResolutionProof, cs: Seq[FSequent] ): RobinsonResolutionProof = {
    rec( p )( cs )
  }

  private def rec( p: RobinsonResolutionProof )( implicit cs: Seq[FSequent] ): RobinsonResolutionProof = {
    var fac = false
    val res = p match {
      case InitialClause( cls ) => handleInitialClause( cls.toFClause, cs )

      case Factor( r, p, a, s ) => {
        fac = true
        a match {
          case lit1 :: Nil => {
            val pos = p.root.succedent.contains( lit1.head )
            Factor( rec( p ), lit1.head.formula, lit1.size, pos, s )
          }
          case lit1 :: lit2 :: Nil =>
            Factor( rec( p ), lit1.head.formula, lit1.size, lit2.head.formula, lit2.size, s )
          case _ => throw new Exception( "Factor rule for " + p.root + " does not have one or two primary formulas!" )
        }
      }
      case Variant( r, p, s ) => Variant( rec( p ), s )
      case Resolution( r, p1, p2, a1, a2, s ) =>
        Resolution( rec( p1 ), rec( p2 ), a1.formula.asInstanceOf[FOLFormula], a2.formula.asInstanceOf[FOLFormula], s )
      case Paramodulation( r, p1, p2, a1, a2, p, s ) =>
        Paramodulation( rec( p1 ), rec( p2 ), a1.formula.asInstanceOf[FOLFormula], a2.formula.asInstanceOf[FOLFormula], p.formula.asInstanceOf[FOLFormula], s, p2.root.succedent.contains( a2 ) )
      // this case is applicable only if the proof is an instance of RobinsonProofWithInstance
      case Instance( _, p, s ) => Instance( rec( p ), s )
    }
    ( res.root.positive ++ res.root.negative ).foreach( fo => assert( fo.formula.isInstanceOf[FOLFormula] ) )
    res
  }
}
