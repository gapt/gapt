package at.logic.gapt.provers.inductionProver

import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.reduceHolToFol
import at.logic.gapt.expr.hol._
import at.logic.gapt.grammars.RecursionScheme
import at.logic.gapt.proofs.lk.skolemize
import at.logic.gapt.proofs.HOLClause
import at.logic.gapt.proofs.resolution.{ forgetfulPropResolve, forgetfulPropParam }
import at.logic.gapt.provers.smtlib.Z3
import at.logic.gapt.provers.veriT.VeriT

import scala.collection.mutable

object qbupForRecSchem {
  def apply( recSchem: RecursionScheme ): HOLFormula = {
    def convert( term: LambdaExpression ): HOLFormula = term match {
      case Apps( ax, _ ) if ax == recSchem.axiom => Bottom()
      case Apps( nt @ Const( name, ty ), args ) if recSchem.nonTerminals contains nt =>
        HOLAtom( Var( s"X_$name", ty )( args: _* ) )
      case formula => -formula
    }

    existsclosure( And( recSchem.rules groupBy { _.lhs } map {
      case ( lhs, rules ) =>
        All.Block(
          freeVariables( lhs ) toSeq,
          And( rules map { _.rhs } map convert toSeq ) --> convert( lhs )
        )
    } toSeq ) )
  }
}

object hSolveQBUP {

  private def getConjuncts( f: HOLFormula ): Set[HOLFormula] = f match {
    case All( _, g )                                 => getConjuncts( g )
    case And( g1, g2 )                               => getConjuncts( g1 ) union getConjuncts( g2 )
    case _ if !containsQuantifierOnLogicalLevel( f ) => Set( f )
  }

  def findConseq( start: HOLFormula, cond: HOLFormula, Xinst: LambdaExpression, subst: Substitution ): Set[HOLFormula] = {
    val isSolution = mutable.Map[Set[HOLClause], Boolean]()

    def checkSol( cnf: Set[HOLClause] ): Unit =
      if ( !isSolution.contains( cnf ) ) {
        val substCnfFormula = subst( And( cnf map { _.toFormula } ) )
        if ( VeriT isValid TermReplacement( cond, Map( Xinst -> substCnfFormula ) ) ) {
          isSolution( cnf ) = true
          forgetfulPropResolve( cnf ) foreach checkSol
          forgetfulPropParam( cnf ) foreach checkSol
        } else {
          isSolution( cnf ) = false
        }
      }

    checkSol( CNFp.toClauseList( start ).map { _.distinct.sortBy { _.hashCode } }.toSet )

    isSolution collect { case ( sol, true ) => And( sol map { _.toFormula } ) } toSet
  }

  def apply( qbupMatrix: HOLFormula, xInst: LambdaExpression, start: HOLFormula ): Option[LambdaExpression] = {
    val Apps( x: Var, xInstArgs ) = xInst
    val conjuncts = getConjuncts( qbupMatrix )

    // FIXME: more than one condition
    val ( searchCondition, searchSubst ) = conjuncts flatMap { c =>
      val xOccs = subTerms( c ) collect { case occ @ Apps( `x`, args ) if args.size == xInstArgs.size => occ }
      // FIXME: two-sided mgu
      syntacticMGU( xOccs map { _ -> xInst } ) map { mgu =>
        mgu( c ) -> mgu
      }
    } head

    val conseqs = findConseq( start, searchCondition, searchSubst( xInst ), searchSubst )

    val xGenArgs = xInstArgs.zipWithIndex.map { case ( a, i ) => Var( s"x$i", a.exptype ) }
    val xGen = x( xGenArgs: _* )
    val Some( matching ) = syntacticMatching( xGen, xInst )
    conseqs foreach { conseq =>
      val genConseq = TermReplacement( conseq, matching.map.map( _.swap ) )
      val sol = Abs( xGenArgs, genConseq )
      if ( Z3 isValid skolemize( BetaReduction.betaNormalize( Substitution( x -> sol )( qbupMatrix ) ) ) ) {
        return Some( sol )
      }
    }
    None
  }

}
