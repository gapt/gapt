package gapt.formats.ivy.conversion

import gapt.formats.ivy.{ IvyResolutionProof, NewSymbol, Flip => IFlip, InitialClause => IInitialClause, Instantiate => IInstantiate, Paramodulation => IParamodulation, Propositional => IPropositional, Resolution => IResolution }
import gapt.proofs.{ Ant, Clause, HOLClause, Suc }
import gapt.proofs.resolution._
import gapt.expr._
import gapt.expr.subst.Substitution
import gapt.expr.util.clauseSubsumption
import gapt.expr.util.freeVariables
import gapt.expr.util.rename

import scala.collection.mutable

/**
 * Converts Ivy Proofs into Resolution Proofs
 */
object IvyToResolution {
  def apply( ivy: IvyResolutionProof ): ResolutionProof = {
    val memo = mutable.Map[String, ResolutionProof]()
    def convert( p: IvyResolutionProof ): ResolutionProof = memo.getOrElseUpdate( p.id, p match {
      // prooftrans ivy adds reflexivity as input clauses
      case IInitialClause( id, exp,
        Clause( Seq(), Seq( Eq( t, t_ ) ) ) ) if t == t_ => Refl( t )
      case IInitialClause( id, exp, clause )            => Input( clause )
      case IInstantiate( id, exp, sub, clause, parent ) => Subst( convert( parent ), sub )
      case IResolution( id, exp, lit1, lit2, clause, parent1, parent2 ) =>
        val q1 = convert( parent1 )
        val q2 = convert( parent2 )
        if ( lit1 isAnt )
          Resolution(
            q2, Suc( q2.conclusion.succedent indexOf parent2.conclusion( lit2 ) ),
            q1, Ant( q1.conclusion.antecedent indexOf parent1.conclusion( lit1 ) ) )
        else
          Resolution(
            q1, Suc( q1.conclusion.succedent indexOf parent1.conclusion( lit1 ) ),
            q2, Ant( q2.conclusion.antecedent indexOf parent2.conclusion( lit2 ) ) )
      case IPropositional( id, exp, clause, parent ) if clause isSubMultisetOf parent.conclusion =>
        Factor( convert( parent ), clause )
      case IPropositional( id, exp, clause, parent ) =>
        val Some( subst ) = clauseSubsumption( parent.conclusion, clause )
        Factor( Subst( convert( parent ), subst ), clause )
      case IFlip( id, exp, unflipped, clause, parent ) =>
        val q = convert( parent )
        Flip( q, q.conclusion.indicesWhere( _ == parent.conclusion( unflipped ) ).filter( _ sameSideAs unflipped ).head )
      case IParamodulation( id, exp, pos, eq, lit, newLit, orientation, clause, parent1, parent2 ) =>
        val q1 = convert( parent1 )
        val q2 = convert( parent2 )

        val litIdx = if ( lit isSuc )
          Suc( q2.conclusion.succedent indexOf parent2.conclusion( lit ) )
        else
          Ant( q2.conclusion.antecedent indexOf parent2.conclusion( lit ) )
        val eqIdx = Suc( q1.conclusion.succedent indexOf parent1.conclusion( eq ) )

        Paramod.withMain( q1, eqIdx, q2, litIdx, newLit )
      case NewSymbol( id, exp, lit, new_symbol, replacement_term, clause, parent ) =>
        // insert a new axiom, will be later removed
        Input( clause )
    } ) ensuring { res => res.conclusion multiSetEquals p.conclusion }

    val proof = convert( ivy )

    val variablesInProof = proof.subProofs flatMap { p => freeVariables( p.conclusion ) }
    val ( newSymbols, justifications ) = ivy.subProofs.collect {
      case NewSymbol( _, _, _, sym, rt, _, parent ) =>
        val justification = convert( parent )
        justification.conclusion match {
          case _ if freeVariables( rt ).isEmpty =>
            ( sym -> rt, Refl( rt ) )
          case HOLClause( Seq(), Seq( Eq( lhs, rhs ) ) ) if lhs == rt =>
            // FIXME: probably still has name clashes if there are multiple new_symbol inferences
            val subst = Substitution( rename( freeVariables( rhs ), variablesInProof ) )
            ( sym -> subst( rhs ), Subst( justification, subst ) )
        }
    }.unzip

    val proofWithoutNewSymbols = TermReplacement( proof, newSymbols.toMap[Expr, Expr] )
    val justificationsWithoutNewSymbols = justifications map { TermReplacement( _, newSymbols.toMap[Expr, Expr] ) }

    mapInputClauses( proofWithoutNewSymbols ) { cls =>
      justificationsWithoutNewSymbols.find { _.conclusion == cls } getOrElse { Input( cls ) }
    }
  }
}
