package at.logic.gapt.formats.ivy.conversion

import at.logic.gapt.formats.ivy.{ InitialClause => IInitialClause, Instantiate => IInstantiate, Resolution => IResolution, Paramodulation => IParamodulation, Propositional => IPropositional, NewSymbol, IvyResolutionProof, Flip => IFlip }
import at.logic.gapt.proofs.{ Clause, HOLClause, Suc, Ant }
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.expr._
import at.logic.gapt.algorithms.rewriting.TermReplacement
import scala.collection.mutable

/**
 * Converts Ivy Proofs into Robinson Resolution Proofs
 */
object IvyToRobinson {
  def apply( ivy: IvyResolutionProof ): ResolutionProof = {
    val memo = mutable.Map[String, ResolutionProof]()
    def convert( p: IvyResolutionProof ): ResolutionProof = memo.getOrElseUpdate( p.id, p match {
      // prooftrans ivy adds reflexivity as input clauses
      case IInitialClause( id, exp,
        Clause( Seq(), Seq( Eq( t, t_ ) ) ) ) if t == t_ => ReflexivityClause( t )
      case IInitialClause( id, exp, clause )            => InputClause( clause )
      case IInstantiate( id, exp, sub, clause, parent ) => Instance( convert( parent ), sub )
      case IResolution( id, exp, lit1, lit2, clause, parent1, parent2 ) =>
        val q1 = convert( parent1 )
        val q2 = convert( parent2 )
        if ( lit1 isAnt )
          Resolution(
            q2, Suc( q2.conclusion.succedent indexOf parent2.conclusion( lit2 ) ),
            q1, Ant( q1.conclusion.antecedent indexOf parent1.conclusion( lit1 ) )
          )
        else
          Resolution(
            q1, Suc( q1.conclusion.succedent indexOf parent1.conclusion( lit1 ) ),
            q2, Ant( q2.conclusion.antecedent indexOf parent2.conclusion( lit2 ) )
          )
      case IPropositional( id, exp, clause, parent ) if clause isSubMultisetOf parent.conclusion =>
        Factor( convert( parent ), clause )._1
      case IPropositional( id, exp, clause, parent ) =>
        val Some( subst ) = StillmanSubsumptionAlgorithmFOL.subsumes_by( parent.conclusion, clause )
        Factor( Instance( convert( parent ), subst ), clause )._1
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

        Paramodulation( q1, Suc( q1.conclusion.succedent indexOf parent1.conclusion( eq ) ),
          q2, litIdx,
          newLit )
      case NewSymbol( id, exp, lit, new_symbol, replacement_term, clause, parent ) =>
        // insert a new axiom, will be later removed
        InputClause( clause )
    } ) ensuring { res => res.conclusion multiSetEquals p.conclusion }

    val proof = convert( ivy )

    val variablesInProof = proof.subProofs flatMap { p => freeVariables( p.conclusion ) }
    val ( newSymbols, justifications ) = ivy.subProofs.collect {
      case NewSymbol( _, _, _, sym, rt, _, parent ) =>
        val justification = convert( parent )
        justification.conclusion match {
          case _ if freeVariables( rt ).isEmpty =>
            ( sym -> rt, ReflexivityClause( rt ) )
          case HOLClause( Seq(), Seq( Eq( lhs, rhs ) ) ) if lhs == rt =>
            // FIXME: probably still has name clashes if there are multiple new_symbol inferences
            val subst = Substitution( rename( freeVariables( rhs ), variablesInProof ) )
            ( sym -> subst( rhs ), Instance( justification, subst ) )
        }
    }.unzip

    val proofWithoutNewSymbols = TermReplacement( proof, newSymbols.toMap[LambdaExpression, LambdaExpression] )

    mapInputClauses( proofWithoutNewSymbols ) { cls =>
      justifications.find { _.conclusion == cls } getOrElse { InputClause( cls ) }
    }
  }
}
