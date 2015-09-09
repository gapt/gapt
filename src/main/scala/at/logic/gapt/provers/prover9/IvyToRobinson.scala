package at.logic.gapt.formats.ivy.conversion

import at.logic.gapt.formats.ivy.{ InitialClause => IInitialClause, Instantiate => IInstantiate, Resolution => IResolution, Paramodulation => IParamodulation, Propositional => IPropositional, NewSymbol, IvyResolutionProof, Flip }
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.proofs.{ HOLClause, Suc, Ant }
import at.logic.gapt.proofs.lk.base.RichOccSequent
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
      case IInitialClause( id, exp, clause )            => InputClause( clause.toHOLSequent.map( _.asInstanceOf[FOLAtom] ) )
      case IInstantiate( id, exp, sub, clause, parent ) => Instance( convert( parent ), sub )
      case IResolution( id, exp, lit1, lit2, clause, parent1, parent2 ) =>
        val q1 = convert( parent1 )
        val q2 = convert( parent2 )
        if ( parent1.root.antecedent contains lit1 )
          Resolution(
            q1, Ant( q1.conclusion.antecedent indexOf lit1.formula ),
            q2, Suc( q2.conclusion.succedent indexOf lit2.formula )
          )
        else
          Resolution(
            q1, Suc( q1.conclusion.succedent indexOf lit1.formula ),
            q2, Ant( q2.conclusion.antecedent indexOf lit2.formula )
          )
      case IPropositional( id, exp, clause, parent ) =>
        Factor( convert( parent ), clause.map( _.formula.asInstanceOf[FOLAtom] ) )._1
      case Flip( id, exp, flipped, clause, parent ) =>
        val q = convert( parent )
        val Eq( t: FOLTerm, s: FOLTerm ) = flipped.formula
        val unflippedIdx = if ( clause.succedent contains flipped )
          Suc( q.conclusion.succedent indexOf Eq( s, t ) )
        else
          Ant( q.conclusion.antecedent indexOf Eq( s, t ) )
        if ( unflippedIdx.isSuc ) {
          /* this is a positive occurrence, i.e. we do the following:
               (parent)
              C :- D, s=t       :- s=s
              ----------------------------- para
                     C :- D, t=s
           */
          Paramodulation( q, unflippedIdx,
            ReflexivityClause( s ), Suc( 0 ), Eq( t, s ) )
        } else {
          /* this is a negative occurrence, i.e. we do the following:
                t=s :- t=s         :- s=s
                ------------------------- para           (parent)
                       t=s :- s=t                      s=t, C :- D
                       -------------------------------------------------- Res
                                       t=s, C :- D
          */
          Resolution(
            Paramodulation( TautologyClause( Eq( t, s ) ), Suc( 0 ),
              ReflexivityClause( s ), Suc( 0 ), Eq( s, t ) ), Suc( 0 ),
            q, unflippedIdx
          )
        }
      case IParamodulation( id, exp, pos, newLit, orientation, clause, parent1, parent2 ) =>
        val q1 = convert( parent1 )
        val q2 = convert( parent2 )

        val eq = newLit.parents( 0 )
        val lit = newLit.parents( 1 )

        val litIdx = if ( parent2.root.succedent contains lit )
          Suc( q2.conclusion.succedent indexOf lit.formula )
        else
          Ant( q2.conclusion.antecedent indexOf lit.formula )

        Paramodulation( q1, Suc( q1.conclusion.succedent indexOf eq.formula ),
          q2, litIdx,
          newLit.formula.asInstanceOf[FOLAtom] )
      case NewSymbol( id, exp, lit, new_symbol, replacement_term, clause, parent ) =>
        // insert a new axiom, will be later removed
        InputClause( clause.toHOLSequent.map( _.asInstanceOf[FOLAtom] ) )
    } )

    val proof = convert( ivy )

    val variablesInProof = proof.subProofs flatMap { p => freeVariables( p.conclusion ) }
    val ( newSymbols, justifications ) = ivy.nodes.collect {
      case NewSymbol( _, _, _, sym, rt, _, parent ) =>
        val justification = convert( parent )
        justification.conclusion match {
          case _ if freeVariables( rt ).isEmpty =>
            ( sym -> rt, ReflexivityClause( rt ) )
          case HOLClause( Seq(), Seq( Eq( lhs: FOLTerm, rhs: FOLTerm ) ) ) if lhs == rt =>
            // FIXME: probably still has name clashes if there are multiple new_symbol inferences
            val subst = FOLSubstitution( rename( freeVariables( rhs ), variablesInProof ) )
            ( sym -> subst( rhs ), Instance( justification, subst ) )
        }
    }.unzip

    val proofWithoutNewSymbols = TermReplacement( proof, newSymbols.toMap[FOLTerm, FOLTerm] )

    mapInputClauses( proofWithoutNewSymbols ) { cls =>
      justifications.find { _.conclusion == cls } getOrElse { InputClause( cls ) }
    }

    convert( ivy )
  }
}
