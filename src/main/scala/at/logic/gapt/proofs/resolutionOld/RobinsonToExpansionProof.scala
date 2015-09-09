package at.logic.gapt.proofs.resolutionOld

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ FOLMatchingAlgorithm, FOLSubstitution }
import at.logic.gapt.expr.hol.{ CNFp, CNFn, univclosure }
import at.logic.gapt.proofs.expansionTrees.{ formulaToExpansionTree, ExpansionSequent, ExpansionTree }
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.resolutionOld.robinson.RobinsonResolutionProof
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.resolutionNew._

import scala.collection.mutable

object RobinsonToExpansionProof {
  def apply( p: RobinsonResolutionProof, es: HOLSequent ): ExpansionSequent =
    apply( resOld2New( p ), es )

  def apply( p: resolutionNew.ResolutionProof, es: HOLSequent ): ExpansionSequent = {
    val dummyConstant = rename( FOLConst( "arbitrary" ), constants( es ).toList )
    val cnfMap: Seq[( HOLClause, Boolean, FOLFormula )] =
      es.map( f => toVNF( f ).asInstanceOf[FOLFormula] ).map(
        ant => CNFp.toClauseList( ant ).map( ( _, false, ant ) ),
        suc => CNFn.toFClauseList( suc ).map { case Clause( n, p ) => ( Clause( n, p ), true, suc ) }
      ).elements.flatten
    apply_( p, clause =>
      Set( cnfMap.view.flatMap {
        case ( cnfClause, pol, formula ) =>
          FOLMatchingAlgorithm.matchTerms(
            cnfClause.toFormula.asInstanceOf[FOLFormula],
            clause.toFormula.asInstanceOf[FOLFormula]
          ) map { subst =>
            ( pol, formula,
              variables( formula ).map( _.asInstanceOf[FOLVar] -> dummyConstant ).toMap
              ++ variables( cnfClause ).map( _.asInstanceOf[FOLVar] ).map( v => v -> subst( v ) ) )
          }
      }.head ) )
  }

  def apply( p: RobinsonResolutionProof ): ExpansionSequent = apply( resOld2New( p ) )
  def apply( p: resolutionNew.ResolutionProof ): ExpansionSequent =
    apply_( p, {
      case Clause( Seq( f ), Seq( f_ ) ) if f == f_       => Set()
      case Clause( Seq(), Seq( Eq( a, a_ ) ) ) if a == a_ => Set()
      case clause                                         => Set( ( false, univclosure( clause.toFormula.asInstanceOf[FOLFormula] ), freeVariables( clause.toFormula.asInstanceOf[FOLFormula] ).map { v => v -> v }.toMap ) )
    } )

  private def apply_( p: resolutionNew.ResolutionProof, instForIC: FOLClause => Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )] ): ExpansionSequent = {
    val inst = getInstances( p, instForIC )
    val dummyConstant = rename( FOLConst( "arbitrary" ), inst.map( _._2 ).flatMap( constants( _ ) ).toList )

    // Expansion trees require instance terms not to contain the quantified variables.
    // Hence we ground the instance substitutions here.
    // FIXME: maybe just rename the variables?
    val instSubsts = inst.map {
      case ( pol, formula, subst ) =>
        ( pol, formula,
          FOLSubstitution( freeVariables( subst.values ).map( _ -> dummyConstant ) )
          compose FOLSubstitution( subst ) )
    }

    Sequent(
      instSubsts.filter( _._1 == false ).groupBy( _._2 ).map {
      case ( formula, substs ) =>
        formulaToExpansionTree( formula, substs.map( _._3 ).toList, false )
    }.toSeq,
      instSubsts.filter( _._1 == true ).groupBy( _._2 ).map {
      case ( formula, substs ) =>
        formulaToExpansionTree( formula, substs.map( _._3 ).toList, true )
    }.toSeq
    )
  }

  private def getInstances( p: resolutionNew.ResolutionProof, instForIC: FOLClause => Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )] ): Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )] = {
    val substMap = mutable.Map[resolutionNew.ResolutionProof, Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )]]()

    def applySubst( instances: Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )], subst: FOLSubstitution ) =
      instances map {
        case ( pol, formula, instSubst ) =>
          ( pol, formula, instSubst.map { case ( v, r ) => v -> subst( r ) } )
      }

    def getInst( node: resolutionNew.ResolutionProof ): Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )] =
      substMap.getOrElseUpdate(
        node,
        node match {
          case InputClause( clause ) => instForIC( clause )
          case Instance( subProof, subst ) =>
            applySubst( getInst( subProof ), subst )
          case _ => node.immediateSubProofs flatMap getInst toSet
        }
      )

    getInst( p )
  }
}
