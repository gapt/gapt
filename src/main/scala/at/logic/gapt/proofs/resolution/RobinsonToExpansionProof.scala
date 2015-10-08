package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ FOLMatchingAlgorithm, FOLSubstitution }
import at.logic.gapt.expr.hol.{ CNFn, CNFp, univclosure }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansionTrees.{ ExpansionSequent, formulaToExpansionTree }

import scala.collection.mutable

object RobinsonToExpansionProof {
  def apply( p: ResolutionProof, es: HOLSequent ): ExpansionSequent = {
    val dummyConstant = rename( FOLConst( "arbitrary" ), constants( es ).toList )
    val cnfMap: Map[FOLClause, Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )]] =
      es.map( f => toVNF( f ).asInstanceOf[FOLFormula] ).map(
        ant => CNFp.toClauseList( ant ).map { ( _, false, ant ) },
        suc => CNFn.toClauseList( suc ).map { ( _, true, suc ) }
      ).elements.flatten.groupBy( _._1 ).mapValues {
          _ map {
            case ( cnfClause, pol, formula ) =>
              ( pol, formula,
                variables( formula ).map( _ -> dummyConstant ).toMap
                ++ variables( cnfClause ).map( v => v -> v ) )
          } toSet
        }
    apply_( p, cnfMap )
  }

  def apply( p: ResolutionProof ): ExpansionSequent =
    apply_( p, clause => Set(
      ( false,
        univclosure( clause.toFormula.asInstanceOf[FOLFormula] ),
        freeVariables( clause.toFormula.asInstanceOf[FOLFormula] ).map { v => v -> v }.toMap )
    ) )

  private def apply_( p: ResolutionProof, instForIC: FOLClause => Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )] ): ExpansionSequent = {
    val inst = getInstances( p, instForIC )
    val dummyConstant = rename( FOLConst( "arbitrary" ), inst.map( _._2 ).flatMap( constants( _ ) ).toList )

    // Expansion trees require instance terms not to contain the quantified variables.
    // Hence we ground the instance substitutions here.
    // FIXME: maybe just rename the variables?
    val instSubsts = inst.map {
      case ( pol, formula, subst ) =>
        val ground = FOLSubstitution( freeVariables( subst.values ).map( _ -> dummyConstant ) )
        ( pol, formula, FOLSubstitution( subst mapValues { ground( _ ) } ) )
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

  private def getInstances( p: ResolutionProof, instForIC: FOLClause => Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )] ): Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )] = {
    val substMap = mutable.Map[ResolutionProof, Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )]]()

    def getInst( node: ResolutionProof ): Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )] =
      substMap.getOrElseUpdate( node, node match {
        case InputClause( clause ) =>
          instForIC( clause )
        case Instance( subProof, subst ) =>
          getInst( subProof ) map {
            case ( pol, formula, instSubst ) =>
              ( pol, formula, instSubst mapValues { subst( _ ) } )
          }
        case _ => node.immediateSubProofs flatMap getInst toSet
      } )

    getInst( p )
  }
}
