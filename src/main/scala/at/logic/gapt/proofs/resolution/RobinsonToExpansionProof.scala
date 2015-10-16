package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ CNFn, CNFp, univclosure }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansionTrees.{ ExpansionSequent, formulaToExpansionTree }

import scala.collection.mutable

object RobinsonToExpansionProof {
  def apply( p: ResolutionProof, es: HOLSequent ): ExpansionSequent =
    if ( !es.forall( isInVNF( _ ) ) ) {
      val vnfES = es map { toVNF( _ ) }
      apply( fixDerivation( p, vnfES ), vnfES )
    } else {
      val cnfMap: Map[HOLClause, Set[( Boolean, HOLFormula, Map[Var, LambdaExpression] )]] =
        es.map(
          ant => CNFp.toClauseList( ant ).map { ( _, false, ant ) },
          suc => CNFn.toFClauseList( suc ).map { ( _, true, suc ) }
        ).elements.flatten.groupBy( _._1 ).mapValues {
            _ map {
              case ( cnfClause, pol, formula ) =>
                ( pol, formula,
                  variables( formula ).map( v => v -> Const( "arbitrary", v.exptype ) ).toMap
                  ++ variables( cnfClause ).map( v => v -> v ) )
            } toSet
          }
      apply_( p, cnfMap )
    }

  def apply( p: ResolutionProof ): ExpansionSequent =
    apply_( p, clause => Set(
      ( false,
        univclosure( clause.toFormula ),
        freeVariables( clause.toFormula ).map { v => v -> v }.toMap )
    ) )

  private def apply_( p: ResolutionProof, instForIC: HOLClause => Set[( Boolean, HOLFormula, Map[Var, LambdaExpression] )] ): ExpansionSequent = {
    val inst = getInstances( p, instForIC )

    // Expansion trees require instance terms not to contain the quantified variables.
    // Hence we ground the instance substitutions here.
    // FIXME: maybe just rename the variables?
    val instSubsts = inst.map {
      case ( pol, formula, subst ) =>
        val ground = Substitution( freeVariables( subst.values ).map( v => v -> Const( "arbitrary", v.exptype ) ) )
        ( pol, formula, Substitution( subst mapValues { ground( _ ) } ) )
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

  private def getInstances( p: ResolutionProof, instForIC: HOLClause => Set[( Boolean, HOLFormula, Map[Var, LambdaExpression] )] ): Set[( Boolean, HOLFormula, Map[Var, LambdaExpression] )] = {
    val substMap = mutable.Map[ResolutionProof, Set[( Boolean, HOLFormula, Map[Var, LambdaExpression] )]]()

    def getInst( node: ResolutionProof ): Set[( Boolean, HOLFormula, Map[Var, LambdaExpression] )] =
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
