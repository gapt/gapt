package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ FOLMatchingAlgorithm, FOLSubstitution }
import at.logic.gapt.expr.hol.{ CNFp, CNFn, univclosure }
import at.logic.gapt.proofs.expansionTrees.{ formulaToExpansionTree, ExpansionSequent, ExpansionTree }
import at.logic.gapt.proofs.lk.base.{ Sequent, HOLSequent, HOLSequentOrdering }
import at.logic.gapt.proofs.resolution.robinson._

import scala.collection.mutable

object RobinsonToExpansionProof {
  def apply( p: RobinsonResolutionProof, es: HOLSequent ): ExpansionSequent = {
    val dummyConstant = rename( FOLConst( "arbitrary" ), constants( es ).toList )
    val cnfMap: Seq[( HOLClause, Boolean, FOLFormula )] =
      es.map( _.asInstanceOf[FOLFormula] ).map(
        ant => CNFp.toClauseList( ant ).map( ( _, false, ant ) ),
        suc => CNFn.toFClauseList( suc ).map { case Clause( n, p ) => ( Clause( n, p ), true, suc ) }
      ).elements.flatten
    apply_( p, {
      case Clause( Seq( f ), Seq( f_ ) ) if f == f_       => Set()
      case Clause( Seq(), Seq( Eq( a, a_ ) ) ) if a == a_ => Set()
      case clause =>
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
        }.head )
    } )
  }

  def apply( p: RobinsonResolutionProof ): ExpansionSequent =
    apply_( p, {
      case Clause( Seq( f ), Seq( f_ ) ) if f == f_       => Set()
      case Clause( Seq(), Seq( Eq( a, a_ ) ) ) if a == a_ => Set()
      case clause                                         => Set( ( false, univclosure( clause.toFormula.asInstanceOf[FOLFormula] ), freeVariables( clause.toFormula.asInstanceOf[FOLFormula] ).map { v => v -> v }.toMap ) )
    } )

  private def apply_( p: RobinsonResolutionProof, instForIC: FOLClause => Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )] ): ExpansionSequent = {
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

  private def getInstances( p: RobinsonResolutionProof, instForIC: FOLClause => Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )] ): Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )] = {
    val substMap = mutable.Map[RobinsonResolutionProof, Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )]]()

    def applySubst( instances: Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )], subst: Substitution ) =
      instances map {
        case ( pol, formula, instSubst ) =>
          ( pol, formula, instSubst.map { case ( v, r ) => v -> subst( r ).asInstanceOf[FOLTerm] } )
      }

    def getInst( node: RobinsonResolutionProof ): Set[( Boolean, FOLFormula, Map[FOLVar, FOLTerm] )] =
      substMap.getOrElseUpdate(
        node,
        node match {
          case InitialClause( clause ) => instForIC( clause.toHOLClause.map( _.asInstanceOf[FOLAtom] ) )
          case Factor( clause, p1, List( occurrences ), subst ) =>
            applySubst( getInst( p1 ), subst )
          case Variant( clause, p1, subst ) =>
            applySubst( getInst( p1 ), subst )
          case Instance( clause, p1, subst ) =>
            applySubst( getInst( p1 ), subst )
          case Resolution( clause, p1, p2, occ1, occ2, subst ) =>
            applySubst( getInst( p1 ) ++ getInst( p2 ), subst )
          case Paramodulation( clause, p1, p2, occ1, occ2, main, subst ) =>
            applySubst( getInst( p1 ) ++ getInst( p2 ), subst )
        }
      )

    getInst( p )
  }
}
