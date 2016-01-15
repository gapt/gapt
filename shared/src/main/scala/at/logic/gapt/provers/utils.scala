package at.logic.gapt.provers

import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ HOLSequent, HOLClause }

object renameConstantsToFi {
  private def mkName( i: Int ) = s"f$i"
  private def getRenaming( seq: HOLSequent ): Map[Const, Const] = getRenaming( constants( seq ) )
  private def getRenaming( cnf: List[HOLClause] ): Map[Const, Const] =
    getRenaming( cnf.flatMap( constants( _ ) ).toSet )
  private def getRenaming( constants: Set[Const] ): Map[Const, Const] =
    constants.toSeq.zipWithIndex.map {
      case ( c @ EqC( _ ), _ ) => c -> c
      case ( c, i )            => c -> Const( mkName( i ), c.exptype )
    }.toMap
  private def invertRenaming( map: Map[Const, Const] ) = map.map( _.swap )

  def apply( seq: HOLSequent ): ( HOLSequent, Map[Const, Const], Map[Const, Const] ) = {
    val renaming = getRenaming( seq )
    val renamedSeq = seq map { TermReplacement( _, renaming.toMap[LambdaExpression, LambdaExpression] ) }
    ( renamedSeq, renaming, invertRenaming( renaming ) )
  }
  def apply( cnf: List[HOLClause] ): ( List[HOLClause], Map[Const, Const], Map[Const, Const] ) = {
    val renaming = getRenaming( cnf )
    val renamedCNF = cnf.map( clause => clause map { TermReplacement( _, renaming.toMap[LambdaExpression, LambdaExpression] ) } )
    ( renamedCNF, renaming, invertRenaming( renaming ) )
  }
}

object groundFreeVariables {
  def getGroundingMap( vars: Set[Var], consts: Set[Const] ): Seq[( Var, Const )] = {
    val varList = vars.toList
    ( varList, getRenaming( varList.map( _.sym ), consts.map( _.sym ).toList ) ).zipped.map {
      case ( v, cs ) =>
        v -> Const( cs.toString, v.exptype )
    }
  }

  def getGroundingMap( seq: HOLSequent ): Seq[( Var, Const )] =
    getGroundingMap( variables( seq ), constants( seq ) )

  def apply( seq: HOLSequent ): ( HOLSequent, Map[LambdaExpression, LambdaExpression] ) = {
    val groundingMap = getGroundingMap( seq )
    val groundSeq = Substitution( groundingMap )( seq )
    val unground = groundingMap.map { case ( f, t ) => ( t, f ) }
    ( groundSeq, unground.toMap )
  }
}