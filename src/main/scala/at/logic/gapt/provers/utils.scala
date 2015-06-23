package at.logic.gapt.provers

import at.logic.gapt.algorithms.rewriting.NameReplacement
import at.logic.gapt.algorithms.rewriting.NameReplacement.SymbolMap
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.proofs.resolution.FClause

object renameConstantsToFi {
  private def mkName( i: Int ) = s"f$i"
  private def getRenaming( seq: FSequent ): SymbolMap = getRenaming( constants( seq ) )
  private def getRenaming( cnf: List[FClause] ): SymbolMap =
    getRenaming( cnf.flatMap( constants( _ ) ).toSet )
  private def getRenaming( constants: Set[Const] ): SymbolMap =
    constants.toSeq.zipWithIndex.map {
      case ( Const( c, FOLHeadType( _, arity ) ), i ) =>
        c -> ( arity, mkName( i ) )
    }.toMap
  private def invertRenaming( map: SymbolMap ) =
    map.map { case ( from, ( arity, to ) ) => ( to, ( arity, from ) ) }

  def apply( seq: FSequent ): ( FSequent, SymbolMap ) = {
    val map = getRenaming( seq )
    val renamedSeq = NameReplacement( seq, map )
    ( renamedSeq, invertRenaming( map ) )
  }
  def apply( cnf: List[FClause] ): ( List[FClause], SymbolMap ) = {
    val map = getRenaming( cnf )
    val renamedCNF = cnf.map( clause => NameReplacement( clause, map ) )
    ( renamedCNF, invertRenaming( map ) )
  }
}

object groundFreeVariables {
  def getGroundingMap( vars: Set[Var], consts: Set[Const] ): Seq[( FOLVar, FOLConst )] = {
    val varList = vars.toList
    ( varList, getRenaming( varList.map( _.sym ), consts.map( _.sym ).toList ) ).zipped.map {
      case ( v: FOLVar, cs ) =>
        v -> FOLConst( cs.toString )
    }
  }

  def getGroundingMap( seq: FSequent ): Seq[( FOLVar, FOLConst )] =
    getGroundingMap( variables( seq ), constants( seq ) )

  def apply( seq: FSequent ): ( FSequent, Map[FOLTerm, FOLTerm] ) = {
    val groundingMap = getGroundingMap( seq )
    val groundSeq = FOLSubstitution( groundingMap )( seq )
    val unground = groundingMap.map { case ( f, t ) => ( t, f ) }.toMap[FOLTerm, FOLTerm]
    ( groundSeq, unground )
  }
}