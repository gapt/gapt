package at.logic.gapt.provers

import at.logic.gapt.algorithms.rewriting.NameReplacement
import at.logic.gapt.algorithms.rewriting.NameReplacement.SymbolMap
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.proofs.{ HOLSequent, HOLClause }

object renameConstantsToFi {
  private def mkName( i: Int ) = s"f$i"
  private def getRenaming( seq: HOLSequent ): Map[Const, String] = getRenaming( constants( seq ) )
  private def getRenaming( cnf: List[HOLClause] ): Map[Const, String] =
    getRenaming( cnf.flatMap( constants( _ ) ).toSet )
  private def getRenaming( constants: Set[Const] ): Map[Const, String] =
    constants.toSeq.zipWithIndex.map {
      case ( c, i ) => c -> mkName( i )
    }.toMap
  private def renamingToSymbolMap( renaming: Map[Const, String] ): SymbolMap =
    renaming.map {
      case ( FOLAtomHead( c, arity ), newName )     => c -> ( arity, newName )
      case ( FOLFunctionHead( c, arity ), newName ) => c -> ( arity, newName )
    }
  private def invertRenaming( map: SymbolMap ) =
    map.map { case ( from, ( arity, to ) ) => ( to, ( arity, from ) ) }

  def apply( seq: HOLSequent ): ( HOLSequent, Map[Const, String], SymbolMap ) = {
    val renaming = getRenaming( seq )
    val map = renamingToSymbolMap( renaming )
    val renamedSeq = NameReplacement( seq, map )
    ( renamedSeq, renaming, invertRenaming( map ) )
  }
  def apply( cnf: List[HOLClause] ): ( List[HOLClause], Map[Const, String], SymbolMap ) = {
    val renaming = getRenaming( cnf )
    val map = renamingToSymbolMap( renaming )
    val renamedCNF = cnf.map( clause => NameReplacement( clause, map ) )
    ( renamedCNF, renaming, invertRenaming( map ) )
  }
}

object groundFreeVariables {
  def getGroundingMap( vars: Set[Var], consts: Set[Const] ): Seq[( Var, Const )] = {
    val varList = vars.toList
    ( varList, getRenaming( varList.map( _.sym ), consts.map( _.sym ).toList ) ).zipped.map {
      case ( v: FOLVar, cs ) =>
        v -> FOLConst( cs.toString )
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