package at.logic.gapt.provers

import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.expansion.{ ETSkolemQuantifier, ExpansionProof }
import at.logic.gapt.proofs.lk.{ LKProof, SkolemQuantifierRule }
import at.logic.gapt.utils.NameGenerator

object renameConstantsToFi {
  private def mkName( i: Int ) = s"f$i"
  private def getRenaming[I, O]( obj: I )( implicit ev: Replaceable[I, O] ): Map[Const, Const] =
    getRenaming( containedNames( obj ).collect { case c: Const => c } )
  private def getRenaming( constants: Set[Const] ): Map[Const, Const] =
    constants.toSeq.zipWithIndex.map {
      case ( c @ EqC( _ ), _ ) => c -> c
      case ( c, i )            => c -> Const( mkName( i ), c.ty )
    }.toMap
  private def invertRenaming( map: Map[Const, Const] ) = map.map( _.swap )

  def wrap[I1, O1, I2, O2]( input: I1 )( func: ( Map[Const, Const], O1 ) => I2 )( implicit ev1: Replaceable[I1, O1], ev2: Replaceable[I2, O2] ): O2 = {
    val renaming = getRenaming( input )
    val renamedInput = TermReplacement( input, renaming.toMap )
    val renamedOutput = func( renaming, renamedInput )
    TermReplacement.hygienic( renamedOutput, renaming.map( _.swap ) )
  }
}

object groundFreeVariables {
  def getGroundingMap( vars: Set[Var], consts: Set[Const] ): Seq[( Var, Const )] = {
    val nameGen = rename.awayFrom( consts )
    vars.toSeq map { v => v -> Const( nameGen fresh v.name, v.ty ) }
  }

  def getGroundingMap( seq: HOLSequent ): Seq[( Var, Const )] =
    getGroundingMap( freeVariables( seq ), constants( seq ) )

  def apply( seq: HOLSequent ): ( HOLSequent, Map[Const, Var] ) = {
    val groundingMap = getGroundingMap( seq )
    val groundSeq = Substitution( groundingMap )( seq )
    val unground = groundingMap.map { case ( f, t ) => ( t, f ) }
    ( groundSeq, unground.toMap )
  }

  def wrapWithConsts[I, O]( seq: HOLSequent )( f: ( HOLSequent, Set[Const] ) => Option[I] )( implicit ev: Replaceable[I, O] ): Option[O] = {
    val ( renamedSeq, invertRenaming ) = groundFreeVariables( seq )
    f( renamedSeq, invertRenaming.keySet ) map { TermReplacement.hygienic( _, invertRenaming ) }
  }

  def wrap[I, O]( seq: HOLSequent )( f: HOLSequent => Option[I] )( implicit ev: Replaceable[I, O] ): Option[O] =
    wrapWithConsts( seq )( ( groundSeq, _ ) => f( groundSeq ) )

  def wrapAndPadSkolemFunctionsLK( seq: HOLSequent )( f: HOLSequent => Option[LKProof] ): Option[LKProof] =
    wrapWithConsts( seq ) { ( groundSeq, extraConsts ) =>
      f( groundSeq ).map { lk =>
        padSkolemFunctions( lk, extraConsts.toVector, rename.awayFrom( containedNames( lk ) ) )
      }
    }

  def wrapAndPadSkolemFunctionsET( seq: HOLSequent )( f: HOLSequent => Option[ExpansionProof] ): Option[ExpansionProof] =
    wrapWithConsts( seq ) { ( groundSeq, extraConsts ) =>
      f( groundSeq ).map { exp =>
        padSkolemFunctions( exp, extraConsts.toVector, rename.awayFrom( containedNames( exp ) ) )
      }
    }
}

object padSkolemFunctions {
  private def apply[T]( p: T, skConsts: Set[Const], extraConsts: Seq[Const],
                        nameGen: NameGenerator )( implicit r: Replaceable[T, T], s: ClosedUnderSub[T] ): T = {
    if ( skConsts.isEmpty ) return p
    val tmpVars = extraConsts.map { case Const( n, t ) => Var( nameGen.fresh( n ), t ) }
    val repl = skConsts.map {
      case c @ Const( n, t ) =>
        c -> Const( nameGen.fresh( n ), FunctionType( t, tmpVars.map( _.ty ) ) )( tmpVars ).
          ensuring( _.ty == t )
    } ++ extraConsts.zip( tmpVars )
    Substitution( tmpVars zip extraConsts )( TermReplacement( p, repl.toMap ) )
  }

  def apply( p: LKProof, extraConsts: Seq[Const], nameGen: NameGenerator ): LKProof = {
    val skConsts = p.subProofs.collect { case sk: SkolemQuantifierRule => sk.skolemConst }
    apply( p, skConsts, extraConsts, nameGen )
  }

  def apply( p: ExpansionProof, extraConsts: Seq[Const], nameGen: NameGenerator ): ExpansionProof = {
    val skConsts = p.skolemFunctions.skolemDefs.keySet
    apply( p, skConsts, extraConsts, nameGen )
  }
}