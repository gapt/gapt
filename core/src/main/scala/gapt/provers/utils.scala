package gapt.provers

import gapt.expr._
import gapt.expr.formula.Formula
import gapt.expr.formula.constants.EqC
import gapt.expr.subst.Substitution
import gapt.expr.ty.TBase
import gapt.expr.util.constants
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.expr.util.typeVariables
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.{ HOLSequent, Sequent }
import gapt.utils.{ Maybe, NameGenerator }

object mangleName {
  def apply( name: String, prefix: String = "f_" ): String = {
    var n = name
    n = prefix + n
    n = n.flatMap {
      case '*' => "m"
      case '+' => "p"
      case '-' => "s"
      case '/' => "d"
      case 'ν' => "n"
      case 'α' => "a"
      case 'γ' => "g"
      case c   => c.toString
    }
    n = n.filter {
      case c if 'a' <= c && c <= 'z' => true
      case c if 'A' <= c && c <= 'Z' => true
      case c if '0' <= c && c <= '9' => true
      case '_'                       => true
      case _                         => false
    }
    n = n.take( 10 )
    n
  }
}

object renameConstantsToFi {
  private def getRenaming[I, O]( obj: I )( implicit ev: Replaceable[I, O] ): Map[Const, Const] =
    getRenaming( containedNames( obj ).collect { case c: Const => c } )
  private def getRenaming( constants: Set[Const] ): Map[Const, Const] = {
    val nameGen = new NameGenerator( Set() )
    Map() ++ constants.view.map {
      case c @ EqC( _ ) => c -> c
      case c            => c -> Const( nameGen.fresh( mangleName( c.name ) ), c.ty )
    }.toMap
  }

  def apply[I, O]( input: I )( implicit ev: Replaceable[I, O] ): O =
    TermReplacement( input, getRenaming( input ).toMap )

  def wrap[I1, O1, I2, O2]( input: I1 )( func: ( Map[Const, Const], O1 ) => I2 )( implicit ev1: Replaceable[I1, O1], ev2: Replaceable[I2, O2] ): O2 = {
    val renaming = getRenaming( input )
    val renamedInput = TermReplacement( input, renaming.toMap )
    val renamedOutput = func( renaming, renamedInput )
    TermReplacement.hygienic( renamedOutput, renaming.map( _.swap ) )
  }
}

object groundFreeVariables {
  def getGroundingMap( vars: Set[Var], consts: Set[Const] ): Substitution = {
    val nameGen = rename.awayFrom( consts )
    val tyVars = typeVariables( vars ++ consts )
    // TODO(gabriel): fresh base types
    val tyGround = Substitution( Map(), tyVars.map( v => v -> TBase( v.name ) ) )
    Substitution( vars.toSeq map { v =>
      v -> Const( nameGen fresh v.name, tyGround( v.ty ) )
    }, tyGround.typeMap )
  }

  def getGroundingMap( seq: HOLSequent ): Substitution =
    getGroundingMap( freeVariables( seq ), constants( seq ) )

  def apply( seq: HOLSequent ): ( HOLSequent, Substitution ) = {
    val groundingMap = getGroundingMap( seq )
    val groundSeq = groundingMap( seq )
    ( groundSeq, groundingMap )
  }
  def apply( formula: Formula ): ( Formula, Substitution ) = {
    val ( Sequent( _, Seq( groundFormula ) ), unground ) = apply( Sequent() :+ formula )
    ( groundFormula, unground )
  }

  def wrapWithConsts[T: ClosedUnderReplacement]( seq: HOLSequent )( f: ( HOLSequent, Set[Const] ) => Option[T] ): Option[T] = {
    val ( renamedSeq, invertRenaming ) = groundFreeVariables( seq )
    f( renamedSeq, constants( invertRenaming.range ) ).map( TermReplacement.undoGrounding( _, invertRenaming ) )
  }

  def wrap[T: ClosedUnderReplacement]( seq: HOLSequent )( f: HOLSequent => Option[T] ): Option[T] = {
    val ( renamedSeq, invertRenaming ) = groundFreeVariables( seq )
    f( renamedSeq ).map( TermReplacement.undoGrounding( _, invertRenaming ) )
  }
}

object extractIntroducedDefinitions {
  import gapt.proofs.resolution._
  def apply( p: ResolutionProof )( implicit maybeCtx: Maybe[MutableContext] ): Unit =
    maybeCtx match {
      case Maybe.None =>
      case Maybe.Some( ctx ) =>
        for ( ( df, by ) <- p.definitions if ctx.definition( df ).isEmpty )
          ctx += Definition( df, by )
    }
}
