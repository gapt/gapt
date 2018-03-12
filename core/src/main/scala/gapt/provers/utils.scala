package gapt.provers

import gapt.expr._
import gapt.proofs.{ HOLSequent, MutableContext }
import gapt.utils.{ Maybe, NameGenerator }

import scala.collection.mutable

object mangleName {
  def apply( name: String, prefix: String = "f_" ): String = {
    var n = name
    n = prefix + n
    n = n.flatMap {
      case '*' => "m"
      case '+' => "p"
      case '-' => "s"
      case '/' => "d"
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
  def getGroundingMap( vars: Set[Var], consts: Set[Const] ): Seq[( Var, Const )] = {
    val nameGen = rename.awayFrom( consts )
    vars.toSeq map { v =>
      val tvs = typeVariables( v ).toList
      v -> Const( nameGen fresh v.name, v.ty, tvs )
    }
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
