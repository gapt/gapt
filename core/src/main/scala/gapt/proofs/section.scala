package gapt.proofs

import gapt.expr._
import gapt.proofs.context.ImmutableContext
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.{ ConstantDeclaration => ConstDecl }
import gapt.proofs.context.update.{ SkolemFunction => SkolemFun }
import gapt.proofs.context.update.Update

import scala.collection.mutable

class ContextSection( ctx: MutableContext ) {
  private val initialCtx: ImmutableContext = ctx.ctx
  private val parameters = mutable.Map[Const, Var]()

  def addParameter( c: Const, v: Var ): Unit = {
    ctx += c
    parameters( c ) = v
  }

  def groundSequent( seq: HOLSequent ): HOLSequent = {
    val nameGen = ctx.newNameGenerator
    val grounding = Substitution(
      for ( v @ Var( n, t ) <- freeVariables( seq ) ) yield {
        val tvs = typeVariables( t ).toList
        val c = Const( nameGen.fresh( n ), t, tvs )
        addParameter( c, v )
        v -> c
      } )
    grounding( seq )
  }

  def revert[T, S]( t: T )( implicit ev: Replaceable[T, S] ): S = {
    val updatesSinceSectionBegin = ctx.updates.dropRight( initialCtx.updates.size )
    ctx.ctx = initialCtx
    val repl = revertParameters( updatesSinceSectionBegin, parameters.toMap )( ctx )
    TermReplacement.hygienic( t, repl )
  }
}

object withSection {
  def apply[T, S]( f: ContextSection => T )( implicit ctx: MutableContext, ev: Replaceable[T, S] ): S = {
    val section = new ContextSection( ctx )
    val t = f( section )
    section.revert( t )
  }
}

object revertParameters {
  def apply( update: Update, replacements: Map[Const, Expr] )( implicit ctx: MutableContext ): Map[Const, Expr] =
    update match {
      case ConstDecl( c ) if replacements contains c =>
        replacements

      case Definition( what0, by0 ) =>
        val by = TermReplacement.hygienic( by0, replacements )
        val fvs = freeVariables( by ).toList
        if ( fvs.isEmpty ) {
          ctx += Definition( what0, by )
          replacements
        } else {
          val by1 = Abs( fvs, by )
          val tvs1 = typeVariables( by1 ).toList
          val what1 = Const( what0.name, FunctionType( what0.ty, fvs.map( _.ty ) ), tvs1 )
          ctx += Definition( what1, by1 )
          replacements + ( what0 -> Apps( what1, fvs ) )
        }

      case SkolemFun( sym0, defn0 ) =>
        val defn = TermReplacement.hygienic( defn0, replacements )
        val fvs = freeVariables( defn ).toList
        if ( fvs.isEmpty ) {
          ctx += SkolemFun( sym0, defn )
          replacements
        } else {
          val defn1 = Abs( fvs, defn )
          val sym1 = Const( sym0.name, FunctionType( sym0.ty, fvs.map( _.ty ) ) )
          ctx += SkolemFun( sym1, defn1 )
          replacements + ( sym0 -> Apps( sym1, fvs ) )
        }

      case _ =>
        ctx += update
        replacements
    }

  def apply( updates: List[Update], replacements: Map[Const, Expr] )( implicit ctx: MutableContext ): Map[Const, Expr] =
    updates.foldRight( replacements )( ( up, repl ) => revertParameters( up, repl ) )
}