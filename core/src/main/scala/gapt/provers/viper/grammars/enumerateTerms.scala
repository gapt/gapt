package gapt.provers.viper.grammars

import cats.instances.list._
import cats.syntax.traverse._
import gapt.expr.VarOrConst
import gapt.expr._
import gapt.expr.ty.FunctionType
import gapt.expr.ty.TBase
import gapt.expr.ty.Ty
import gapt.expr.ty.baseTypes
import gapt.proofs.context.Context
import gapt.proofs.context.facet.BaseTypes
import gapt.proofs.context.facet.StructurallyInductiveTypes
import gapt.utils.NameGenerator

import scala.collection.mutable

object enumerateTerms {

  private def normalizeFreeVars( expr: Expr ): Expr = {
    val nameGen = new NameGenerator( Set() )
    def norm( e: Expr ): Expr = e match {
      case App( a, b ) => App( norm( a ), norm( b ) )
      case Var( _, t ) => Var( nameGen.freshWithIndex( "x" ), t )
      case c: Const    => c
    }
    norm( expr )
  }

  def constructorsForType( t: Ty* )( implicit ctx: Context ): Set[VarOrConst] = {
    val done = mutable.Set[Ty]()
    val out = Set.newBuilder[VarOrConst]
    def go( t: Ty ): Unit = if ( !done( t ) ) {
      done += t
      ctx.getConstructors( t ) match {
        case Some( ctrs ) =>
          for ( ctr <- ctrs ) {
            out += ctr
            val FunctionType( _, fields ) = ctr.ty
            fields.foreach( go )
          }
        case None =>
          out += Var( "x", t )
      }
    }
    t.foreach( go )
    out.result()
  }

  def freeConstructorsForType( ts: Ty* )( implicit ctx: Context ): Set[VarOrConst] =
    ts.flatMap( t => ctx.getConstructors( t ) match {
      case Some( ctrs ) =>
        ctrs ++ ( ctrs.map( _.ty ).flatMap( baseTypes( _ ) ).toSet[Ty] diff ts.toSet ).map( Var( "x", _ ) )
      case None =>
        Seq( Var( "x", t ) )
    } ).toSet

  def asStream( implicit ctx: Context ): LazyList[Expr] = withSymbols( Set.empty
    ++ ctx.get[StructurallyInductiveTypes].constructors.values.flatten
    ++ ( ctx.get[BaseTypes].baseTypes -- ctx.get[StructurallyInductiveTypes].constructors.keySet ).values.map( Var( "x", _ ) ) )

  def forType( ty: Ty* )( implicit ctx: Context ): LazyList[Expr] =
    forType( freeConstructors = false, ty: _* )

  def forType( freeConstructors: Boolean, ty: Ty* )( implicit ctx: Context ): LazyList[Expr] =
    withSymbols( if ( freeConstructors ) freeConstructorsForType( ty: _* )
    else constructorsForType( ty: _* ) )

  def withSymbols( syms: Set[VarOrConst] ): LazyList[Expr] = {
    val nonConstantCtrs = syms.filter( sym => sym.isInstanceOf[Const] && !sym.ty.isInstanceOf[TBase] )

    val terms = mutable.Set[Expr]()
    terms ++= ( syms diff nonConstantCtrs )

    def take( tys: Seq[Ty] ): Seq[Seq[Expr]] =
      tys.toList.traverse( t => terms.filter( _.ty == t ).toList )
    def iterate() =
      nonConstantCtrs.flatMap {
        case ctr @ Const( _, FunctionType( _, argTypes ), _ ) =>
          take( argTypes ).map( ctr( _ ) ).map( normalizeFreeVars )
      }

    ( terms.toVector +: LazyList.continually {
      val newTerms = iterate().filterNot( terms )
      terms ++= newTerms
      newTerms
    } ).takeWhile( _.nonEmpty ).flatten
  }

}
