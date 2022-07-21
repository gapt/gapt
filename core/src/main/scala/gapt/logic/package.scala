package gapt

import gapt.utils.unorderedPairsOf
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.ReductionRule
import gapt.expr.Var
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Eq
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.hol.universalClosure
import gapt.expr.ty.FunctionType
import gapt.expr.ty.To
import gapt.expr.ty.Ty
import gapt.proofs.context.update.InductiveType

package object logic {

  def projectorDefinitions( it: InductiveType ): Iterable[Formula] = {
    it.constructors.flatMap( projectorDefinitions )
  }

  def projectorDefinitionRules( it: InductiveType ): Iterable[ReductionRule] =
    projectorDefinitions( it ) map {
      case All.Block( _, Eq( lhs, rhs ) ) => ReductionRule( lhs, rhs )
    }

  private def projectorDefinitions( constructor: InductiveType.Constructor ): Iterable[Formula] = {
    val c = constructor.constant
    val xs = argumentVariablesWithPatternFor( n => s"x$n" )( c )
    constructor.fields.zipWithIndex.flatMap {
      case ( f, i ) =>
        f.projector.map { p => All.Block( xs, p( c( xs ) ) === xs( i ) ) }
    }
  }

  def disjointnessAxioms( inductiveType: InductiveType ): Iterable[Formula] = {
    unorderedPairsOf( inductiveType.constructors.map( _.constant ) ).map {
      case ( c1, c2 ) => disjointnessAxiom( c1, c2 )
    }
  }

  def disjointnessAxiom( constructor1: Const, constructor2: Const ): Formula = {
    val vs1 = argumentVariablesWithPatternFor( j => s"x$j" )( constructor1 )
    val vs2 = argumentVariablesWithPatternFor( j => s"y$j" )( constructor2 )
    universalClosure( constructor1( vs1 ) !== constructor2( vs2 ) )
  }

  def argumentVariablesWithPatternFor( pattern: ( Int ) => String )( constant: Const ): Seq[Var] = {
    val FunctionType( _, ts ) = constant.ty
    ts.zipWithIndex.map { case ( t, j ) => Var( pattern( j ), t ) }
  }

  def injectivityAxioms( inductiveType: InductiveType ): Iterable[Formula] =
    inductiveType.constructors.map( _.constant )
      .filter( isPolyadic ).map { injectivityAxiom }

  def injectivityAxiom( constructor: Const ): Formula = {
    val vs1 = argumentVariablesWithPatternFor( n => s"x${n}" )( constructor )
    val vs2 = argumentVariablesWithPatternFor( n => s"y${n}" )( constructor )
    val conclusion = And( vs1.zip( vs2 ).map { case ( v1, v2 ) => v1 === v2 } )
    universalClosure(
      ( constructor( vs1 ) === constructor( vs2 ) ) --> conclusion )
  }

  def isPolyadic( constant: Const ): Boolean = {
    val FunctionType( _, ts ) = constant.ty
    ts.nonEmpty
  }

  object PredicateCongruence {
    def formula( p: Const ): Formula = {
      val FunctionType( to, from ) = p.ty
      require( to == To )
      val xs = from.zipWithIndex.map { case ( t, i ) => Var( s"x${i}", t ) }
      val ys = from.zipWithIndex.map { case ( t, i ) => Var( s"y${i}", t ) }
      All.Block( xs ++ ys, Imp( And( xs.zip( ys ).map { case ( x, y ) => Eq( x, y ) } :+ p( xs ) ), p( ys ) ) )
    }
  }
  object FunctionCongruence {
    def formula( f: Const ): Formula = {
      val FunctionType( _, from ) = f.ty
      val xs = from.zipWithIndex.map { case ( t, i ) => Var( s"x${i}", t ) }
      val ys = from.zipWithIndex.map { case ( t, i ) => Var( s"y${i}", t ) }
      All.Block( xs ++ ys, Imp( And( xs.zip( ys ).map { case ( x, y ) => Eq( x, y ) } ), Eq( f( xs ), f( ys ) ) ) )
    }
  }

  object EqualityTransitivity {
    def formula( t: Ty ): Formula = {
      val x = Var( "x", t )
      val y = Var( "y", t )
      val z = Var( "z", t )
      All.Block( Seq( x, y, z ), Imp( And( Eq( x, y ), Eq( y, z ) ), Eq( x, z ) ) )
    }
  }

  object EqualityReflexivity {
    def formula( t: Ty ): Formula = {
      val x = Var( "x", t )
      All( x, Eq( x, x ) )
    }
  }

  object AllDistinct {
    def apply( ts: Expr* ): Formula =
      And.nAry( unorderedPairsOf( ts ).map { case ( t1, t2 ) => Neg( Eq( t1, t2 ) ) }.toList: _* )
  }
}
