package gapt

import gapt.utils.unorderedPairsOf
import gapt.expr.Const
import gapt.expr.ReductionRule
import gapt.expr.Var
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Eq
import gapt.expr.formula.Formula
import gapt.expr.formula.hol.universalClosure
import gapt.expr.ty.FunctionType
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

}
