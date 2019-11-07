package gapt

import gapt.utils.unorderedPairsOf
import gapt.expr.Const
import gapt.expr.Var
import gapt.expr.formula.Formula
import gapt.expr.formula.hol.universalClosure
import gapt.expr.ty.FunctionType
import gapt.proofs.context.update.InductiveType

package object logic {

  def disjointnessAxioms( inductiveType: InductiveType ): Iterable[Formula] = {
    unorderedPairsOf( inductiveType.constructors ).map {
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

}
