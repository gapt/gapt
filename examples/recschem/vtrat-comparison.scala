package at.logic.gapt.examples.recschem

import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.Numeral
import at.logic.gapt.expr.hol.{ lcomp, simplify, toNNF }
import at.logic.gapt.grammars._
import at.logic.gapt.provers.maxsat.bestAvailableMaxSatSolver
import at.logic.gapt.utils.{ PrintMetrics, metrics, time }

object vtrat_comparison extends Script {
  metrics.current.value = PrintMetrics

  val N = 11
  val terms = ( 0 until N ).map { i => FOLFunction( "r", Numeral( i ), Numeral( N - i ) ) }.toSet

  val A = FOLConst( "A" )
  val B = FOLFunctionConst( "B", 2 )
  val Seq( x, y, z ) = Seq( "x", "y", "z" ) map { FOLVar( _ ) }
  val rst = RecSchemTemplate( A, A -> B( x, y ), A -> z, B( x, y ) -> z )
  val targets = terms.map( A -> _ ).toSet[( LambdaExpression, LambdaExpression )]
  val nfRecSchem = rst.stableRecSchem( targets )

  println( lcomp( simplify( toNNF( ( new RecSchemGenLangFormula( nfRecSchem ) )( targets ) ) ) ) )

  val nfG = stableVTRATG( terms.toSet, Seq( 2 ) )
  println( lcomp( simplify( toNNF( new VectGrammarMinimizationFormula( nfG ).coversLanguage( terms ) ) ) ) )

  val minimized = time { minimizeRecursionScheme( nfRecSchem, targets, solver = bestAvailableMaxSatSolver ) }
  println( minimized )
  println( terms.toSet diff minimized.language )
  println( recSchemToVTRATG( minimized ) )

  val minG = time { minimizeVTRATG( nfG, terms.toSet, bestAvailableMaxSatSolver ) }
  println( minG )
}
