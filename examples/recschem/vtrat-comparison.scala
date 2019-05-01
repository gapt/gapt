package gapt.examples.recschem

import gapt.examples.Script
import gapt.expr._
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFunction
import gapt.expr.formula.fol.FOLFunctionConst
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.fol.Numeral
import gapt.expr.formula.hol.lcomp
import gapt.grammars._
import gapt.logic.hol.simplify
import gapt.logic.hol.toNNF
import gapt.provers.maxsat.bestAvailableMaxSatSolver
import gapt.utils.{ LogHandler, time, verbose }

object vtrat_comparison extends Script {
  verbose {
    val N = 11
    val terms = ( 0 until N ).map { i => FOLFunction( "r", Numeral( i ), Numeral( N - i ) ) }.toSet

    val A = FOLConst( "A" )
    val B = FOLFunctionConst( "B", 2 )
    val Seq( x, y, z ) = Seq( "x", "y", "z" ) map { FOLVar( _ ) }
    val rst = RecSchemTemplate( A, A -> B( x, y ), A -> z, B( x, y ) -> z )
    val targets = terms.map( A -> _ ).toSet[( Expr, Expr )]
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
}
