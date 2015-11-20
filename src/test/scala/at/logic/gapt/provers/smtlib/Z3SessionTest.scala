package at.logic.gapt.provers.smtlib

import at.logic.gapt.expr._
import org.specs2.mutable._

class Z3SessionTest extends Specification {

  if ( !Z3.isInstalled ) skipAll

  "check sat of empty theory" in {
    for ( session <- Z3.startIncrementalSession() )
      yield session.checkSat() must_== true
  }

  "validity of linear example" in {
    val nat = TBase( "nat" )
    val o = Const( "0", nat )
    val s = Const( "s", nat -> nat )
    val p = Const( "p", nat -> To )

    val numeral = Stream.iterate[LambdaExpression]( o )( s( _ ) )

    for ( session <- Z3.startIncrementalSession() ) yield {
      session.produceUnsatCores()
      session declareSymbolsIn ( o, s, p )

      val n = 10
      session assert HOLAtom( p( o ) )
      for ( i <- 0 until ( 2 * n ) )
        session assert ( p( numeral( i ) ) --> p( numeral( i + 1 ) ), s"hyp$i" )
      session withScope {
        session assert -p( numeral( n ) )
        session.checkSat() must_== false
        session.getUnsatCore() must contain( exactly( 0 until n map { i => s"hyp$i" }: _* ) )
      }
      session.checkSat() must_== true
    }
  }
}
