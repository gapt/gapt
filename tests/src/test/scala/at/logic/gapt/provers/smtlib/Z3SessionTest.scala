package at.logic.gapt.provers.smtlib

import at.logic.gapt.expr._
import at.logic.gapt.formats.lisp.{ LAtom, LFun, LList, SExpression }
import org.specs2.mutable._
import at.logic.gapt.provers.Session._
import cats.implicits._
import at.logic.gapt.utils.EitherHelpers._

class Z3SessionTest extends Specification {

  if ( !Z3.isInstalled ) skipAll

  "check sat of empty theory" in {
    Z3.runSession( checkSat ) must_== Right( true )
  }

  "validity of linear example" in {
    val nat = TBase( "nat" )
    val o = Const( "0", nat )
    val s = Const( "s", nat ->: nat )
    val p = Const( "p", nat ->: To )

    val numeral = Stream.iterate[Expr]( o )( s( _ ) )

    val n = 10

    val getUnsatCore = ask( LFun( "get-unsat-core" ) ) map {
      case LList( labels @ _* ) => labels map { case LAtom( l ) => l }
    }

    val session: Session[( Boolean, Boolean, Seq[String] )] = for {
      _ <- setOption( ":produce-unsat-cores", "true" )
      _ <- declareSymbolsIn( o, s, p )
      _ <- assert( Atom( p( o ) ) )
      _ <- ( 0 until ( 2 * n ) ).toList.map( i => ( p( numeral( i ) ) --> p( numeral( i + 1 ) ), s"hyp$i" ) ).traverse_( p => assert( p._1, p._2 ) )
      p <- withScope {
        for {
          _ <- assert( -p( numeral( n ) ) )
          sat <- checkSat
          labels <- getUnsatCore
        } yield ( sat.get, labels )
      }
      satOuter <- checkSat
    } yield ( p._1, satOuter.get, p._2 )

    val ( satInner, satOuter, labels ) = Z3.runSession( session )

    satInner must_== false
    satOuter must_== true
    labels must contain( exactly( 0 until n map { i => s"hyp$i" }: _* ) )
  }
}
