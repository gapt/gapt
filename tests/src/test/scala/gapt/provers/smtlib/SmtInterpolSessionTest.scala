package gapt.provers.smtlib

import gapt.expr._
import gapt.proofs.context.update.InductiveType
import gapt.provers.Session._
import gapt.formats.lisp.{ LFun, LList, LSymbol }
import org.specs2.mutable._
import cats.implicits._
import gapt.proofs.context.Context
import gapt.utils.EitherHelpers._

class SmtInterpolSessionTest extends Specification {

  "check sat of empty theory" in {
    SmtInterpol.runSession( checkSat ) must_== Right( true )
  }

  "push and pop" in {
    implicit var ctx = Context()
    ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    ctx += hoc"p: nat>o"

    SmtInterpol.runSession {
      for {
        _ <- declareSymbolsIn( ctx.constants )
        _ <- assert( hof"p 0 -> -p (s 0)" )
        sat1 <- withScope { assert( hof"p 0 & p (s 0)" ) *> checkSat }
        sat2 <- checkSat
        sat3 <- withScope { assert( hof"p 0 & 0 = s 0" ) *> checkSat }
      } yield ( sat1, sat2, sat3 )
    } must_== ( Right( false ), Right( true ), Right( false ) )
  }

  "validity of linear example" in {
    val nat = TBase( "nat" )
    val o = Const( "0", nat )
    val s = Const( "s", nat ->: nat )
    val p = Const( "p", nat ->: To )

    val numeral = Stream.iterate[Expr]( o )( s( _ ) )

    val n = 10

    val getUnsatCore = ask( LFun( "get-unsat-core" ) ) map {
      case LList( labels @ _* ) => labels map { case LSymbol( l ) => l }
    }

    val session: Session[( Boolean, Boolean, Seq[String] )] = for {
      _ <- setOption( "produce-unsat-cores", "true" )
      _ <- setLogic( "QF_UF" )
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

    val ( satInner, satOuter, labels ) = new SmtInterpolSession().run( session )

    satInner must_== false
    satOuter must_== true
    labels must contain( exactly( 0 until n map { i => s"hyp$i" }: _* ) )
  }
}
