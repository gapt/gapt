package gapt.examples

import gapt.expr._
import gapt.expr.formula._
import gapt.expr.formula.fol._
import gapt.proofs._
import gapt.provers.prover9._
import gapt.utils.{ TimeOutException, withTimeout }

import scala.concurrent.duration._

object groupexp {
  type word = List[FOLTerm]

  // group theory
  val assoc = fof"∀x ∀y ∀z f(x, f(y, z)) = f(f(x, y), z)"
  val lunit = fof"∀x f(e, x) = x"
  val runit = fof"∀x f(x, e) = x"
  val linv = fof"∀x f(g(x), x) = e"
  val rinv = fof"∀x f(x, g(x)) = e"

  // some LOT groups
  val G1 = List(
    Edge( 1, 2, 3 ),
    Edge( 3, 2, 4 ),
    Edge( 3, 4, 5 ),
    Edge( 5, 4, 3 ) )
  val G2 = List(
    Edge( 1, 5, 2 ),
    Edge( 2, 1, 3 ),
    Edge( 2, 3, 1 ),
    Edge( 4, 2, 5 ) )
  val G3 = List(
    Edge( 1, 5, 3 ),
    Edge( 1, 2, 4 ),
    Edge( 2, 3, 1 ),
    Edge( 2, 4, 5 ) )
  val G4 = List(
    Edge( 2, 1, 5 ),
    Edge( 3, 2, 4 ),
    Edge( 3, 4, 1 ),
    Edge( 5, 4, 3 ) )

  // options
  var ngen = 0 // the number of generators in our group
  var ax: List[FOLFormula] = Nil // axiomatisation of our group
  var timeout = 1 second // the timeout
  var verbose = true

  case class Edge( from: Int, to: Int, lbl: Int )

  def setGroup( ng: Int, rel: List[Edge] ) = {
    ngen = ng
    val group = rel map ( x => groupexp.LOGrel( x.from, x.to, x.lbl ) )
    ax = List( assoc, lunit, linv, runit, rinv ) ++ group
  }

  // check for equalities between generators
  def checkGenerators = {
    for { i <- 1 to ngen; j <- i + 1 to ngen }
      checkEquality( List( gen( i ) ), List( gen( j ) ) )
  }

  // find commuting words filtering out trivial cases
  // lu length of u
  // lv length of v
  // n max exponent for is-power-of check
  // TODO: additional filtering: rewrite words with f(x,g(x)) -> e and
  // f(g(x),x) -> e and with edges oriented in length-decreasing way and
  // with inverse of edge in length-decreasing way, check remaining words for
  // trivial cases u = e, v = e, u = v, u = g(v)
  def findCommutations( lu: Int, lv: Int, n: Int ) = {
    val U = generateWordsOfLength( lu )
    val V = generateWordsOfLength( lv )
    for { u <- U; v <- V } {
      vprint( "checking whether " + u + " and " + v + " commute..." )
      val seq = Sequent( ax, List( Eq( op( u ++ v ), op( v ++ u ) ) ) )
      if ( Prover9WithTimeout( seq ) ) {
        vprintln( "yes." )

        vprint( "checking whether " + u + " is a power of " + v + "..." )
        if ( IsPowerOf( u, v, n ) )
          vprintln( "yes." )
        else {
          vprintln( "no." )

          vprint( "checking whether " + v + " is a power of " + u + "..." )
          if ( IsPowerOf( v, u, n ) )
            vprintln( "yes." )
          else {
            vprintln( "no." )
            println( "! found commutation candidates: " + u + ", " + v )
          }
        }
      } else
        vprintln( "no." )
    }
  }

  // check commutation of a words of length lu with all words of length lv
  def checkCommutations( lu: Int, lv: Int ) = { // TODO filter out 1. duplicate checks and 2. trivial commutations
    val U = generateWordsOfLength( lu )
    val V = generateWordsOfLength( lv )
    for { u <- U; v <- V } checkCommutation( u, v )
  }

  // check if the two words u and v commute
  def checkCommutation( u: word, v: word ) = {
    checkEquality( u ++ v, v ++ u )
  }

  def checkEquality( u: word, v: word ) = {
    check( ax, Eq( op( u ), op( v ) ) )
  }

  def checkEdges = {
    // TODO filter out trivially true where f = t = l, filter out known edges
    for { f <- 1 to ngen; t <- 1 to ngen; l <- 1 to ngen }
      checkEdge( f, t, l )
  }

  // check if an edge is provable
  def checkEdge( from: Int, to: Int, lbl: Int ) = {
    check( ax, LOGrel( from, to, lbl ) )
  }

  // returns true iff a power-of relation could be established
  def IsPowerOf( u: word, v: word, n: Int ) = {
    var rv = false
    for ( i <- -n to n ) {
      val seq = Sequent( ax, List( Eq( op( u ), op( pow( v, i ) ) ) ) )
      rv = rv || Prover9WithTimeout( seq )
    }
    rv
  }

  // checks if u is a power of v from -n to n
  def checkIsPowerOf( u: word, v: word, n: Int ) = {
    for ( i <- -n to n )
      checkEquality( u, pow( v, i ) )
  }

  def generateWordsOfLength( l: Int ): List[word] = {
    if ( l == 1 ) {
      val el = ( 1 to ngen toList ) map ( x => List( gen( x ) ) )
      val invel = ( 1 to ngen toList ) map ( x => List( inv( gen( x ) ) ) )
      el ++ invel
    } else {
      for {
        x <- generateWordsOfLength( 1 );
        w <- generateWordsOfLength( l - 1 )
      } yield x ++ w
    }
  }

  def Prover9WithTimeout( seq: FOLSequent ) = {
    try withTimeout( timeout ) {
      Prover9 isValid seq
    } catch {
      case _: TimeOutException => false
    }
  }

  def check( ax: Seq[FOLFormula], goal: FOLFormula ) = {
    try withTimeout( timeout ) {
      if ( verbose ) print( "running prover9 on goal " + goal + "... " )
      val seq = Sequent( ax, List( goal ) )
      if ( Prover9 isValid seq )
        if ( verbose )
          println( "proof found" )
        else
          println( "found proof of " + goal )
      else if ( verbose ) println( "no proof found (prover terminated)" )
    } catch {
      case _: TimeOutException => if ( verbose ) println( "no proof found (timeout)" )
    }
  }

  // wrappers around group signature
  def unit = FOLFunction( "e" )
  def inv( w: FOLTerm ): FOLTerm = FOLFunction( "g", w )
  def inv( w: word ): word = w.reverse.map( inv( _ ) ) // FIXME: is not completely clean, may create inverses of inverses
  def gen( i: Int ) = FOLFunction( "a" + i )
  def op( w: word ): FOLTerm = {
    if ( w == Nil ) unit
    else if ( w.tail == Nil ) w.head
    else FOLFunction( "f", w.head, op( w.tail ) )
  }

  // returns the word w^n for an integer n
  def pow( w: word, n: Int ): word = {
    if ( n < 0 ) pow( inv( w ), -n )
    else if ( n == 0 ) Nil
    else w ++ pow( w, n - 1 )
  }

  // return FOLAtom defining LOG relation
  def LOGrel( from: Int, to: Int, lbl: Int ) = {
    val lhs = op( List( inv( gen( lbl ) ), gen( from ), gen( lbl ) ) )
    val rhs = gen( to )
    Eq( lhs, rhs )
  }

  private def vprint( s: String ) = if ( verbose ) print( s )
  private def vprintln( s: String ) = if ( verbose ) println( s )
}
