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

  // relations of some LOT groups
  val G1rel = List(
    LOGrel( 1, 2, 3 ),
    LOGrel( 3, 2, 4 ),
    LOGrel( 3, 4, 5 ),
    LOGrel( 5, 4, 3 ) )
  val G2rel = List(
    LOGrel( 1, 5, 2 ),
    LOGrel( 2, 1, 3 ),
    LOGrel( 2, 3, 1 ),
    LOGrel( 4, 2, 5 ) )
  val G3rel = List(
    LOGrel( 1, 5, 3 ),
    LOGrel( 1, 2, 4 ),
    LOGrel( 2, 3, 1 ),
    LOGrel( 2, 4, 5 ) )

  // options
  var ngen = 5 // the number of generators in our group
  var group = G1rel // (the relations of) our group
  var ax = List( assoc, lunit, linv, runit, rinv ) ++ group // axiomatisation of our group
  var timeout = 1 second // the timeout

  // check for equalities between generators
  def checkGenerators = {
    for { i <- 1 to ngen; j <- i + 1 to ngen }
      checkEquality( List( gen( i ) ), List( gen( j ) ) )
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
    // TODO filter out trivially true where f = t = l
    for { f <- 1 to ngen; t <- 1 to ngen; l <- 1 to ngen }
      checkEdge( f, t, l )
  }

  // check if an edge is provable
  def checkEdge( from: Int, to: Int, lbl: Int ) = {
    check( ax, LOGrel( from, to, lbl ) )
  }

  // checks if u is a power of v from 0 to n
  def checkIsPowerOf( u: word, v: word, n: Int ) = {
    for ( i <- 0 to n )
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

  def check( ax: Seq[FOLFormula], goal: FOLFormula ) = {
    try withTimeout( timeout ) {
      print( "running prover9 on goal " + goal + "... " )
      val seq = Sequent( ax, List( goal ) )
      if ( Prover9 isValid seq )
        println( "proof found" )
      else
        println( "no proof found (prover terminated)" )
    } catch {
      case _: TimeOutException => println( "no proof found (timeout)" )
    }
  }

  // wrappers around group signature
  def unit = FOLFunction( "e" )
  def inv( w: FOLTerm ) = FOLFunction( "g", w )
  def gen( i: Int ) = FOLFunction( "a" + i )
  def op( w: word ): FOLTerm = {
    if ( w == Nil ) unit
    else if ( w.tail == Nil ) w.head
    else FOLFunction( "f", w.head, op( w.tail ) )
  }

  // returns the word w^n
  def pow( w: word, n: Int ): word = {
    if ( n == 0 ) Nil
    else if ( n == 1 ) w
    else w ++ pow( w, n - 1 )
  }

  // return FOLAtom defining LOG relation
  def LOGrel( from: Int, to: Int, lbl: Int ) = {
    val lhs = op( List( inv( gen( lbl ) ), gen( from ), gen( lbl ) ) )
    val rhs = gen( to )
    Eq( lhs, rhs )
  }

}
