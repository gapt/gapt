// This package implements formula and proof Skolemization.
package at.logic.transformations.skolemization

import at.logic.utils.logging.Logger
import scala.collection.mutable.{Map,HashMap}
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.base.{LKProof,Sequent,SequentOccurrence}
import at.logic.language.hol._
import at.logic.language.lambda.types._
import at.logic.language.lambda._
import at.logic.language.lambda.substitutions._
import at.logic.algorithms.lksk.applySubstitution
import at.logic.algorithms.lk.getCutAncestors
import at.logic.language.hol.logicSymbols.ConstantStringSymbol

object skolemize {

  def apply(p: LKProof) : LKProof = 
  {
    val sk_s = skolemize( p.root )
    skolemize( p, sk_s._1, sk_s._2, sk_s._3 )._1
  }

  def skolemize(p: LKProof, sk_s: Sequent, map_ant: Map[FormulaOccurrence, Int],
                map_succ: Map[FormulaOccurrence, Int] ) : (LKProof, Map[FormulaOccurrence, FormulaOccurrence]) = p match
  {
    case Axiom(s) => {
      val ax = Axiom( sk_s )
      val map = new HashMap[FormulaOccurrence, FormulaOccurrence]()
      // TODO: notation? p is a pair, but we cannot write (fo, i) for p...
      map_ant.foreach( p => map += ( p._1 -> ax._2._1(p._2) ) )
      map_succ.foreach( p => map += ( p._1 -> ax._2._2(p._2) ) )
      (ax._1, map)
    }
  }

  def skolemize(s: SequentOccurrence) : (Sequent, Map[FormulaOccurrence, Int], Map[FormulaOccurrence, Int]) =
  {
    val ant = s.antecedent.toList
    val succ = s.succedent.toList

    val sk_ant = ant.map( fo => apply( fo.formula, 1 ) )
    val sk_succ = succ.map( fo => apply( fo.formula, 0 ) )
    
    val map_ant = new HashMap[FormulaOccurrence, Int]()
    for (i <- ant.indices)
      map_ant += (ant(i) -> i)
  
    val map_succ = new HashMap[FormulaOccurrence, Int]()
    for (i <- succ.indices)
      map_succ += (succ(i) -> i)

    (Sequent(sk_ant, sk_succ), map_ant, map_succ)
  }

  def skolem_symbol_stream(n: Int): Stream[ConstantStringSymbol] =
    Stream.cons(ConstantStringSymbol( "s_" + n ) , skolem_symbol_stream( n + 1 ) )

  def skolem_symbol_stream : Stream[ConstantStringSymbol]= skolem_symbol_stream( 0 )

  // TODO: in Scala 2.8 there is +: which can be used instead of Stream.cons
  def even[A]( s: Stream[A] ) : Stream[A] = Stream.cons( s.head, even(s.tail.tail) )

  def odd[A]( s: Stream[A] ) : Stream[A] = Stream.cons( s.tail.head, odd(s.tail.tail) )

  def invert( pol: Int ) = 
    if (pol == 0)
      1
    else
      0

  def apply(f: HOLFormula, pol: Int) = sk( f, pol, Nil, skolem_symbol_stream )

  def sk(f: HOLFormula, pol: Int, vars: List[HOLVar], symbols: Stream[ConstantStringSymbol]) : HOLFormula = f match {
    case And(l, r) => And( sk( l , pol, vars, even( symbols ) ), sk( r, pol, vars, odd( symbols ) ) )
    case Or(l, r) => Or( sk( l , pol, vars, even( symbols ) ), sk( r, pol, vars, odd( symbols ) ) )
    case Imp(l, r) => Imp( sk( l , invert( pol ), vars, even( symbols ) ), sk( r, pol, vars, odd( symbols ) ) )
    case Neg(f) => Neg( sk( f, invert( pol ), vars, symbols ) )
    case ExVar(x, f) =>
      if (pol == 1)
      {
        val sub = Substitution(x, Function( symbols.head, vars, x.exptype ) )
        // TODO: should not be necessary to cast here, Formula is closed under substitution
        sk( sub( f ).asInstanceOf[HOLFormula], pol, vars, symbols.tail )
      }
      else // TODO: should not be necessary to cast! try to change it in hol.scala.
        ExVar(x, sk( f, pol, vars + x.asInstanceOf[HOLVar], symbols ) )
    case AllVar(x, f) =>
      if (pol == 0)
      {
        val sub = Substitution(x, Function( symbols.head, vars, x.exptype ) )
        println("Substituting!")
        println( sub )
        // TODO: should not be necessary to cast here, Formula is closed under substitution
        sk( sub( f ).asInstanceOf[HOLFormula], pol, vars, symbols.tail )
      }
      else // TODO: should not be necessary to cast! try to change it in hol.scala.
      {
        println("Not substituting!")
        AllVar(x, sk( f, pol, vars + x.asInstanceOf[HOLVar], symbols ) )
      }
    case Atom(_,_) => f
  }
}
