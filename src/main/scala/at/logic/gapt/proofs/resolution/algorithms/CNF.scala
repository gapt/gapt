package at.logic.gapt.proofs.resolution.algorithms

import at.logic.gapt.language.fol._
import at.logic.gapt.language.hol._
import at.logic.gapt.language.hol.logicSymbols.{ TopSymbol, BottomSymbol }
import at.logic.gapt.language.lambda.symbols.{ StringSymbol, SymbolA }
import at.logic.gapt.proofs.resolution.FClause
import scala.annotation.tailrec
import scala.collection.mutable

/**
 * Computes a clause set which is logically equivalent to the HOLFormula f by
 * expanding it using distributivity.
 */
object CNFp {
  /**
   * @param f a HOLFormula which is regular and does not contain strong quantifiers
   */
  def apply( f: HOLFormula ): List[FClause] = transform( f ).distinct

  def transform( f: HOLFormula ): List[FClause] = f match {
    case HOLBottomC         => List( FClause( List(), List() ) )
    case HOLTopC            => List()
    case HOLAtom( _, _ )    => List( FClause( List(), List( f ) ) )
    case HOLNeg( f2 )       => CNFn.transform( f2 )
    case HOLAnd( f1, f2 )   => CNFp.transform( f1 ) ++ CNFp.transform( f2 )
    case HOLOr( f1, f2 )    => times( CNFp.transform( f1 ), CNFp.transform( f2 ) )
    case HOLImp( f1, f2 )   => times( CNFn.transform( f1 ), CNFp.transform( f2 ) )
    case HOLAllVar( _, f2 ) => CNFp.transform( f2 )
    case _                  => throw new IllegalArgumentException( "unknown head of formula: " + f.toString )
  }
}

/**
 * Computes a clause set which is logically equivalent to the negation of
 * the HOLFormula f by expanding it using distributivity.
 */
object CNFn {
  /**
   * @param f a HOLFormula which is regular and does not contain strong quantifiers
   */
  def apply( f: HOLFormula ): List[FClause] = transform( f ).distinct

  def transform( f: HOLFormula ): List[FClause] = f match {
    case HOLBottomC        => List()
    case HOLTopC           => List( FClause( List(), List() ) )
    case HOLAtom( _, _ )   => List( FClause( List( f ), List() ) )
    case HOLNeg( f2 )      => CNFp.transform( f2 )
    case HOLAnd( f1, f2 )  => times( CNFn.transform( f1 ), CNFn.transform( f2 ) )
    case HOLOr( f1, f2 )   => CNFn.transform( f1 ) ++ CNFn.transform( f2 )
    case HOLImp( f1, f2 )  => CNFp.transform( f1 ) ++ CNFn.transform( f2 )
    case HOLExVar( _, f2 ) => CNFn.transform( f2 )
    case _                 => throw new IllegalArgumentException( "unknown head of formula: " + f.toString )
  }
}

private object times {
  def apply( s1: List[FClause], s2: List[FClause] ): List[FClause] = {
    s1.flatMap( c1 => s2.map( c2 => c1 compose c2 ) )
  }
}

object TseitinCNF {
  /**
   * Generates from a formula f a List of FClauses in CNF by using Tseitin's Transformation
   * @param f formula which should be transformed
   * @return CNF satisfiability-equivalent to f
   */
  def apply( f: FOLFormula ): List[FClause] = {
    val tseitin = new TseitinCNF()

    val clauses = getConjuncts( removeTopAndBottom( toNNF( f ) ) ) flatMap { c => tseitin.transform( c ) }
    clauses toList
  }
}

object getConjuncts {
  def apply( f: FOLFormula ): Set[FOLFormula] = f match {
    case FOLAnd( x, y ) => getConjuncts( x ) union getConjuncts( y )
    case x              => Set( x )
  }
}

class TseitinCNF {

  // add already known subformulas
  val subformulaMap = mutable.Map[FOLFormula, FOLFormula]()

  val hc = StringSymbol( "x" )
  var fsyms = Set[SymbolA]()
  var auxsyms = mutable.MutableList[SymbolA]()
  /**
   * Get a list of all Atoms symbols used in f
   * @param f formula
   * @return List of all atom symbols used in f
   */
  def getAtomSymbols( f: FOLFormula ): List[SymbolA] = f match {
    case FOLAtom( h, args ) => List( h )
    case FOLNeg( f2 )       => getAtomSymbols( f2 )
    case FOLAnd( f1, f2 )   => getAtomSymbols( f1 ) ::: getAtomSymbols( f2 )
    case FOLOr( f1, f2 )    => getAtomSymbols( f1 ) ::: getAtomSymbols( f2 )
    case FOLImp( f1, f2 )   => getAtomSymbols( f1 ) ::: getAtomSymbols( f2 )
    case FOLExVar( _, f2 )  => getAtomSymbols( f2 )
    case FOLAllVar( _, f2 ) => getAtomSymbols( f2 )
    case _                  => throw new IllegalArgumentException( "unknown head of formula: " + f.toString )
  }

  def transform( f: FOLFormula ): List[FClause] = {
    // take an arbitrary atom symbol and rename it
    // s.t. it does not occur anywhere in f
    fsyms = getAtomSymbols( f ) toSet

    // parseFormula and transform it via Tseitin-Transformation
    val pf = parseFormula( f )
    val extraDefs =
      if ( fsyms.contains( TopSymbol ) || fsyms.contains( BottomSymbol ) )
        getConstantDefs()
      else
        Nil
    ( pf._2 ++ extraDefs ) :+ FClause( List(), List( pf._1 ) )
  }

  private def getConstantDefs() = FClause( List(), List( FOLTopC ) ) :: FClause( List( FOLBottomC ), List() ) :: Nil

  /**
   * Adds a FOLFormula to fol.Atom map to the subFormulas HashMap, iff
   * the subformula does not already map to an existing atom.
   * The representing atom is returned.
   * In case f is an atom itself, nothing will be added to the subformulas HashMap and the atom itself is return as 1st/2nd
   * @param f subformula to possibly be added to subformulas HashMap
   * @return an atom either representing the subformula or f if f is already an atom
   */
  private var auxCounter: Int = 0
  @tailrec
  private def addIfNotExists( f: FOLFormula ): FOLFormula = f match {
    case FOLAtom( h, args ) => f
    case _ =>
      if ( subformulaMap.isDefinedAt( f ) ) {
        subformulaMap( f )
      } else {
        auxCounter += 1
        var auxsym = StringSymbol( s"$hc$auxCounter" )
        if ( fsyms.contains( auxsym ) ) {
          addIfNotExists( f )
        } else {
          auxsyms += auxsym
          val auxAtom = FOLAtom( auxsym )
          subformulaMap( f ) = auxAtom
          auxAtom
        }
      }
  }

  /**
   * Takes a propositional FOLFormula and parses it s.t. every subformula gets
   * assigned a freshly introduced Atom which is from there on used instead of the formula
   * @param f The formula to be parsed.
   * @return a Tuple2, where 1st is the prop. variable representing the formula in 2nd
   */
  def parseFormula( f: FOLFormula ): Tuple2[FOLFormula, List[FClause]] = f match {
    case FOLAtom( _, _ ) => ( f, List() )
    case FOLNeg( f2 ) =>
      val pf = parseFormula( f2 )
      val x = addIfNotExists( f )
      val x1 = pf._1
      val c1 = FClause( List( x, x1 ), List() )
      val c2 = FClause( List(), List( x, x1 ) )
      ( x, pf._2 ++ List( c1, c2 ) )

    case FOLAnd( f1, f2 ) =>
      val pf1 = parseFormula( f1 )
      val pf2 = parseFormula( f2 )
      val x = addIfNotExists( f )
      val x1 = pf1._1
      val x2 = pf2._1
      val c1 = FClause( List( x ), List( x1 ) )
      val c2 = FClause( List( x ), List( x2 ) )
      val c3 = FClause( List( x1, x2 ), List( x ) )
      ( x, pf1._2 ++ pf2._2 ++ List( c1, c2, c3 ) )

    case FOLOr( f1, f2 ) =>
      val pf1 = parseFormula( f1 )
      val pf2 = parseFormula( f2 )
      val x = addIfNotExists( f )
      val x1 = pf1._1
      val x2 = pf2._1
      val c1 = FClause( List( x1 ), List( x ) )
      val c2 = FClause( List( x2 ), List( x ) )
      val c3 = FClause( List( x ), List( x1, x2 ) )
      ( x, pf1._2 ++ pf2._2 ++ List( c1, c2, c3 ) )

    case FOLImp( f1, f2 ) =>
      val pf1 = parseFormula( f1 )
      val pf2 = parseFormula( f2 )
      val x = addIfNotExists( f )
      val x1 = pf1._1
      val x2 = pf2._1
      val c1 = FClause( List(), List( x, x1 ) )
      val c2 = FClause( List( x2 ), List( x ) )
      val c3 = FClause( List( x, x1 ), List( x2 ) )
      ( x, pf1._2 ++ pf2._2 ++ List( c1, c2, c3 ) )

    case _ => throw new IllegalArgumentException( "Formula not supported in Tseitin transformation: " + f.toString )
  }
}
