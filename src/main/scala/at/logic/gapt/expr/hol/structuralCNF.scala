package at.logic.gapt.expr.hol

import at.logic.gapt.expr._
import at.logic.gapt.proofs._

import scala.collection.mutable

object structuralCNF {

  def apply( formula: HOLFormula ): ( Set[HOLClause], Map[HOLAtomConst, LambdaExpression] ) = {
    val cnf = mutable.Set[HOLClause]()
    val defs = mutable.Map[LambdaExpression, HOLAtomConst]()

    val symsInFormula = constants( formula ) map { _.name }
    val skolemSyms = new SkolemSymbolFactory().getSkolemSymbols.map { _.toString() }.filter { s => !symsInFormula.contains( s ) }.iterator
    val abbrevSyms = Stream.from( 0 ).map { i => s"X$i" }.filter { s => !symsInFormula.contains( s ) }.iterator

    // We do a clausification similar to forward proof search in Ral.
    // (But we handle Skolemization more as an afterthought here.)

    // Since we want a CNF of formula, we start with the singleton set of sequents (:- formula).
    expand( Sequent() :+ formula )

    // If we interpret the sequents in this set as a disjunction, their conjunction is equivalent to the original formula.
    // In each step we simplify the sequents in this set and make them more like clauses.

    // First we expand the connectives which correspond to nested disjunctions, e.g. (:- a|b) turns into (:- a, b).
    def expand( seq: HOLSequent ): Unit = {
      val ant = mutable.Set[HOLFormula]()
      val suc = mutable.Set[HOLFormula]()
      lazy val freeVars = mutable.Set[Var]( freeVariables( seq ).toSeq: _* )
      var trivial = false

      def left( f: HOLFormula ): Unit = f match {
        case All( x, a ) => right( Ex( x, -a ) )
        case Ex( x, a )  => right( All( x, -a ) )
        case And( a, b ) =>
          left( a ); left( b )
        case Neg( a ) => right( a )
        case Top()    =>
        case Bottom() => trivial = true
        case _        => ant += f
      }

      def right( f: HOLFormula ): Unit = f match {
        case All( x, a ) =>
          val eigen = rename( x, freeVars.toList )
          freeVars += eigen
          right( Substitution( x -> eigen )( a ) )
        case Ex( x, a ) =>
          val fvs = freeVariables( f ).toSeq
          val skolem = Const( skolemSyms.next, FunctionType( x.exptype, fvs map { _.exptype } ) )
          right( Substitution( x -> skolem( fvs: _* ) )( a ) )
        case Or( a, b ) =>
          right( a ); right( b )
        case Imp( a, b ) =>
          left( a ); right( b )
        case Neg( a ) => left( a )
        case Bottom() =>
        case Top()    => trivial = true
        case _        => suc += f
      }

      seq.antecedent foreach left
      seq.succedent foreach right

      if ( !trivial && ant.intersect( suc ).isEmpty )
        split( Sequent( ant.toSeq, suc.toSeq ) )
    }

    // Then we simplify the connectives which correspond to nested conjunctions, e.g. (:- a&b) turns into (:- a) and (:- b).
    // In order to combat exponential blow-up, we do something special if there are two or more such elements:
    // we introduce a definition for the first one.
    def split( seq: HOLSequent ): Unit = {
      seq.zipWithIndex.elements collect {
        case ( And( a, b ), i: Suc ) => i
        case ( Or( a, b ), i: Ant )  => i
        case ( Imp( a, b ), i: Ant ) => i
      } match {
        case splits if splits.size > 1 =>
          abbrev( seq, splits.head )
        case Seq( i ) => splitAt( seq, i )
        case Seq()    => cnf += seq.map { _.asInstanceOf[HOLAtom] }
      }
    }

    def splitAt( seq: HOLSequent, i: SequentIndex ): Unit =
      ( seq( i ), i ) match {
        case ( And( a, b ), i: Suc ) =>
          splitAt( seq.updated( i, a ), i ); splitAt( seq.updated( i, b ), i )
        case ( Or( a, b ), i: Ant ) =>
          splitAt( seq.updated( i, a ), i ); splitAt( seq.updated( i, b ), i )
        case ( Imp( a, b ), i: Ant ) =>
          splitAt( seq.delete( i ) :+ a, Suc( seq.succedent.size ) ); splitAt( seq.updated( i, b ), i )
        case _ => expand( seq )
      }

    // Here, we replace the formula at index i with a definition, and continue with
    // both the abbreviated sequent, and (the necessary part of) the definition.
    def abbrev( seq: HOLSequent, i: SequentIndex ): Unit = {
      val f = seq( i )
      val fvs = freeVariables( f ).toSeq
      val const = defs.getOrElseUpdate(
        Abs( fvs, f ),
        HOLAtomConst( abbrevSyms.next(), fvs map { _.exptype }: _* )
      )
      val repl = const( fvs: _* )
      if ( i isAnt ) {
        expand( Sequent( Seq( f ), Seq( repl ) ) )
      } else {
        expand( Sequent( Seq( repl ), Seq( f ) ) )
      }
      split( seq.updated( i, repl ) )
    }

    ( cnf.toSet, defs.map( _.swap ).toMap )
  }

}
