package gapt.logic.hol

import gapt.expr.Abs
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.formula
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.expr.formula.hol.HOLAtomConst
import gapt.expr.subst.Substitution
import gapt.expr.ty.FunctionType
import gapt.expr.util.constants
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.proofs.Ant
import gapt.proofs.FOLClause
import gapt.proofs.FOLSequent
import gapt.proofs.HOLClause
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.Suc
import gapt.utils.NameGenerator

import scala.collection.mutable

case class fastStructuralCNF( propositional: Boolean = true, bidirectionalDefs: Boolean = false ) {

  def apply( formula: Formula ): ( Set[HOLClause], Map[HOLAtomConst, Expr] ) =
    apply( formula +: Sequent() )

  def apply( endSequent: FOLSequent )( implicit dummyImplicit: DummyImplicit ): ( Set[FOLClause], Map[HOLAtomConst, Expr] ) = {
    val ( cnf, definitions ) = apply( endSequent.asInstanceOf[HOLSequent] )
    ( cnf.map { _.asInstanceOf[FOLClause] }, definitions )
  }

  def apply( endSequent: HOLSequent ): ( Set[HOLClause], Map[HOLAtomConst, Expr] ) = {
    if ( !propositional )
      require( freeVariables( endSequent ).isEmpty, "end-sequent has free variables" )

    val cnf = mutable.Set[HOLClause]()
    val defs = mutable.Map[Expr, HOLAtomConst]()
    val skConsts = mutable.Map[Expr, Const]()

    val nameGen = new NameGenerator( constants.nonLogical( endSequent ) map { _.name } )
    def mkSkolemSym() = nameGen.freshWithIndex( "s" )
    def mkAbbrevSym() = nameGen.freshWithIndex( "D" )

    def getSkolemInfo( f: Formula, x: Var ): ( Expr, Expr ) = {
      val fvs = freeVariables( f ).toSeq
      val skolemizedFormula = Abs( fvs, f )
      val skolemConst = skConsts.getOrElseUpdate(
        skolemizedFormula,
        Const( mkSkolemSym(), FunctionType( x.ty, fvs map { _.ty } ) ) )
      ( skolemConst( fvs: _* ), skolemizedFormula )
    }

    // We do a clausification similar to forward proof search in Ral.
    // (But we handle Skolemization more as an afterthought here.)

    // Since we the CNF of the negation of endSequent, we start with the following set of sequents:
    // For every formula in the antecedent:  :- formula
    // For every formula in the succedent:   formula -:
    for ( ( initial, index ) <- endSequent.map( Sequent() :+ _, _ +: Sequent() ).zipWithIndex )
      expand( initial )
    // If we interpret the sequents in this set as a disjunction, their conjunction is equivalent to the original formula.

    // In each step we simplify the sequents in this set and make them more like clauses.

    // First we expand the connectives which correspond to nested disjunctions, e.g. (:- a|b) turns into (:- a, b).
    def expand( seq: HOLSequent ): Unit = {
      val ant = mutable.Set[Formula]()
      val suc = mutable.Set[Formula]()
      lazy val freeVars = mutable.Set[Var]( freeVariables( seq ).toSeq: _* )
      var trivial = false

      def left( f: Formula ): Unit = f match {
        case Ex( x, a ) if !propositional =>
          val eigen = rename( x, freeVars )
          freeVars += eigen
          left( Substitution( x -> eigen )( a ) )
        case All( x, a ) if !propositional =>
          val ( skolemTerm, skolemizedFormula ) = getSkolemInfo( f, x )
          left( Substitution( x -> skolemTerm )( a ) )
        case And( a, b ) =>
          left( a ); left( b )
        case Neg( a ) => right( a )
        case Top() =>
        case Bottom() => trivial = true
        case Or( a, Bottom() ) => left( a )
        case Or( Bottom(), b ) => left( b )
        case Imp( a, Bottom() ) => right( a )
        case Imp( Top(), b ) => left( b )
        case Or( Top(), _ ) | Or( _, Top() ) | Imp( Bottom(), _ ) | Imp( _, Top() ) =>
        case _ => ant += f
      }

      def right( f: Formula ): Unit = f match {
        case All( x, a ) if !propositional =>
          val eigen = rename( x, freeVars )
          freeVars += eigen
          right( Substitution( x -> eigen )( a ) )
        case Ex( x, a ) if !propositional =>
          val ( skolemTerm, skolemizedFormula ) = getSkolemInfo( f, x )
          right( Substitution( x -> skolemTerm )( a ) )
        case Or( a, b ) =>
          right( a ); right( b )
        case Imp( a, b ) =>
          left( a ); right( b )
        case Neg( a )                                => left( a )
        case Bottom()                                =>
        case Top()                                   => trivial = true
        case And( a, Top() )                         => right( a )
        case And( Top(), b )                         => right( b )
        case And( Bottom(), _ ) | And( _, Bottom() ) =>
        case _                                       => suc += f
      }

      seq.map( left, right )

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
        case splits if splits.size > 1 || ( splits.size == 1 && seq.size > 3 ) =>
          abbrev( seq, splits.head )
        case Seq( i ) => splitAt( seq, i )
        case Seq()    => cnf += seq.map { _.asInstanceOf[Atom] }
      }
    }

    def splitAt( seq: HOLSequent, i: SequentIndex ): Unit =
      ( seq( i ), i ) match {
        case ( And( a, b ), i: Suc ) =>
          splitAt( seq.updated( i, a ), i )
          splitAt( seq.updated( i, b ), i )
        case ( Or( a, b ), i: Ant ) =>
          splitAt( seq.updated( i, a ), i )
          splitAt( seq.updated( i, b ), i )
        case ( Imp( a, b ), i: Ant ) =>
          val aIdx = Suc( seq.succedent.size )
          splitAt( seq.delete( i ) :+ a, aIdx )
          splitAt( seq.updated( i, b ), i )
        case _ => expand( seq )
      }

    // Here, we replace the formula at index i with a definition, and continue with
    // both the abbreviated sequent, and (the necessary part of) the definition.
    def abbrev( seq: HOLSequent, i: SequentIndex ): Unit = {
      val f = seq( i )
      val fvs = if ( propositional ) Seq() else freeVariables( f ).toSeq
      val alreadyDefined = defs isDefinedAt Abs( fvs, f )
      val const = defs.getOrElseUpdate(
        Abs( fvs, f ),
        formula.hol.HOLAtomConst( mkAbbrevSym(), fvs map { _.ty }: _* ) )
      val repl = const( fvs: _* )
      if ( !alreadyDefined ) {
        if ( i.isAnt || bidirectionalDefs ) expand( Sequent( Seq( f ), Seq( repl ) ) )
        if ( i.isSuc || bidirectionalDefs ) expand( Sequent( Seq( repl ), Seq( f ) ) )
      }
      split( seq.updated( i, repl ) )
    }

    ( cnf.toSet, defs.map( _.swap ).toMap )
  }

}
