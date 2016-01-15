package at.logic.gapt.expr.hol

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansionTrees._

import scala.collection.mutable

object structuralCNF {

  sealed trait Justification
  case class ProjectionFromEndSequent( projection: ExpansionSequent, indexInES: SequentIndex ) extends Justification
  case class Definition( newAtom: HOLAtom, expansion: ExpansionTree ) extends Justification

  def apply( formula: HOLFormula, generateJustifications: Boolean, propositional: Boolean ): ( Set[HOLClause], Set[( HOLClause, Justification )], Map[HOLAtomConst, LambdaExpression] ) =
    apply( formula +: Sequent(), generateJustifications, propositional )

  def apply( endSequent: FOLSequent, generateJustifications: Boolean, propositional: Boolean )( implicit dummyImplicit: DummyImplicit ): ( Set[FOLClause], Set[( HOLClause, Justification )], Map[HOLAtomConst, LambdaExpression] ) = {
    val ( cnf, justifications, definitions ) = apply( endSequent.asInstanceOf[HOLSequent], generateJustifications, propositional )
    ( cnf.map { _.asInstanceOf[FOLClause] }, justifications, definitions )
  }

  def apply( endSequent: HOLSequent, generateJustifications: Boolean, propositional: Boolean ): ( Set[HOLClause], Set[( HOLClause, Justification )], Map[HOLAtomConst, LambdaExpression] ) = {
    if ( !propositional )
      require( freeVariables( endSequent ).isEmpty, "end-sequent has free variables" )

    val cnf = mutable.Set[HOLClause]()
    val justifications = mutable.Set[( HOLClause, Justification )]()
    val defs = mutable.Map[LambdaExpression, HOLAtomConst]()

    val symsInFormula = constants( endSequent ) map { _.name }
    val skolemSyms = new SkolemSymbolFactory().getSkolemSymbols.map { _.toString() }.filter { s => !symsInFormula.contains( s ) }.iterator
    val abbrevSyms = Stream.from( 0 ).map { i => s"D$i" }.filter { s => !symsInFormula.contains( s ) }.iterator

    // We do a clausification similar to forward proof search in Ral.
    // (But we handle Skolemization more as an afterthought here.)

    // Since we the CNF of the negation of endSequent, we start with the following set of sequents:
    // For every formula in the antecedent:  :- formula
    // For every formula in the succedent:   formula -:
    for ( ( initial, index ) <- endSequent.map( Sequent() :+ _, _ +: Sequent() ).zipWithIndex )
      expand( initial, es => ProjectionFromEndSequent( es.swapped, index ) )
    // If we interpret the sequents in this set as a disjunction, their conjunction is equivalent to the original formula.

    // In each step we simplify the sequents in this set and make them more like clauses.

    // First we expand the connectives which correspond to nested disjunctions, e.g. (:- a|b) turns into (:- a, b).
    def expand( seq: HOLSequent, backTrans: ExpansionSequent => Justification ): Unit = {
      val ant = mutable.Buffer[HOLFormula]()
      val suc = mutable.Buffer[HOLFormula]()
      lazy val freeVars = mutable.Set[Var]( freeVariables( seq ).toSeq: _* )
      var trivial = false

      def left( f: HOLFormula ): ( ExpansionSequent => ExpansionTree ) = f match {
        case Ex( x, a ) if !propositional =>
          val eigen = rename( x, freeVars.toList )
          freeVars += eigen
          val fa = left( Substitution( x -> eigen )( a ) )
          es => ETWeakQuantifier( f, fa( es ) -> eigen ).asInstanceOf[ExpansionTree]
        case All( x, a ) if !propositional =>
          val fvs = freeVariables( f ).toSeq
          val skolem = Const( skolemSyms.next, FunctionType( x.exptype, fvs map { _.exptype } ) )
          val fa = left( Substitution( x -> skolem( fvs: _* ) )( a ) )
          es => ETSkolemQuantifier( f, skolem, fa( es ) )
        case And( a, b ) =>
          val fa = left( a )
          val fb = left( b )
          es => ETAnd( fa( es ), fb( es ) )
        case Neg( a ) =>
          val fa = right( a )
          es => ETNeg( fa( es ) )
        case Top() => es => ETTop
        case Bottom() =>
          trivial = true
          es => ETBottom
        case Or( a, Bottom() ) =>
          val fa = left( a )
          es => ETOr( fa( es ), ETBottom )
        case Or( Bottom(), b ) =>
          val fb = left( b )
          es => ETOr( ETBottom, fb( es ) )
        case Imp( a, Bottom() ) =>
          val fa = right( a )
          es => ETImp( fa( es ), ETBottom )
        case Imp( Top(), b ) =>
          val fb = left( b )
          es => ETImp( ETTop, fb( es ) )
        case Or( Top(), _ ) | Or( _, Top() ) | Imp( Bottom(), _ ) | Imp( _, Top() ) =>
          es => ETWeakening( f )
        case _ =>
          if ( !ant.contains( f ) ) ant += f
          es => es( Ant( ant indexOf f ) )
      }

      def right( f: HOLFormula ): ( ExpansionSequent => ExpansionTree ) = f match {
        case All( x, a ) if !propositional =>
          val eigen = rename( x, freeVars.toList )
          freeVars += eigen
          val fa = right( Substitution( x -> eigen )( a ) )
          es => ETWeakQuantifier( f, fa( es ) -> eigen ).asInstanceOf[ExpansionTree]
        case Ex( x, a ) if !propositional =>
          val fvs = freeVariables( f ).toSeq
          val skolem = Const( skolemSyms.next, FunctionType( x.exptype, fvs map { _.exptype } ) )
          val fa = right( Substitution( x -> skolem( fvs: _* ) )( a ) )
          es => ETSkolemQuantifier( f, skolem, fa( es ) )
        case Or( a, b ) =>
          val fa = right( a )
          val fb = right( b )
          es => ETOr( fa( es ), fb( es ) )
        case Imp( a, b ) =>
          val fa = left( a )
          val fb = right( b )
          es => ETImp( fa( es ), fb( es ) )
        case Neg( a ) =>
          val fa = left( a )
          es => ETNeg( fa( es ) )
        case Bottom() => es => ETBottom
        case Top() =>
          trivial = true
          es => ETTop
        case And( a, Top() ) =>
          val fa = right( a )
          es => ETAnd( fa( es ), ETTop )
        case And( Top(), b ) =>
          val fb = right( b )
          es => ETAnd( ETTop, fb( es ) )
        case And( Bottom(), _ ) | And( _, Bottom() ) =>
          es => ETWeakening( f )
        case _ =>
          if ( !suc.contains( f ) ) suc += f
          es => es( Suc( suc indexOf f ) )
      }

      val expandBackTranfs = seq.map( left, right )

      if ( !trivial && ant.intersect( suc ).isEmpty )
        split(
          Sequent( ant.toSeq, suc.toSeq ),
          es => backTrans( expandBackTranfs.map( _( es ) ) )
        )
    }

    // Then we simplify the connectives which correspond to nested conjunctions, e.g. (:- a&b) turns into (:- a) and (:- b).
    // In order to combat exponential blow-up, we do something special if there are two or more such elements:
    // we introduce a definition for the first one.
    def split( seq: HOLSequent, backTrans: ExpansionSequent => Justification ): Unit = {
      seq.zipWithIndex.elements collect {
        case ( And( a, b ), i: Suc ) => i
        case ( Or( a, b ), i: Ant )  => i
        case ( Imp( a, b ), i: Ant ) => i
      } match {
        case splits if splits.size > 1 || ( splits.size == 1 && seq.size > 3 ) =>
          abbrev( seq, splits.head, backTrans )
        case Seq( i ) => splitAt( seq, i, backTrans )
        case Seq() =>
          val clause = seq.map { _.asInstanceOf[HOLAtom] }
          cnf += clause
          if ( generateJustifications )
            justifications += ( clause -> backTrans( clause map ETAtom ) )
      }
    }

    def splitAt( seq: HOLSequent, i: SequentIndex, backTrans: ExpansionSequent => Justification ): Unit =
      ( seq( i ), i ) match {
        case ( And( a, b ), i: Suc ) =>
          splitAt( seq.updated( i, a ), i, es => backTrans( es.updated( i, ETAnd( es( i ), ETWeakening( b ) ) ) ) )
          splitAt( seq.updated( i, b ), i, es => backTrans( es.updated( i, ETAnd( ETWeakening( a ), es( i ) ) ) ) )
        case ( Or( a, b ), i: Ant ) =>
          splitAt( seq.updated( i, a ), i, es => backTrans( es.updated( i, ETOr( es( i ), ETWeakening( b ) ) ) ) )
          splitAt( seq.updated( i, b ), i, es => backTrans( es.updated( i, ETOr( ETWeakening( a ), es( i ) ) ) ) )
        case ( Imp( a, b ), i: Ant ) =>
          val aIdx = Suc( seq.succedent.size )
          splitAt( seq.delete( i ) :+ a, aIdx, es => backTrans( es.delete( aIdx ).insertAt( i, ETImp( es( aIdx ), ETWeakening( b ) ) ) ) )
          splitAt( seq.updated( i, b ), i, es => backTrans( es.updated( i, ETImp( ETWeakening( a ), es( i ) ) ) ) )
        case _ => expand( seq, backTrans )
      }

    // Here, we replace the formula at index i with a definition, and continue with
    // both the abbreviated sequent, and (the necessary part of) the definition.
    def abbrev( seq: HOLSequent, i: SequentIndex, backTrans: ExpansionSequent => Justification ): Unit = {
      val f = seq( i )
      val fvs = if ( propositional ) Seq() else freeVariables( f ).toSeq
      val alreadyDefined = defs isDefinedAt Abs( fvs, f )
      val const = defs.getOrElseUpdate(
        Abs( fvs, f ),
        HOLAtomConst( abbrevSyms.next(), fvs map { _.exptype }: _* )
      )
      val repl = const( fvs: _* )
      if ( !alreadyDefined ) {
        if ( i isAnt ) {
          expand( Sequent( Seq( f ), Seq( repl ) ), es => Definition( repl, es( Ant( 0 ) ) ) )
        } else {
          expand( Sequent( Seq( repl ), Seq( f ) ), es => Definition( repl, es( Suc( 0 ) ) ) )
        }
      }
      split( seq.updated( i, repl ), es => backTrans( es.updated( i, ETAtom( repl ) ) ) )
    }

    ( cnf.toSet, justifications.toSet, defs.map( _.swap ).toMap )
  }

}
