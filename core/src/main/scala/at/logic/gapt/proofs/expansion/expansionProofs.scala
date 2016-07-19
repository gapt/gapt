package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.expr.hol.{ HOLPosition, SkolemFunctions }
import at.logic.gapt.formats.babel.BabelSignature

import scala.collection.mutable

object linearizeStrictPartialOrder {
  def apply[T]( set: Iterable[T], relation: Iterable[( T, T )] ): Either[Seq[T], Seq[T]] =
    build( set.toSet, relation.toSet, Seq() )

  private def build[T]( set: Set[T], relation: Set[( T, T )], prefix: Seq[T] ): Either[Seq[T], Seq[T]] =
    if ( set isEmpty ) {
      Right( prefix )
    } else {
      set find { n => relation forall { _._2 != n } } match {
        case Some( next ) =>
          build( set - next, relation filterNot { _._1 == next }, prefix :+ next )
        case None =>
          val start = set.head
          val cycle = start +: walk( start, relation ).drop( 1 ).takeWhile( _ != start ) :+ start
          Left( cycle.toList )
      }
    }

  private def walk[T]( start: T, relation: Set[( T, T )] ): Stream[T] = {
    val Some( ( _, next ) ) = relation find { _._1 == start }
    next #:: walk( next, relation )
  }
}

case class ExpansionProof( expansionSequent: Sequent[ExpansionTree] ) {
  for ( ( tree, index ) <- expansionSequent.zipWithIndex ) require( tree.polarity == index.isSuc )

  {
    val evs = mutable.Set[Var]()
    val fvs = freeVariables( shallow )
    for {
      tree <- expansionSequent
      ETStrongQuantifier( _, ev, _ ) <- tree.treeLike.postOrder
    } {
      require( !evs.contains( ev ), s"duplicate eigenvariable $ev" )
      require( !fvs.contains( ev ), s"eigenvariable $ev is free in shallow sequent" )
      evs += ev
    }
  }

  def shallow = expansionSequent.shallow
  def deep = expansionSequent.deep

  val subProofs = expansionSequent.elements flatMap { _.subProofs } toSet
  val eigenVariables = for ( ETStrongQuantifier( _, ev, _ ) <- subProofs ) yield ev

  val skolemFunctions = SkolemFunctions(
    subProofs collect {
      case sk: ETSkolemQuantifier => sk.skolemConst -> sk.skolemDef
    }
  )

  val atomDefs =
    subProofs collect {
      case d: ETDefinedAtom => d.definitionConst -> d.definition
      case d: ETDefinition  => d.pred -> d.definedExpr
    } groupBy { _._1 } map {
      case ( c, ds ) =>
        require(
          ds.size == 1,
          s"Inconsistent definition $c:\n${ds.map { _._2 }.mkString( "\n" )}"
        )
        c -> ds.head._2
    }

  /**
   * Contains the pair (x, y) iff x occurs as a selected term in any sort of quantifier node
   * below the strong quantifier node introducing y.
   */
  val dependencyRelation = for {
    ETQuantifier( _, instances ) <- subProofs
    ( term, child ) <- instances
    ETStrongQuantifier( _, ev, _ ) <- child.subProofs
    evInTerm <- eigenVariables intersect freeVariables( term )
  } yield evInTerm -> ev
  val Right( linearizedDependencyRelation ) = linearizeStrictPartialOrder( eigenVariables, dependencyRelation )

  override def toString = toSigRelativeString
  def toSigRelativeString( implicit sig: BabelSignature ) =
    expansionSequent.map( _.toSigRelativeString ).toString
}

case class ExpansionProofWithCut( expansionWithCutAxiom: ExpansionProof ) {
  import ExpansionProofWithCut._
  def expansionSequent = expansionWithCutAxiom.expansionSequent filter { _.shallow != cutAxiom }
  def eigenVariables = expansionWithCutAxiom.eigenVariables
  def deep = expansionWithCutAxiom.deep
  def shallow = expansionSequent map { _.shallow }
  def subProofs = expansionWithCutAxiom.subProofs
  def skolemFunctions = expansionWithCutAxiom.skolemFunctions

  val cuts = for {
    cutAxiomExpansion <- expansionWithCutAxiom.expansionSequent.antecedent
    if cutAxiomExpansion.shallow == cutAxiom
    cut <- cutAxiomExpansion( HOLPosition( 1 ) )
    cut1 <- cut( HOLPosition( 1 ) )
    cut2 <- cut( HOLPosition( 2 ) )
  } yield ETImp( cut1, cut2 )

  def toExpansionProof = {
    require( cuts.isEmpty )
    ExpansionProof( expansionSequent )
  }

  override def toString = expansionWithCutAxiom.toString
}
object ExpansionProofWithCut {
  val cutAxiom = hof"∀X (X ⊃ X)"
  def apply( expansionSequentWithCutAxiom: ExpansionSequent ): ExpansionProofWithCut =
    ExpansionProofWithCut( ExpansionProof( expansionSequentWithCutAxiom ) )
  def apply( cuts: Seq[ETImp], expansionSequent: Sequent[ExpansionTree] ): ExpansionProofWithCut =
    apply( mkCutAxiom( cuts ) +: expansionSequent )
  def mkCutAxiom( cuts: Seq[ETImp] ): ExpansionTree =
    ETWeakQuantifier.withMerge(
      ExpansionProofWithCut.cutAxiom,
      for ( cut @ ETImp( cut1, cut2 ) <- cuts ) yield cut1.shallow -> cut
    )
}

object freeVariablesET {
  def apply( expansionProof: ExpansionProof ): Set[Var] =
    freeVariables( expansionProof.deep ) diff expansionProof.eigenVariables
  def apply( expansionProofWithCut: ExpansionProofWithCut ): Set[Var] =
    apply( expansionProofWithCut.expansionWithCutAxiom )
}
private[expansion] object expansionProofSubstitution extends ClosedUnderSub[ExpansionProof] {
  override def applySubstitution( subst: Substitution, expansionProof: ExpansionProof ): ExpansionProof =
    if ( subst.domain intersect expansionProof.eigenVariables nonEmpty ) {
      applySubstitution( Substitution( subst.map -- expansionProof.eigenVariables ), expansionProof )
    } else {
      val substWithRenaming = subst compose Substitution(
        rename( expansionProof.eigenVariables intersect subst.range, expansionProof.eigenVariables union subst.range )
      )
      ExpansionProof( substWithRenaming( expansionProof.expansionSequent ) )
    }
}
private[expansion] object expansionProofWithCutSubstitution extends ClosedUnderSub[ExpansionProofWithCut] {
  override def applySubstitution( subst: Substitution, expansionProofWithCut: ExpansionProofWithCut ): ExpansionProofWithCut =
    ExpansionProofWithCut( subst( expansionProofWithCut.expansionWithCutAxiom ) )
}

object eliminateMerges {
  def apply( expansionProof: ExpansionProofWithCut ): ExpansionProofWithCut =
    ExpansionProofWithCut( elim( expansionProof.expansionWithCutAxiom.expansionSequent ) )

  def apply( expansionProof: ExpansionProof ): ExpansionProof =
    ExpansionProof( elim( expansionProof.expansionSequent ) )

  def unsafe( expansionSequent: ExpansionSequent ): ExpansionSequent =
    elim( expansionSequent )

  private def elim( expansionSequent: Sequent[ExpansionTree] ): ExpansionSequent = {
    var needToMergeAgain = false
    var eigenVarSubst = Substitution()

    def merge( tree: ExpansionTree ): ExpansionTree = tree match {
      case ETMerge( t, s )              => merge2( t, s )
      case _: ETDefinedAtom | _: ETAtom => tree
      case tree: ETDefinition           => tree.copy( child = merge( tree.child ) )
      case ETWeakening( formula, pol )  => ETWeakening( formula, pol )
      case _: ETTop | _: ETBottom       => tree
      case ETNeg( t )                   => ETNeg( merge( t ) )
      case ETAnd( t, s )                => ETAnd( merge( t ), merge( s ) )
      case ETOr( t, s )                 => ETOr( merge( t ), merge( s ) )
      case ETImp( t, s )                => ETImp( merge( t ), merge( s ) )
      case ETWeakQuantifier( shallow, inst ) =>
        ETWeakQuantifier(
          shallow,
          for ( ( selectedTerm, child ) <- inst )
            yield selectedTerm -> merge( child )
        )
      case tree: ETStrongQuantifier => tree.copy( child = merge( tree.child ) )
      case tree: ETSkolemQuantifier => tree.copy( child = merge( tree.child ) )
    }
    def merge2( tree1: ExpansionTree, tree2: ExpansionTree ): ExpansionTree = ( tree1, tree2 ) match {
      case ( _: ETWeakening, s ) => merge( s )
      case ( t, _: ETWeakening ) => merge( t )
      case ( ETMerge( t1, t2 ), s ) =>
        merge2( t1, t2 ) match {
          case t: ETMerge => ETMerge( t, merge( s ) )
          case t          => merge2( t, s )
        }
      case ( t, s: ETMerge ) => merge2( s, t )
      case ( t: ETAtom, _: ETAtom ) => t
      case ( t @ ETDefinedAtom( a1, _, d1 ), ETDefinedAtom( a2, _, d2 ) ) if d1 == d2 => t
      case ( ETDefinition( shallow, def1, t1 ), ETDefinition( _, def2, t2 ) ) if def1 == def2 =>
        ETDefinition( shallow, def1, merge2( t1, t2 ) )
      case ( t: ETTop, _: ETTop )               => t
      case ( t: ETBottom, _: ETBottom )         => t
      case ( ETNeg( t ), ETNeg( s ) )           => ETNeg( merge2( t, s ) )
      case ( ETAnd( t1, t2 ), ETAnd( s1, s2 ) ) => ETAnd( merge2( t1, s1 ), merge2( t2, s2 ) )
      case ( ETOr( t1, t2 ), ETOr( s1, s2 ) )   => ETOr( merge2( t1, s1 ), merge2( t2, s2 ) )
      case ( ETImp( t1, t2 ), ETImp( s1, s2 ) ) => ETImp( merge2( t1, s1 ), merge2( t2, s2 ) )
      case ( ETWeakQuantifier( shallow, inst1 ), ETWeakQuantifier( _, inst2 ) ) =>
        ETWeakQuantifier(
          shallow,
          ( for ( selected <- inst1.keySet union inst2.keySet ) yield selected ->
          ( if ( !inst2.contains( selected ) ) merge( inst1( selected ) )
          else if ( !inst1.contains( selected ) ) merge( inst2( selected ) )
          else merge2( inst1( selected ), inst2( selected ) ) ) ).toMap
        )
      case ( tree1 @ ETStrongQuantifier( shallow, v1, t1 ), tree2 @ ETStrongQuantifier( _, v2, t2 ) ) =>
        if ( v1 == v2 ) {
          ETStrongQuantifier( shallow, v1, merge2( t1, t2 ) )
        } else {
          eigenVarSubst = eigenVarSubst compose Substitution( v2 -> v1 )
          needToMergeAgain = true

          ETMerge( merge( tree1 ), merge( tree2 ) )
        }
      case ( ETStrongQuantifier( _, v1, t1 ), ETSkolemQuantifier( shallow, st2, sf2, t2 ) ) =>
        needToMergeAgain = true
        if ( !eigenVarSubst.map.isDefinedAt( v1 ) )
          eigenVarSubst = eigenVarSubst compose Substitution( v1 -> st2 )

        ETMerge( merge( tree1 ), merge( tree2 ) )
      case ( t: ETSkolemQuantifier, s: ETStrongQuantifier ) => merge2( s, t )
      case ( ETSkolemQuantifier( shallow, st1, sf1, t1 ), ETSkolemQuantifier( _, st2, sf2, t2 ) ) if st1 == st2 =>
        ETSkolemQuantifier( shallow, st1, sf1, merge2( t1, t2 ) )
      case ( t, s ) => ETMerge( merge( t ), merge( s ) )
    }

    val mergedSequent = expansionSequent map merge

    if ( !needToMergeAgain ) {
      mergedSequent
    } else {
      elim( mergedSequent map { eigenVarSubst( _ ) } )
    }
  }
}

object generatedUpperSetInPO {
  def apply[T]( gen: Iterable[T], rel: Iterable[( T, T )] ): Set[T] = {
    val upper = mutable.Set[T]()
    def walk( el: T ): Unit =
      if ( !upper.contains( el ) ) {
        upper += el
        for ( ( `el`, next ) <- rel ) walk( next )
      }
    gen foreach walk
    upper.toSet
  }
}

object eliminateCutsET {
  def apply( expansionProof: ExpansionProofWithCut ): ExpansionProof = {
    if ( expansionProof.cuts.isEmpty ) return expansionProof.toExpansionProof

    def simplifiedEPWC( cuts: Seq[ETImp], es: ExpansionSequent ) =
      ExpansionProofWithCut( eliminateMerges.unsafe( ExpansionProofWithCut.mkCutAxiom( simpPropCuts( cuts ) ) +: es ) )

    var epwc = simplifiedEPWC( expansionProof.cuts, expansionProof.expansionSequent )

    while ( true )
      epwc.cuts.view.flatMap {
        case cut @ ETImp( cut1, cut2 ) =>
          singleStep( cut1, cut2, epwc.cuts.filterNot( _ == cut ), epwc.expansionSequent,
            epwc.eigenVariables union freeVariables( epwc.deep ),
            epwc.expansionWithCutAxiom.dependencyRelation )
      }.headOption match {
        case Some( ( newCuts, newES ) ) =>
          epwc = simplifiedEPWC( newCuts, newES )
        case None =>
          return {
            if ( epwc.cuts.isEmpty ) epwc.toExpansionProof
            else epwc.expansionWithCutAxiom
          }
      }

    throw new IllegalStateException
  }

  private def simpPropCuts( cuts: Seq[ETImp] ): Seq[ETImp] = {
    val newCuts = Seq.newBuilder[ETImp]
    def simp( left: ExpansionTree, right: ExpansionTree ): Unit = ( left, right ) match {
      case ( _: ETWeakening, _ )        =>
      case ( _, _: ETWeakening )        =>
      case ( _: ETAtom, _: ETAtom )     =>
      case ( _: ETTop, _: ETTop )       =>
      case ( _: ETBottom, _: ETBottom ) =>
      case ( ETMerge( l1, l2 ), r ) =>
        simp( l1, r ); simp( l2, r )
      case ( l, ETMerge( r1, r2 ) ) =>
        simp( l, r1 ); simp( l, r2 )
      case ( ETNeg( t1 ), ETNeg( t2 ) ) => simp( t2, t1 )
      case ( ETAnd( t1, s1 ), ETAnd( t2, s2 ) ) =>
        simp( t1, t2 ); simp( s1, s2 )
      case ( ETOr( t1, s1 ), ETOr( t2, s2 ) ) =>
        simp( t1, t2 ); simp( s1, s2 )
      case ( ETImp( t1, s1 ), ETImp( t2, s2 ) ) =>
        simp( t2, t1 ); simp( s1, s2 )
      case _ => newCuts += ETImp( left, right )
    }
    for ( ETImp( l, r ) <- cuts ) simp( l, r )
    newCuts.result()
  }

  private def singleStep( cut1: ExpansionTree, cut2: ExpansionTree, rest: Seq[ETImp],
                          expansionSequent: Sequent[ExpansionTree], freeVars: Set[Var],
                          dependencyRelation: Set[( Var, Var )] ): Option[( Seq[ETImp], ExpansionSequent )] = {
    // This uses a slightly more optimized reduction step than described in the unpublished
    // paper "Expansion Trees with Cut".
    //
    // Say we have an expansion proof with cut ∀x P(x) ⊃ ∀x P(x), Γ :- Δ where the cut expands
    // to P(eigenvar) ⊃ P(inst_1) ∧ ‥ ∧ P(inst_n), and the deep sequent is T-valid (for a given theory T).
    // Let η_i be renamings of the eigenvariables above the eigenvariables in P(eigenvar) and all P(inst_i)
    // in the dependency order to fresh variables, and σ_i = η_i [eigenvar \ inst_i].
    // By applying an invertible rule to the cut-implication we see that the deep formulas of Γ :- Δ, P(eigenvar)
    // and P(inst_1), ‥, P(inst_n), Γ :- Δ are T-valid.
    //
    // If there exists an σ_k such that the shallow formulas of P(eigenvar) and P(inst_i)σ_k are equal for all i,
    // then we can apply all σ_i to the first sequent, and apply σ_k to the second sequent and conclude that
    // P(eigenvar)σ_1 ⊃ P(inst_1)σ_k, P(eigenvar)σ_2 ⊃ P(inst_2)σ_k, ‥, Γσ_1, Γσ_2, ‥ :- Δσ_1, Δσ_2, ‥
    // is T-valid.
    //
    // In the general case we can still apply all σ_i to the first sequent, but we cannot apply
    // σ_1 to the second sequent--but it's not necessary to apply a substitution there, it just
    // keeps the quantifier complexity low.
    // In this case the following sequent becomes T-valid by the same argument:
    // P(eigenvar)σ_1 ⊃ P(inst_1), P(eigenvar)σ_2 ⊃ P(inst_2), ‥, Γ, Γσ_1, Γσ_2, ‥ :- Δ, Δσ_1, Δσ_2, ‥
    //
    // The resulting expansion proof will have duplicate eigenvariables since we did not rename the ones
    // that are not above the eigenvariables in the cut.  But these will get merged as they do not dominate
    // weak quantifier instances that have been changed through the substitution.
    def quantifiedCut(
      instances:     Map[LambdaExpression, ExpansionTree],
      eigenVariable: Var, child: ExpansionTree
    ): ( Seq[ETImp], ExpansionSequent ) = {
      if ( instances isEmpty ) return ( rest, expansionSequent )

      val eigenVarsToRename = generatedUpperSetInPO( eigenVariablesET( child ) + eigenVariable, dependencyRelation ) - eigenVariable
      val nameGen = rename.awayFrom( freeVars )
      val renamings = for ( _ <- 0 until instances.size )
        yield Substitution( eigenVarsToRename map { ev => ev -> nameGen.fresh( ev ) } )
      val substs =
        for ( ( renaming, ( term, instance ) ) <- renamings zip instances )
          yield Substitution( eigenVariable -> term ) compose renaming

      val matchingSubstOption = substs find { s => ( substs zip instances.values ).forall { inst => s( inst._2.shallow ) == inst._1( child.shallow ) } }
      val matchingSubst = matchingSubstOption getOrElse Substitution()
      val needExtraCopy = matchingSubstOption.isEmpty

      val newCuts = for ( ( subst, ( term, instance ) ) <- substs zip instances ) yield {
        if ( instance.polarity ) ETImp( matchingSubst( instance ), subst( child ) )
        else ETImp( subst( child ), matchingSubst( instance ) )
      }

      val substs_ = if ( needExtraCopy ) substs :+ Substitution() else substs
      (
        newCuts ++ ( for ( c <- rest; s <- substs_ ) yield s( c ).asInstanceOf[ETImp] ),
        for ( tree <- expansionSequent ) yield ETMerge( substs_.map { _( tree ) } )
      )
    }

    Some( ( cut1, cut2 ) ) collect {
      case ( ETWeakQuantifier( _, instances ), ETStrongQuantifier( _, eigenVariable, child ) ) =>
        quantifiedCut( instances, eigenVariable, child )
      case ( ETStrongQuantifier( _, eigenVariable, child ), ETWeakQuantifier( _, instances ) ) =>
        quantifiedCut( instances, eigenVariable, child )
    }

  }
}

object eliminateDefsET {
  object DefinitionFormula {
    def unapply( f: HOLFormula ) = f match {
      case All.Block( vs, And( Imp( Apps( d1: HOLAtomConst, vs1 ), r1 ),
        Imp( r2, Apps( d2, vs2 ) ) ) ) if d1 == d2 && r1 == r2 && vs == vs1 && vs == vs2 =>
        Some( ( vs, d1, r2 ) )
      case _ => None
    }
  }
  val negReplPos = HOLPosition( 1, 2 )
  val posReplPos = HOLPosition( 2, 1 )

  def apply( ep: ExpansionProof, pureFolWithoutEq: Boolean, definitions: Set[Const] ): ExpansionProofWithCut =
    definitions.foldLeft( ExpansionProofWithCut( ep ) )( apply( _, _, pureFolWithoutEq ) )
  def apply( epwc: ExpansionProofWithCut, definitionConst: Const, pureFolWithoutEq: Boolean ): ExpansionProofWithCut = {
    val definition = epwc.expansionWithCutAxiom.atomDefs.getOrElse( definitionConst, return epwc )
    val Abs.Block( vs, definedFormula: HOLFormula ) = definition

    val ( defCuts, otherCuts ) = epwc.cuts.partition {
      case ETImp( d @ ETDefinedAtom( _, _, _ ), _ ) if d.definitionConst == definitionConst => true
      case ETImp( _, d @ ETDefinedAtom( _, _, _ ) ) if d.definitionConst == definitionConst => true
      case _ => false
    }

    val insts0 = defCuts map {
      case ETImp( ETDefinedAtom( Apps( _, as ), _, _ ), repl ) => as -> repl
      case ETImp( repl, ETDefinedAtom( Apps( _, as ), _, _ ) ) => as -> repl
    }
    var insts = insts0.groupBy( _._1 ).mapValues { repls =>
      val shallow = repls.head._2.shallow
      ETMerge( shallow, true, repls.map( _._2 ).filter( _.polarity ) ) ->
        ETMerge( shallow, false, repls.map( _._2 ).filter( !_.polarity ) )
    }

    val rest = ExpansionProofWithCut( otherCuts, epwc.expansionSequent ).expansionWithCutAxiom.expansionSequent
    val usesites = rest.elements.flatMap { _.subProofs }.
      collect { case ETDefinedAtom( Apps( `definitionConst`, args ), pol, _ ) => ( args, pol ) }.toSet
    insts = Map() ++
      usesites.map { _._1 }.map { as =>
        val ras = Substitution( vs zip as )( definedFormula )
        as -> ( ETWeakening( ras, true ), ETWeakening( ras, false ) )
      } ++
      insts

    if ( !pureFolWithoutEq ) {
      val newNegRepl = ETMerge( definedFormula, false, insts.values.map { _._2 }.map { generalizeET( _, definedFormula ) } )
      val newPosRepl = ETMerge( definedFormula, true, insts.values.map { _._1 }.map { generalizeET( _, definedFormula ) } )
      insts = insts map { case ( as, _ ) => as -> Substitution( vs zip as )( newPosRepl -> newNegRepl ) }
    }

    def replm: PartialFunction[LambdaExpression, LambdaExpression] = {
      case Apps( `definitionConst`, as ) => Substitution( vs zip as )( definedFormula )
    }
    def replf( f: HOLFormula ): HOLFormula = TermReplacement( f, replm )
    def repl( et: ExpansionTree ): ExpansionTree = et match {
      case ETMerge( a, b )                      => ETMerge( repl( a ), repl( b ) )
      case ETWeakening( sh, pol )               => ETWeakening( replf( sh ), pol )

      case ETTop( _ ) | ETBottom( _ )           => et
      case ETNeg( ch )                          => ETNeg( repl( ch ) )
      case ETAnd( l, r )                        => ETAnd( repl( l ), repl( r ) )
      case ETOr( l, r )                         => ETOr( repl( l ), repl( r ) )
      case ETImp( l, r )                        => ETImp( repl( l ), repl( r ) )
      case ETWeakQuantifier( sh, is )           => ETWeakQuantifier( replf( sh ), is mapValues repl )
      case ETStrongQuantifier( sh, ev, ch )     => ETStrongQuantifier( replf( sh ), ev, repl( ch ) )
      case ETSkolemQuantifier( sh, st, sd, ch ) => ETSkolemQuantifier( replf( sh ), st, sd, repl( ch ) )

      case ETDefinedAtom( Apps( `definitionConst`, as ), pol, _ ) =>
        if ( pol ) insts( as )._1 else insts( as )._2
      case ETDefinedAtom( _, _, _ )                          => et
      case ETAtom( Apps( f, _ ), _ ) if f != definitionConst => et
    }

    for ( ( _, ( pos, neg ) ) <- insts ) {
      require( !constants( pos.deep ).contains( definitionConst ) )
      require( !constants( neg.deep ).contains( definitionConst ) )
    }

    val newCuts = ETWeakQuantifier.withMerge(
      ExpansionProofWithCut.cutAxiom,
      insts.values.map { case ( pos, neg ) => pos.shallow -> ETImp( pos, neg ) }
    )

    val newES = ( newCuts +: rest.map { repl } ).
      groupBy { _.shallow }.map { _._2 }.map { ETMerge( _ ) }

    ExpansionProofWithCut( newES )
  }
}
