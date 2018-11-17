package gapt.proofs.expansion

import gapt.expr._
import gapt.utils.generatedUpperSetInPO

import scala.collection.mutable

object eliminateCutsET {
  def apply( expansionProof: ExpansionProof, maxCutInsts: Int = Integer.MAX_VALUE ): ExpansionProof = {
    if ( expansionProof.cuts.isEmpty ) return ExpansionProof( expansionProof.nonCutPart )

    def simplifiedEPWC( cuts: Seq[ETCut.Cut], es: ExpansionSequent ) =
      ExpansionProof( eliminateMerges( simpPropCuts( cuts ) +: es ) )

    var epwc = simplifiedEPWC( expansionProof.cuts, expansionProof.nonCutPart )

    while ( true ) {
      val cuts = epwc.cuts
      cuts.sortBy( numCutInsts ).view.flatMap {
        case cut if numCutInsts( cut ) > maxCutInsts => None
        case cut @ ETCut.Cut( cut1, cut2 ) =>
          singleStep( cut1, cut2, cuts.filterNot( _ == cut ), epwc.nonCutPart,
            freeVariablesET.includingEigenVariables( epwc ),
            epwc.dependencyRelation )
      }.headOption match {
        case Some( ( newCuts, newES ) ) =>
          epwc = simplifiedEPWC( newCuts, newES )
        case None =>
          return if ( epwc.cuts.isEmpty ) ExpansionProof( epwc.nonCutPart ) else epwc
      }
    }
    throw new IllegalStateException
  }

  private def numCutInsts: ETCut.Cut => Int = {
    case ETCut.Cut( ETWeakQuantifierBlock( _, n, insts ), _ ) if n > 0 => insts.size
    case ETCut.Cut( _, ETWeakQuantifierBlock( _, n, insts ) ) if n > 0 => insts.size
    case _ => 0
  }

  private def simpPropCuts( cuts: Seq[ETCut.Cut] ): ExpansionTree = {
    val newCuts = mutable.Buffer[( ExpansionTree, ExpansionTree )]()
    def simp( left: ExpansionTree, right: ExpansionTree ): Unit = ( left, right ) match {
      case ( ETWeakening( _, _ ), _ )         =>
      case ( _, ETWeakening( _, _ ) )         =>
      case ( ETAtom( _, _ ), ETAtom( _, _ ) ) =>
      case ( ETTop( _ ), ETTop( _ ) )         =>
      case ( ETBottom( _ ), ETBottom( _ ) )   =>
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
      case _ => newCuts += ( ( left, right ) )
    }
    for ( ETCut.Cut( l, r ) <- cuts ) simp( l, r )
    ETCut( newCuts.groupBy( _._1.shallow ).values.map( cs =>
      ETCut.Cut( ETMerge( cs.map( _._1 ) ), ETMerge( cs.map( _._2 ) ) ) ) )
  }

  private def singleStep( cut1: ExpansionTree, cut2: ExpansionTree, rest: Seq[ETCut.Cut],
                          expansionSequent: ExpansionSequent, freeVars: Set[Var],
                          dependencyRelation: Set[( Var, Var )] ): Option[( Seq[ETCut.Cut], ExpansionSequent )] = {
    // This uses a slightly more optimized reduction step than described in the unpublished
    // paper "Expansion Trees with Cut".
    //
    // Say we have an expansion proof with cut ∀x P(x) → ∀x P(x), Γ :- Δ where the cut expands
    // to P(eigenvar) → P(inst_1) ∧ ‥ ∧ P(inst_n), and the deep sequent is T-valid (for a given theory T).
    // Let η_i be renamings of the eigenvariables above the eigenvariables in P(eigenvar) and all P(inst_i)
    // in the dependency order to fresh variables, and σ_i = η_i [eigenvar \ inst_i].
    // By applying an invertible rule to the cut-implication we see that the deep formulas of Γ :- Δ, P(eigenvar)
    // and P(inst_1), ‥, P(inst_n), Γ :- Δ are T-valid.
    //
    // If there exists an σ_k such that the shallow formulas of P(eigenvar) and P(inst_i)σ_k are equal for all i,
    // then we can apply all σ_i to the first sequent, and apply σ_k to the second sequent and conclude that
    // P(eigenvar)σ_1 → P(inst_1)σ_k, P(eigenvar)σ_2 → P(inst_2)σ_k, ‥, Γσ_1, Γσ_2, ‥ :- Δσ_1, Δσ_2, ‥
    // is T-valid.
    //
    // In the general case we can still apply all σ_i to the first sequent, but we cannot apply
    // σ_1 to the second sequent--but it's not necessary to apply a substitution there, it just
    // keeps the quantifier complexity low.
    // In this case the following sequent becomes T-valid by the same argument:
    // P(eigenvar)σ_1 → P(inst_1), P(eigenvar)σ_2 → P(inst_2), ‥, Γ, Γσ_1, Γσ_2, ‥ :- Δ, Δσ_1, Δσ_2, ‥
    //
    // The resulting expansion proof will have duplicate eigenvariables since we did not rename the ones
    // that are not above the eigenvariables in the cut.  But these will get merged as they do not dominate
    // weak quantifier instances that have been changed through the substitution.
    def quantifiedCut(
      instances:      Map[Seq[Expr], ExpansionTree],
      eigenVariables: Seq[Var], child: ExpansionTree ): ( Seq[ETCut.Cut], ExpansionSequent ) = {
      if ( instances isEmpty ) return ( rest, expansionSequent )

      val eigenVarsToRename =
        generatedUpperSetInPO( child.term.eigenVariables ++ eigenVariables, dependencyRelation ) -- eigenVariables
      val nameGen = rename.awayFrom( freeVars )
      val renamings = for ( _ <- 0 until instances.size )
        yield Substitution( eigenVarsToRename map { ev => ev -> nameGen.fresh( ev ) } )
      val substs =
        for ( ( renaming, ( term, instance ) ) <- renamings zip instances )
          yield Substitution( eigenVariables zip term ) compose renaming

      val matchingSubstOption = substs.find( s =>
        ( substs zip instances.values ).forall( inst =>
          s( inst._2.shallow ) == inst._1( child.shallow ) ) )
      val matchingSubst = matchingSubstOption getOrElse Substitution()
      val needExtraCopy = matchingSubstOption.isEmpty

      val newCuts = for ( ( subst, ( term, instance ) ) <- substs zip instances ) yield {
        if ( instance.polarity.positive ) ETCut.Cut( matchingSubst( instance ), subst( child ) )
        else ETCut.Cut( subst( child ), matchingSubst( instance ) )
      }

      val substs_ = if ( needExtraCopy ) substs :+ Substitution() else substs
      ( newCuts ++ ( for ( c <- rest; s <- substs_ ) yield s( c ) ),
        for ( tree <- expansionSequent ) yield ETMerge( substs_.map( _( tree ) ) ) )
    }

    Some( ( cut1, cut2 ) ) collect {
      case ( ETWeakQuantifierBlock( _, n, instances ),
        ETStrongQuantifierBlock( _, eigenVariables, child ) ) if n > 0 && eigenVariables.size == n =>
        quantifiedCut( instances, eigenVariables, child )
      case ( ETStrongQuantifierBlock( _, eigenVariables, child ),
        ETWeakQuantifierBlock( _, n, instances ) ) if n > 0 && eigenVariables.size == n =>
        quantifiedCut( instances, eigenVariables, child )
    }

  }
}
