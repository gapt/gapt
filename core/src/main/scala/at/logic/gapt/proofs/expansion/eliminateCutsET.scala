package at.logic.gapt.proofs.expansion
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.utils.generatedUpperSetInPO

object eliminateCutsET {
  def apply( expansionProof: ExpansionProof ): ExpansionProof = {
    def cuts( epwc: ExpansionProof ) = for {
      cutAxiomExpansion <- epwc.expansionSequent.antecedent
      if cutAxiomExpansion.shallow == ETCut.cutAxiom
      cut <- cutAxiomExpansion( HOLPosition( 1 ) )
      cut1 <- cut( HOLPosition( 1 ) )
      cut2 <- cut( HOLPosition( 2 ) )
    } yield ETImp( cut1, cut2 )

    if ( cuts( expansionProof ).isEmpty ) return ExpansionProof( expansionProof.expansionSequent filter { _.shallow != ETCut.cutAxiom } )

    def simplifiedEPWC( cuts: Seq[ETImp], es: ExpansionSequent ) =
      ExpansionProof( eliminateMerges.unsafe( ETCut( simpPropCuts( cuts ) ) +: es ) )

    var epwc = simplifiedEPWC( cuts( expansionProof ), expansionProof.expansionSequent filter { _.shallow != ETCut.cutAxiom } )

    while ( true )
      cuts( epwc ).view.flatMap {
        case cut @ ETImp( cut1, cut2 ) =>
          singleStep( cut1, cut2, cuts( epwc ).filterNot( _ == cut ), epwc.expansionSequent filter { _.shallow != ETCut.cutAxiom },
            epwc.eigenVariables union freeVariables( epwc.deep ),
            epwc.dependencyRelation )
      }.headOption match {
        case Some( ( newCuts, newES ) ) =>
          epwc = simplifiedEPWC( newCuts, newES )
        case None =>
          return {
            if ( cuts( epwc ).isEmpty ) return ExpansionProof( epwc.expansionSequent filter { _.shallow != ETCut.cutAxiom } )
            else epwc
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
                          expansionSequent: ExpansionSequent, freeVars: Set[Var],
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
      instances:      Map[Seq[Expr], ExpansionTree],
      eigenVariables: Seq[Var], child: ExpansionTree ): ( Seq[ETImp], ExpansionSequent ) = {
      if ( instances isEmpty ) return ( rest, expansionSequent )

      val eigenVarsToRename = generatedUpperSetInPO( eigenVariablesET( child ) ++ eigenVariables, dependencyRelation ) -- eigenVariables
      val nameGen = rename.awayFrom( freeVars )
      val renamings = for ( _ <- 0 until instances.size )
        yield Substitution( eigenVarsToRename map { ev => ev -> nameGen.fresh( ev ) } )
      val substs =
        for ( ( renaming, ( term, instance ) ) <- renamings zip instances )
          yield Substitution( eigenVariables zip term ) compose renaming

      val matchingSubstOption = substs find { s => ( substs zip instances.values ).forall { inst => s( inst._2.shallow ) == inst._1( child.shallow ) } }
      val matchingSubst = matchingSubstOption getOrElse Substitution()
      val needExtraCopy = matchingSubstOption.isEmpty

      val newCuts = for ( ( subst, ( term, instance ) ) <- substs zip instances ) yield {
        if ( instance.polarity.positive ) ETImp( matchingSubst( instance ), subst( child ) )
        else ETImp( subst( child ), matchingSubst( instance ) )
      }

      val substs_ = if ( needExtraCopy ) substs :+ Substitution() else substs
      (
        newCuts ++ ( for ( c <- rest; s <- substs_ ) yield s( c ).asInstanceOf[ETImp] ),
        for ( tree <- expansionSequent ) yield ETMerge( substs_.map { _( tree ) } ) )
    }

    Some( ( cut1, cut2 ) ) collect {
      case ( ETWeakQuantifierBlock( _, n, instances ), ETStrongQuantifierBlock( _, eigenVariables, child ) ) if n > 0 && eigenVariables.size == n =>
        quantifiedCut( instances, eigenVariables, child )
      case ( ETStrongQuantifierBlock( _, eigenVariables, child ), ETWeakQuantifierBlock( _, n, instances ) ) if n > 0 && eigenVariables.size == n =>
        quantifiedCut( instances, eigenVariables, child )
    }

  }
}
