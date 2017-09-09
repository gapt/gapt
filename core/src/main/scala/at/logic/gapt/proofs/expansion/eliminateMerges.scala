package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr.Substitution

object eliminateMerges {
  def apply( expansionProof: ExpansionProofWithCut ): ExpansionProofWithCut =
    ExpansionProofWithCut( elim( expansionProof.expansionWithCutAxiom.expansionSequent ) )

  def apply( expansionProof: ExpansionProof ): ExpansionProof =
    ExpansionProof( elim( expansionProof.expansionSequent ) )

  def unsafe( expansionSequent: ExpansionSequent ): ExpansionSequent =
    elim( expansionSequent )

  private def elim( expansionSequent: ExpansionSequent ): ExpansionSequent = {
    var needToMergeAgain = false
    var eigenVarSubst = Substitution()

    def merge( tree: ExpansionTree ): ExpansionTree = tree match {
      case ETMerge( t, s )             => merge2( t, s )
      case _: ETAtom                   => tree
      case tree: ETDefinition          => tree.copy( child = merge( tree.child ) )
      case ETWeakening( formula, pol ) => ETWeakening( formula, pol )
      case _: ETTop | _: ETBottom      => tree
      case ETNeg( t )                  => ETNeg( merge( t ) )
      case ETAnd( t, s )               => ETAnd( merge( t ), merge( s ) )
      case ETOr( t, s )                => ETOr( merge( t ), merge( s ) )
      case ETImp( t, s )               => ETImp( merge( t ), merge( s ) )
      case ETWeakQuantifier( shallow, inst ) =>
        ETWeakQuantifier( shallow, Map() ++ inst.mapValues( merge ) )
      case tree: ETStrongQuantifier => tree.copy( child = merge( tree.child ) )
      case tree: ETSkolemQuantifier => tree.copy( child = merge( tree.child ) )
    }
    def merge2( tree1: ExpansionTree, tree2: ExpansionTree ): ExpansionTree = ( tree1, tree2 ) match {
      case ( _: ETWeakening, s ) => merge( s )
      case ( t, _: ETWeakening ) => merge( t )
      case ( ETMerge( t1, t2 ), s ) if !s.isInstanceOf[ETSkolemQuantifier] =>
        merge2( t1, t2 ) match {
          case t: ETMerge => ETMerge( t, merge( s ) )
          case t          => merge2( t, s )
        }
      case ( t, s: ETMerge )        => merge2( s, t )
      case ( t: ETAtom, _: ETAtom ) => t
      case ( ETDefinition( sh, t ), ETDefinition( _, s ) ) =>
        if ( t.shallow == s.shallow ) ETDefinition( sh, merge2( t, s ) )
        else ETMerge( merge( tree1 ), merge( tree2 ) )
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
            else merge2( inst1( selected ), inst2( selected ) ) ) ).toMap )
      case ( tree1 @ ETStrongQuantifier( shallow, v1, t1 ), tree2 @ ETStrongQuantifier( _, v2, t2 ) ) =>
        if ( v1 == v2 ) {
          ETStrongQuantifier( shallow, v1, merge2( t1, t2 ) )
        } else {
          eigenVarSubst = eigenVarSubst compose Substitution( v2 -> v1 )
          needToMergeAgain = true

          ETMerge( merge( tree1 ), merge( tree2 ) )
        }
      case ( ETStrongQuantifier( _, v1, t1 ), ETSkolemQuantifier( shallow, st2, sf2, t2 ) ) =>
        val localSubst = Substitution( v1 -> st2 )

        needToMergeAgain = true
        if ( !eigenVarSubst.map.isDefinedAt( v1 ) )
          eigenVarSubst = eigenVarSubst compose localSubst

        ETSkolemQuantifier( shallow, st2, sf2, merge2( localSubst( t1 ), t2 ) )
      case ( t: ETSkolemQuantifier, s: ETStrongQuantifier ) => merge2( s, t )
      case ( ETSkolemQuantifier( shallow, st1, sf1, t1 ), ETSkolemQuantifier( _, st2, sf2, t2 ) ) if st1 == st2 =>
        ETSkolemQuantifier( shallow, st1, sf1, merge2( t1, t2 ) )
      case ( ETMerges( ts0 ), s: ETSkolemQuantifier ) =>
        val ts = ts0 :+ s
        ( ts.filterNot( _.isInstanceOf[ETSkolemQuantifier] ).map( merge ) ++
          ts.collect { case t: ETSkolemQuantifier => t }.
          groupBy( _.skolemTerm ).map {
            case ( _, Vector( tree ) ) => merge( tree )
            case ( _, trees )          => trees.reduce( merge2 )
          } ).reduce( ETMerge( _, _ ) )
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
