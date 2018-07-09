package gapt.proofs.expansion

import gapt.expr._

object eliminateMerges {
  def apply( expansionProof: ExpansionProof ): ExpansionProof =
    ExpansionProof( elim( expansionProof.expansionSequent ) )

  def unsafe( expansionSequent: ExpansionSequent ): ExpansionSequent =
    elim( expansionSequent )

  private def elim( expansionSequent: ExpansionSequent ): ExpansionSequent = {
    var eigenVarSubst = Substitution()
    var skolemDefs = Map[Expr, Expr]()

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
      case ( t: ETWeakening, s ) => merge( s )
      case ( t, s: ETWeakening ) => merge( t )
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
          ETMerge( merge( tree1 ), merge( tree2 ) )
        }
      case ( tree1 @ ETStrongQuantifier( _, v1, _ ), tree2 @ ETSkolemQuantifier( _, st2, sd2, _ ) ) =>
        eigenVarSubst = eigenVarSubst compose Substitution( v1 -> st2 )
        skolemDefs += ( st2 -> sd2 )
        ETMerge( merge( tree1 ), merge( tree2 ) )
      case ( tree2 @ ETSkolemQuantifier( _, st2, sd2, _ ), tree1 @ ETStrongQuantifier( _, v1, _ ) ) =>
        eigenVarSubst = eigenVarSubst compose Substitution( v1 -> st2 )
        skolemDefs += ( st2 -> sd2 )
        ETMerge( merge( tree2 ), merge( tree1 ) )
      case ( ETSkolemQuantifier( shallow, st1, sf1, t1 ), ETSkolemQuantifier( _, st2, sf2, t2 ) ) if st1 == st2 =>
        // the st1 != st2 case is handled by the default case
        ETSkolemQuantifier( shallow, st1, sf1, merge2( t1, t2 ) )
      case ( ETMerges( ts0 ), s: ETSkolemQuantifier ) =>
        // Skolem quantifier inferences on different skolem terms s1 and s2 are preserved
        // as ETMerge(s1, s2). Group skolem ETs by skolem term and merge; also merge
        // non-skolem ETs. Return ETMerges( non_sk +: sk1 +: sk2 +: ... ) where non_sk is
        // the non-skolem ET and sk1, sk2, ... have different skolem terms.
        val ts = ( ts0 :+ s ).filterNot( _.isInstanceOf[ETWeakening] )
        ( ts.filterNot( _.isInstanceOf[ETSkolemQuantifier] ).reduceOption( merge2 ).toSeq ++
          ts.collect { case t @ ETSkolemQuantifier( _, _, _, _ ) => t }
          .groupBy( _.skolemTerm ).map {
            case ( _, Vector( tree ) ) => merge( tree )
            case ( _, trees )          => trees.reduce( merge2 )
          } ).reduce( ETMerge( _, _ ) )
      case ( s: ETSkolemQuantifier, t @ ETMerges( ts0 ) ) =>
        merge2( t, s )
      case ( t, s ) =>
        ETMerge( merge( t ), merge( s ) )
    }

    val mergedSequent = expansionSequent map merge

    if ( eigenVarSubst.map.isEmpty ) {
      mergedSequent
    } else {
      val skDefsPerVar = Map() ++ ( for {
        ( v, st ) <- eigenVarSubst.map
        if !st.isInstanceOf[Var]
      } yield v -> skolemDefs( st ) )
      elim( mergedSequent map { expansionTreeSubstitution( eigenVarSubst, skDefsPerVar, _ ) } )
    }
  }
}
