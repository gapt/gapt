package gapt.proofs.expansion

import gapt.expr._
import gapt.expr.formula.Formula
import gapt.expr.subst.Substitution
import gapt.proofs.Sequent

import scala.annotation.tailrec
import scala.collection.mutable

private class MutableSubstitution {
  var subst = Substitution()
  def add( v: Var, by: Expr ): Unit =
    if ( v != by ) subst = subst compose Substitution( v -> by )
}

/**
 * Mutable tree data structure used during merging.
 *
 * A [[MergeNode]] conceptually represents an irreducible merge node.
 * For example, a merge of two incompatible Skolem nodes, or a merge of
 * a definition node with a node for a binary connective.
 *
 * In the first step, we convert the input expansion tree to a tree
 * of [[MergeNode]]s using the [[add()]] method.  This method does
 * most of the work, such as computing the substitution for eigenvariables
 * that need to be merged.
 *
 * In the second step, we convert the [[MergeNode]] back into an expansion
 * tree term using [[toETt]].
 *
 * There are two advantages compared to the alternative of using the standard
 * expansion tree terms during merging as well:
 *
 *  1. Performance.
 *  2. It is very easy to handle the AC-rewriting required for merging.  Consider
 *     e.g. the merge of many Skolem nodes with different Skolem terms.  We
 *     need to group these terms by their Skolem terms in order to merge them.
 *     In the previous implementation we used a fragile hack that relied on the
 *     left-associative construction of merges.
 */
private class MergeNode {
  var hasAtom = false
  var hasNullary = false

  var unary: MergeNode = _

  var binaryLeft: MergeNode = _
  var binaryRight: MergeNode = _

  var weak: mutable.Map[Expr, MergeNode] = _

  var strongEV: Var = _
  var strongChild: MergeNode = _

  var defs: mutable.Map[Formula, MergeNode] = _

  var skolems: mutable.Map[Expr, MergeNode] = _

  def toETt: ETt = {
    var result: ETt = null
    def write( et: ETt ): Unit =
      result = if ( result == null ) et else ETtMerge( result, et )
    if ( hasAtom ) write( ETtAtom )
    if ( hasNullary ) write( ETtNullary )
    if ( unary != null ) write( ETtUnary( unary.toETt ) )
    if ( binaryLeft != null || binaryRight != null )
      write( ETtBinary( binaryLeft.toETt, binaryRight.toETt ) )
    if ( weak != null ) write( ETtWeak( Map() ++ weak.view.mapValues( _.toETt ).toMap ) )
    if ( strongEV != null ) write( ETtStrong( strongEV, strongChild.toETt ) )
    if ( defs != null ) for ( ( sh, ch ) <- defs ) write( ETtDef( sh, ch.toETt ) )
    if ( skolems != null ) for ( ( skT, ch ) <- skolems ) write( ETtSkolem( skT, ch.toETt ) )
    if ( result == null ) ETtWeakening else result
  }

  def add( et: ETt )( implicit subst: MutableSubstitution ): Unit =
    et match {
      case ETtAtom      => hasAtom = true
      case ETtWeakening =>
      case ETtMerge( child1, child2 ) =>
        add( child2 )
        add( child1 )
      case ETtNullary => hasNullary = true
      case ETtUnary( child ) =>
        if ( unary == null ) unary = new MergeNode
        unary.add( child )
      case ETtBinary( child1, child2 ) =>
        if ( binaryLeft == null ) { binaryLeft = new MergeNode; binaryRight = new MergeNode }
        binaryLeft.add( child1 )
        binaryRight.add( child2 )
      case ETtWeak( insts ) =>
        if ( weak == null ) weak = mutable.Map()
        for ( ( inst, ch ) <- insts )
          weak.getOrElseUpdate( inst, new MergeNode ).add( ch )
      case ETtStrong( eigenVar, child ) =>
        if ( skolems != null ) {
          val ( skT, merger ) = skolems.head
          subst.add( eigenVar, skT )
          merger.add( child )
        } else {
          if ( strongEV == null ) {
            strongEV = eigenVar
            strongChild = new MergeNode
          } else {
            subst.add( eigenVar, strongEV )
          }
          strongChild.add( child )
        }
      case ETtDef( shallow, child ) =>
        if ( defs == null ) defs = mutable.Map.empty
        defs.getOrElseUpdate( shallow, new MergeNode ).add( child )
      case ETtSkolem( skTerm, child ) =>
        if ( strongEV != null ) {
          require( skolems == null )
          subst.add( strongEV, skTerm )
          skolems = mutable.Map( skTerm -> strongChild )
          strongChild = null
          strongEV = null
        }
        if ( skolems == null ) skolems = mutable.Map.empty
        skolems.getOrElseUpdate( skTerm, new MergeNode ).add( child )
    }
}
private object MergeNode {
  def apply( et: ExpansionTree, subst: MutableSubstitution ): ExpansionTree =
    et.copy( term = apply( et.term, subst ) )
  def apply( et: ETt, subst: MutableSubstitution ): ETt = {
    val merger = new MergeNode
    merger.add( et )( subst )
    merger.toETt
  }
}

/** Reduces merge nodes in an expansion proof. */
object eliminateMerges {
  def apply( et: ETt ): ETt = apply( Sequent() :+ et ).succedent.head
  @tailrec private def go[T: ClosedUnderSub]( t: T )( merge: ( T, MutableSubstitution ) => T ): T = {
    val subst = new MutableSubstitution
    val merged = merge( t, subst )
    if ( subst.subst.isEmpty ) merged else go( subst.subst( merged ) )( merge )
  }
  def apply( es: Sequent[ETt] ): Sequent[ETt] = go( es )( ( es, subst ) => es.map( MergeNode( _, subst ) ) )
  def apply( es: Sequent[ExpansionTree] )( implicit dummyImplicit: DummyImplicit ): Sequent[ExpansionTree] =
    go( es )( ( es, subst ) => es.map( MergeNode( _, subst ) ) )
  def apply( ep: ExpansionProof ): ExpansionProof =
    ExpansionProof( apply( ep.expansionSequent ) )
}
