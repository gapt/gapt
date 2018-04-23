package gapt.proofs.expansion

import gapt.expr._
import gapt.expr.fol.folSubTerms
import gapt.expr.hol.instantiate
import gapt.provers.escargot.LPO
import gapt.provers.verit.VeriT

object removeSkolemCongruences {

  def repl( m: Map[Expr, Expr], et: ExpansionTree, newSh: Formula ): ExpansionTree =
    ( et, newSh ) match {
      case ( ETTop( _ ) | ETBottom( _ ), _ ) => et
      case ( ETAtom( _, pol ), newSh: Atom ) => ETAtom( newSh, pol )
      case ( ETWeakening( _, pol ), _ )      => ETWeakening( newSh, pol )
      case ( ETMerge( a, b ), _ )            => ETMerge( repl( m, a, newSh ), repl( m, b, newSh ) )
      case ( ETNeg( a ), Neg( f ) )          => ETNeg( repl( m, a, f ) )
      case ( ETAnd( a, b ), And( f, g ) )    => ETAnd( repl( m, a, f ), repl( m, b, g ) )
      case ( ETOr( a, b ), Or( f, g ) )      => ETOr( repl( m, a, f ), repl( m, b, g ) )
      case ( ETImp( a, b ), Imp( f, g ) )    => ETImp( repl( m, a, f ), repl( m, b, g ) )
      case ( ETStrongQuantifier( _, ev, ch ), _ ) =>
        ETStrongQuantifier( newSh, ev, repl( m, ch, instantiate( newSh, ev ) ) )
      case ( ETSkolemQuantifier( _, Apps( skC, skAs ), skD, ch ), _ ) =>
        val newSkT = skC( TermReplacement( skAs, m ) )
        ETSkolemQuantifier( newSh, newSkT, skD,
          repl( m, ch, instantiate( newSh, newSkT ) ) )
      case ( ETWeakQuantifier( _, insts ), _ ) =>
        ETWeakQuantifier.withMerge(
          newSh,
          insts.view.map {
            case ( t, ch ) =>
              val newT = TermReplacement( t, m )
              newT -> repl( m, ch, BetaReduction.betaNormalize( instantiate( newSh, newT ) ) )
          } )
    }

  def remove1( m: Map[Expr, Expr], ep: ExpansionProof ): ExpansionProof =
    eliminateMerges( ExpansionProof( ep.expansionSequent.
      map( et => ETMerge( et, repl( m, et, et.shallow ) ) ) ) )

  def getAllPossibleCongruences( ep: ExpansionProof ): Vector[( Expr, Expr )] = {
    val skSyms = ep.skolemFunctions.skolemDefs.keySet
    val skTerms = folSubTerms( ep.deep.elements ).collect {
      case skTerm @ Apps( skSym: Const, _ ) if skSyms( skSym ) => skTerm
    }
    skTerms.groupBy { case Apps( c: Const, _ ) => c }.
      values.flatMap( skTs =>
        skTs.subsets( 2 ).map( _.toList ).
          flatMap { case List( Apps( _, as ), Apps( _, bs ) ) => as zip bs } ).
      toVector
  }

  def getCongruencesViaVeriT( ep: ExpansionProof ): Vector[( Expr, Expr )] = {
    val skSyms = ep.skolemFunctions.skolemDefs.keySet
    val Some( epwc ) = VeriT.getExpansionProof( ep.deep )
    epwc.expansionSequent.antecedent.flatMap {
      case ETWeakQuantifierBlock( All.Block( _, Imp( _, Eq( Apps( f: Const, _ ), Apps( f_, _ ) ) ) ), n,
        insts ) if n > 0 && f == f_ && skSyms( f ) =>
        insts.flatMap { case ( inst, _ ) => inst.splitAt( n / 2 ).zipped.view }
      case _ => Seq()
    }
  }

  def simplCongrs( congrs: Vector[( Expr, Expr )] ): Vector[( Expr, Expr )] = {
    val lpo = LPO( containedNames( congrs ).collect { case c: Const => c }.toSeq.sortBy( _.name ) )
    def lt( a: Expr, b: Expr ): Boolean = lpo.lt( a, b, true )
    congrs.view.
      filter( c => c._1 != c._2 ).
      map( c => if ( lt( c._1, c._2 ) ) c.swap else c ).
      distinct.
      sortWith( ( c1, c2 ) => lt( c1._1, c2._1 ) ).
      reverseIterator.toVector
  }

  def remove( ep: ExpansionProof, congrs: Vector[( Expr, Expr )] ): ExpansionProof =
    congrs match {
      case Vector() => ep
      case ( a, b ) +: congrs_ =>
        val repl = Map( a -> b )
        val ep_ = remove1( repl, ep )
        remove(
          ep_,
          simplCongrs( congrs_ ++ TermReplacement( congrs_, repl ) ) )
    }

  def apply( ep: ExpansionProof ): ExpansionProof =
    remove( ep, simplCongrs( getAllPossibleCongruences( ep ) ) )

}
