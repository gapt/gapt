package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.proofs._
import at.logic.gapt.utils.NameGenerator

import scala.collection.mutable

private class skolemizeInferences( nameGen: NameGenerator ) {
  val skolemDefs = mutable.Map[LambdaExpression, Const]()

  // Info contains (generalizedFormula, isCutAnc)
  type Info = ( HOLFormula, Boolean )
  // We maintain the invariant that subst(info.map(_._1)) is equal to the end-sequent of the resulting proof.
  def apply( p: LKProof, info: Sequent[Info], subst: Substitution ): LKProof = {
    def sub( e: LambdaExpression ): LambdaExpression = BetaReduction.betaNormalize( subst( e ) )
    def suba( f: HOLAtom ): HOLAtom = sub( f ).asInstanceOf[HOLAtom]
    def subf( f: HOLFormula ): HOLFormula = sub( f ).asInstanceOf[HOLFormula]

    p match {
      case LogicalAxiom( atom )     => LogicalAxiom( subf( atom ) )
      case ReflexivityAxiom( term ) => ReflexivityAxiom( sub( term ) )
      case TheoryAxiom( axiom )     => TheoryAxiom( axiom map suba )

      case TopAxiom                 => TopAxiom
      case BottomAxiom              => BottomAxiom

      case p @ ContractionLeftRule( q, a1, a2 ) =>
        ContractionLeftRule( apply( q, p.getOccConnector parent info, subst ), a1, a2 )
      case p @ ContractionRightRule( q, a1, a2 ) =>
        ContractionRightRule( apply( q, p.getOccConnector parent info, subst ), a1, a2 )

      case p @ WeakeningLeftRule( q, f ) =>
        WeakeningLeftRule( apply( q, p.getOccConnector parent info, subst ), subf( f ) )
      case p @ WeakeningRightRule( q, f ) =>
        WeakeningRightRule( apply( q, p.getOccConnector parent info, subst ), subf( f ) )

      case p @ NegLeftRule( q, a ) =>
        val ( Neg( f ), ca ) = destruct( p, info )
        NegLeftRule( apply( q, p.getOccConnector parent info updated ( a, ( f, ca ) ), subst ), a )
      case p @ NegRightRule( q, a ) =>
        val ( Neg( f ), ca ) = destruct( p, info )
        NegRightRule( apply( q, p.getOccConnector parent info updated ( a, ( f, ca ) ), subst ), a )

      case p @ AndLeftRule( q, a1, a2 ) =>
        val ( And( f, g ), ca ) = destruct( p, info )
        AndLeftRule( apply( q, p.getOccConnector parent info updated ( a1, ( f, ca ) ) updated ( a2, ( g, ca ) ), subst ), a1, a2 )
      case p @ OrRightRule( q, a1, a2 ) =>
        val ( Or( f, g ), ca ) = destruct( p, info )
        OrRightRule( apply( q, p.getOccConnector parent info updated ( a1, ( f, ca ) ) updated ( a2, ( g, ca ) ), subst ), a1, a2 )
      case p @ ImpRightRule( q, a1, a2 ) =>
        val ( Imp( f, g ), ca ) = destruct( p, info )
        ImpRightRule( apply( q, p.getOccConnector parent info updated ( a1, ( f, ca ) ) updated ( a2, ( g, ca ) ), subst ), a1, a2 )

      case p @ AndRightRule( q1, a1, q2, a2 ) =>
        val ( And( f, g ), ca ) = destruct( p, info )
        AndRightRule(
          apply( q1, p.getLeftOccConnector parent info updated ( a1, ( f, ca ) ), subst ), a1,
          apply( q2, p.getRightOccConnector parent info updated ( a2, ( g, ca ) ), subst ), a2
        )
      case p @ OrLeftRule( q1, a1, q2, a2 ) =>
        val ( Or( f, g ), ca ) = destruct( p, info )
        OrLeftRule(
          apply( q1, p.getLeftOccConnector parent info updated ( a1, ( f, ca ) ), subst ), a1,
          apply( q2, p.getRightOccConnector parent info updated ( a2, ( g, ca ) ), subst ), a2
        )
      case p @ ImpLeftRule( q1, a1, q2, a2 ) =>
        val ( Imp( f, g ), ca ) = destruct( p, info )
        ImpLeftRule(
          apply( q1, p.getLeftOccConnector parent info updated ( a1, ( f, ca ) ), subst ), a1,
          apply( q2, p.getRightOccConnector parent info updated ( a2, ( g, ca ) ), subst ), a2
        )

      case p: EqualityRule =>
        val ( _, ca ) = info( p.auxInConclusion )
        val subProofNew =
          apply( p.subProof, p.getOccConnector parent info
            updated ( p.aux, ( p.auxFormula, ca ) )
            updated ( p.eq, info( p.eqInConclusion ) ),
            subst )
        if ( p.aux.isAnt )
          EqualityLeftRule( subProofNew, p.eq, p.aux, sub( p.replacementContext ).asInstanceOf[Abs] )
        else
          EqualityRightRule( subProofNew, p.eq, p.aux, sub( p.replacementContext ).asInstanceOf[Abs] )

      case p @ CutRule( q1, a1, q2, a2 ) =>
        CutRule(
          apply( q1, p.getLeftOccConnector parent ( info, ( p.cutFormula, true ) ), subst ), a1,
          apply( q2, p.getRightOccConnector parent ( info, ( p.cutFormula, true ) ), subst ), a2
        )

      case p @ WeakQuantifierRule( q, a, _, term, bound, pol ) =>
        val ( f, isCutAnc ) = destruct( p, info )
        val freshVar = nameGen fresh bound
        val q_ = apply( q, p.occConnectors.head parent info
          updated ( a, ( instantiate( f, freshVar ), isCutAnc ) ),
          subst compose Substitution( freshVar -> term ) )
        val Quant( v, matrix ) = subf( f )
        if ( pol ) ExistsRightRule( q_, a, matrix, sub( term ), v )
        else ForallLeftRule( q_, a, matrix, sub( term ), v )

      case p: SkolemQuantifierRule =>
        val ( f @ Quant( v, _ ), isCutAnc ) = destruct( p, info )
        val freshVar = nameGen fresh v
        val q_ = apply( p.subProof, p.occConnectors.head parent info
          updated ( p.aux, ( instantiate( f, freshVar ), isCutAnc ) ),
          subst compose Substitution( freshVar -> p.skolemTerm ) )
        if ( p.aux.isSuc ) ForallSkRightRule( q_, p.aux, subf( p.mainFormula ), sub( p.skolemTerm ), p.skolemDef )
        else ExistsSkLeftRule( q_, p.aux, subf( p.mainFormula ), sub( p.skolemTerm ), p.skolemDef )

      // cut-ancestors
      case p @ StrongQuantifierRule( q, a, eigen, quant, pol ) if info( p.mainIndices.head )._2 =>
        val q_ = apply( q, p.occConnectors.head parent info updated ( a, ( q.conclusion( a ), true ) ), subst )
        if ( pol ) ForallRightRule( q_, a, eigen, quant )
        else ExistsLeftRule( q_, a, eigen, quant )

      // end-sequent ancestors
      case p @ StrongQuantifierRule( q, a, eigen, quant, pol ) if !info( p.mainIndices.head )._2 =>
        val main = p.mainFormulas.head
        val ( f, false ) = destruct( p, info )
        val argVars = freeVariables( f ).toSeq.sortBy { _.name }
        val skolemDef = Abs( argVars, f )
        val skolemConst = skolemDefs.getOrElseUpdate(
          skolemDef,
          Const( nameGen freshWithIndex "s", FunctionType( eigen.exptype, argVars.map( _.exptype ) ) )
        )
        val skolemTerm = skolemConst( argVars: _* )
        val q_ = apply( q, p.occConnectors.head parent info
          updated ( a, ( instantiate( f, skolemTerm ), false ) ),
          subst compose Substitution( eigen -> skolemTerm ) )
        if ( pol ) ForallSkRightRule( q_, a, subf( main ), sub( skolemTerm ), skolemDef )
        else ExistsSkLeftRule( q_, a, subf( main ), sub( skolemTerm ), skolemDef )
    }
  }

  private def destruct( p: LKProof, info: Sequent[Info] ): Info = info( p.mainIndices.head ) match {
    case ( HOLAtom( _, _ ), isCutAnc ) =>
      ( p.mainFormulas.head, isCutAnc )
    case ( generalized, isCutAnc ) =>
      ( BetaReduction.betaNormalize( generalized ), isCutAnc )
  }
}

object skolemizeInferences {
  def apply( p: LKProof ): LKProof = {
    val p_ = regularize( p )
    val conv = new skolemizeInferences( rename.awayFrom( containedNames( p_ ) ) )
    conv( p_, p_.endSequent map { _ -> false }, Substitution() )
  }
}
