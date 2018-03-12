package gapt.proofs.lk

import gapt.expr._
import gapt.expr.hol.{ HOLPosition, SkolemFunctions, instantiate }
import gapt.proofs._
import gapt.utils.NameGenerator

import scala.collection.mutable

private class skolemizeLK(
    nameGen:            NameGenerator,
    proofTheoretic:     Boolean,
    skolemizeAboveCuts: Boolean )( implicit ctx: MutableContext ) {
  type PosInEndSequent = Seq[Int]

  val skolemDefs = mutable.Map[( Expr, PosInEndSequent ), Const]()

  // The general idea is that as we proceed upwards through the proof, we maintain
  // certain information about each formula in the current sequent.
  //
  // In particular, we keep a list of *generalizations* of each formula.  The generalization happens in weak
  // quantifier inferences: instead of instantiating with the term, we instantiate with a fresh variable.
  // lowerWeakQuantifierTermVars is the list of these fresh variables that were already used for
  // descendants of the formula.
  //
  // These generalizations are connected to the current sequent via a substitution (there is only one substitution
  // for the whole sequent, so it is not included in the per-formula Info).  This substitution maps each of the
  // generalizations to the current formula.
  case class Info(
      generalizedFormulas:         Seq[Formula],
      isCutAnc:                    Boolean,
      lowerWeakQuantifierTermVars: Seq[Var],
      position:                    PosInEndSequent ) {
    val generalizedFormula = generalizedFormulas.head

    def atPosition( pos: Int* ): Info = atPosition( HOLPosition( pos: _* ) )
    def atPosition( pos: HOLPosition ): Info =
      copy( generalizedFormulas.filter( !_.isInstanceOf[Atom] ).flatMap( _.get( pos ) ).map( _.asInstanceOf[Formula] ) )

    def instantiateQuantifier( term: Expr ) =
      copy(
        generalizedFormulas = generalizedFormulas.
          collect { case quant @ Quant( _, _, _ ) => BetaReduction.betaNormalize( instantiate( quant, term ) ) },
        position = position :+ 1 )

    def instantiateWeakQuantifier( freshVar: Var ) =
      instantiateQuantifier( freshVar ).copy( lowerWeakQuantifierTermVars = lowerWeakQuantifierTermVars :+ freshVar )

    def addGeneralization( formula: Formula ) =
      copy( generalizedFormulas = generalizedFormulas :+ formula )
  }
  // We maintain the invariant that subst(info.map(_.generalizedFormula)) is beta-delta-equal to the end-sequent of the resulting proof.
  def apply( p: LKProof, info: Sequent[Info], subst: Substitution ): LKProof = {
    def sub( e: Expr ): Expr = BetaReduction.betaNormalize( subst( e ) )
    def suba( f: Atom ): Atom = sub( f ).asInstanceOf[Atom]
    def subf( f: Formula ): Formula = sub( f ).asInstanceOf[Formula]

    p match {
      case LogicalAxiom( atom )     => LogicalAxiom( subf( atom ) )
      case ReflexivityAxiom( term ) => ReflexivityAxiom( sub( term ) )

      case ProofLink( name, seq )   => ProofLink( subst( name ), seq map subf )

      case TopAxiom                 => TopAxiom
      case BottomAxiom              => BottomAxiom

      case p @ ContractionLeftRule( q, a1, a2 ) =>
        ContractionLeftRule( apply( q, p.getSequentConnector parent info, subst ), a1, a2 )
      case p @ ContractionRightRule( q, a1, a2 ) =>
        ContractionRightRule( apply( q, p.getSequentConnector parent info, subst ), a1, a2 )

      case p @ WeakeningLeftRule( q, f ) =>
        WeakeningLeftRule( apply( q, p.getSequentConnector parent info, subst ), subf( f ) )
      case p @ WeakeningRightRule( q, f ) =>
        WeakeningRightRule( apply( q, p.getSequentConnector parent info, subst ), subf( f ) )

      case p @ NegLeftRule( q, a ) =>
        NegLeftRule( apply( q, p.getSequentConnector.parent( info ).updated( a, info( p.mainIndices.head ).atPosition( 1 ) ), subst ), a )
      case p @ NegRightRule( q, a ) =>
        NegRightRule( apply( q, p.getSequentConnector.parent( info ).updated( a, info( p.mainIndices.head ).atPosition( 1 ) ), subst ), a )

      case p @ AndLeftRule( q, a1, a2 ) =>
        AndLeftRule( apply(
          q,
          p.getSequentConnector.parent( info ).
            updated( a1, info( p.mainIndices.head ).atPosition( 1 ) ).
            updated( a2, info( p.mainIndices.head ).atPosition( 2 ) ),
          subst ), a1, a2 )
      case p @ OrRightRule( q, a1, a2 ) =>
        OrRightRule( apply(
          q,
          p.getSequentConnector.parent( info ).
            updated( a1, info( p.mainIndices.head ).atPosition( 1 ) ).
            updated( a2, info( p.mainIndices.head ).atPosition( 2 ) ),
          subst ), a1, a2 )
      case p @ ImpRightRule( q, a1, a2 ) =>
        ImpRightRule( apply(
          q,
          p.getSequentConnector.parent( info ).
            updated( a1, info( p.mainIndices.head ).atPosition( 1 ) ).
            updated( a2, info( p.mainIndices.head ).atPosition( 2 ) ),
          subst ), a1, a2 )

      case p @ AndRightRule( q1, a1, q2, a2 ) =>
        AndRightRule(
          apply( q1, p.getLeftSequentConnector.parent( info ).updated( a1, info( p.mainIndices.head ).atPosition( 1 ) ), subst ), a1,
          apply( q2, p.getRightSequentConnector.parent( info ).updated( a2, info( p.mainIndices.head ).atPosition( 2 ) ), subst ), a2 )
      case p @ OrLeftRule( q1, a1, q2, a2 ) =>
        OrLeftRule(
          apply( q1, p.getLeftSequentConnector.parent( info ).updated( a1, info( p.mainIndices.head ).atPosition( 1 ) ), subst ), a1,
          apply( q2, p.getRightSequentConnector.parent( info ).updated( a2, info( p.mainIndices.head ).atPosition( 2 ) ), subst ), a2 )
      case p @ ImpLeftRule( q1, a1, q2, a2 ) =>
        ImpLeftRule(
          apply( q1, p.getLeftSequentConnector.parent( info ).updated( a1, info( p.mainIndices.head ).atPosition( 1 ) ), subst ), a1,
          apply( q2, p.getRightSequentConnector.parent( info ).updated( a2, info( p.mainIndices.head ).atPosition( 2 ) ), subst ), a2 )

      case p: EqualityRule =>
        val subProofNew =
          apply( p.subProof, p.getSequentConnector.parent( info ).
            updated( p.aux, info( p.auxInConclusion ).copy( generalizedFormulas = Seq( p.auxFormula ) ) ).
            updated( p.eq, info( p.eqInConclusion ) ),
            subst )
        if ( p.aux.isAnt )
          EqualityLeftRule( subProofNew, p.eq, p.aux, sub( p.replacementContext ).asInstanceOf[Abs] )
        else
          EqualityRightRule( subProofNew, p.eq, p.aux, sub( p.replacementContext ).asInstanceOf[Abs] )

      case p @ CutRule( q1, a1, q2, a2 ) =>
        CutRule(
          apply( q1, p.getLeftSequentConnector.parent( info, Info( Seq( p.cutFormula ), isCutAnc = true, Seq(), Seq( -1 ) ) ), subst ), a1,
          apply( q2, p.getRightSequentConnector.parent( info, Info( Seq( p.cutFormula ), isCutAnc = true, Seq(), Seq( -1 ) ) ), subst ), a2 )

      case p @ DefinitionLeftRule( q, a, m ) =>
        val qNew = apply( q, p.getSequentConnector.parent( info ).
          updated( a, info( p.mainIndices.head ).copy( generalizedFormulas = Seq( q.conclusion( a ) ) ) ), subst )
        DefinitionLeftRule( qNew, a, subst( m ) )
      case p @ DefinitionRightRule( q, a, m ) =>
        val qNew = apply( q, p.getSequentConnector.parent( info ).
          updated( a, info( p.mainIndices.head ).copy( generalizedFormulas = Seq( q.conclusion( a ) ) ) ), subst )
        DefinitionRightRule( qNew, a, subst( m ) )

      case p @ WeakQuantifierRule( q, a, _, term, bound, pol ) =>
        val freshVar = nameGen fresh bound
        val q_ = apply( q, p.occConnectors.head.parent( info ).
          updated( a, info( p.mainIndices.head ).
            instantiateWeakQuantifier( freshVar ).
            addGeneralization( q.conclusion( a ) ) ),
          subst compose Substitution( freshVar -> term ) )
        val Quant( v, matrix, _ ) = subf( p.mainFormulas.head )
        if ( pol ) ExistsRightRule( q_, a, matrix, sub( term ), v )
        else ForallLeftRule( q_, a, matrix, sub( term ), v )

      case p: SkolemQuantifierRule =>
        val freshVar = nameGen fresh p.quantifiedVariable
        val q_ = apply( p.subProof, p.occConnectors.head.parent( info ).
          updated( p.aux, info( p.mainIndices.head ).instantiateQuantifier( freshVar ) ),
          subst compose Substitution( freshVar -> p.skolemTerm ) )
        if ( p.aux.isSuc ) ForallSkRightRule( q_, p.aux, subf( p.mainFormula ), sub( p.skolemTerm ), p.skolemDef )
        else ExistsSkLeftRule( q_, p.aux, subf( p.mainFormula ), sub( p.skolemTerm ), p.skolemDef )

      // Eigenvariable inferences that we keep
      case p @ StrongQuantifierRule( q, a, eigen, quant, pol ) if info( p.mainIndices.head ).isCutAnc && !skolemizeAboveCuts =>
        val q_ = apply( q, p.occConnectors.head.parent( info ).
          updated( a, info( p.mainIndices.head ).instantiateQuantifier( eigen ) ),
          subst )
        if ( pol ) ForallRightRule( q_, a, eigen, quant )
        else ExistsLeftRule( q_, a, eigen, quant )

      // Eigenvariable inferences that are Skolemized
      case p @ StrongQuantifierRule( q, a, eigen, quant, pol ) =>
        val Some( genFormula ) = info( p.mainIndices.head ).generalizedFormulas.find( !_.isInstanceOf[Atom] )
        val argVars_ = info( p.mainIndices.head ).lowerWeakQuantifierTermVars ++ freeVariables( genFormula )
        val argVars = if ( proofTheoretic ) argVars_.distinct else argVars_.filter( freeVariables( genFormula ) ).distinct
        val skolemDef = Abs( argVars, genFormula )
        val skolemConst = skolemDefs.getOrElseUpdate(
          ( skolemDef, if ( proofTheoretic ) info( p.mainIndices.head ).position else Seq() ),
          ctx.addSkolemSym( skolemDef, nameGen freshWithIndex "s", !proofTheoretic ) )
        val skolemTerm = skolemConst( argVars: _* )
        val q_ = apply( q, p.occConnectors.head.parent( info ).
          updated( a, info( p.mainIndices.head ).instantiateQuantifier( skolemTerm ) ),
          subst compose Substitution( eigen -> skolemTerm ) )
        if ( pol ) ForallSkRightRule( q_, a, subf( p.mainFormulas.head ), sub( skolemTerm ), skolemDef )
        else ExistsSkLeftRule( q_, a, subf( p.mainFormulas.head ), sub( skolemTerm ), skolemDef )
    }
  }
}

object skolemizeLK {
  /**
   * Skolemize a proof in LK by introducing the Skolem inferences [[ExistsSkLeftRule]] and [[ForallSkRightRule]].
   * This transformation does not increase the number of inferences (with tree-like counting).
   *
   * @param proofTheoretic  Whether to Skolemize proof-theoretically.  Setting this flag to true guarantees
   *                        that the expansion proof of the Skolemized proof can be deskolemized using the naive
   *                        linear-time algorithm.
   */
  def apply( p: LKProof, proofTheoretic: Boolean = true, skolemizeAboveCuts: Boolean = false )( implicit ctx: MutableContext = MutableContext.guess( p ) ): LKProof = {
    val p_ = regularize( p )
    val conv = new skolemizeLK(
      new NameGenerator( containedNames( p_ ).map( _.name ) ++ ctx.names ),
      proofTheoretic, skolemizeAboveCuts )
    conv(
      p_,
      for ( ( f, i ) <- p_.endSequent.zipWithIndex )
        yield conv.Info( Seq( f ), isCutAnc = false, Seq(), Seq( i.toInt ) ),
      Substitution() )
  }
}
