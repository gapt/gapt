package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ HOLPosition, instantiate }
import at.logic.gapt.proofs.lksk._
import at.logic.gapt.proofs.lksk
import at.logic.gapt.proofs._

import scala.collection.mutable

private class LKToLKsk2( consts: Set[Const], vars: Set[Var] ) {
  val nameGen = rename.awayFrom( consts )
  val varNameGen = rename.awayFrom( vars )

  val skolemDefs = mutable.Map[LambdaExpression, Const]()

  // info contains ([(weakVar, label)], generalizedFormula, isCutAnc)
  type Info = ( Seq[( Var, LambdaExpression )], HOLFormula, Boolean )
  def apply( p: LKProof, info: Sequent[Info], subst: Map[Var, LambdaExpression] ): LKskProof = {
    def subfixedpoint( e: LambdaExpression ): LambdaExpression = {
      val e_ = Substitution( subst )( e )
      if ( e == e_ ) e else subfixedpoint( e_ )
    }
    def sub( e: LambdaExpression ): LambdaExpression = BetaReduction.betaNormalize( subfixedpoint( e ) )
    def subf( f: HOLFormula ): HOLFormula = sub( f: LambdaExpression ).asInstanceOf[HOLFormula]

    p match {
      case LogicalAxiom( atom )     => lksk.Axiom( info( Ant( 0 ) )._1.map { _._2 }.map( sub ), info( Suc( 0 ) )._1.map { _._2 }.map( sub ), sub( atom ).asInstanceOf[HOLAtom] )
      case ReflexivityAxiom( term ) => Reflexivity( info( Suc( 0 ) )._1.map { _._2 }.map( sub ), sub( term ) )

      case TopAxiom                 => TopRight( info( Suc( 0 ) )._1.map { _._2 }.map( sub ) )
      case BottomAxiom              => BottomLeft( info( Suc( 0 ) )._1.map { _._2 }.map( sub ) )

      case p @ ContractionLeftRule( q, a1: Ant, a2: Ant ) =>
        ContractionLeft( apply( q, p.getOccConnector parent info, subst ), a1, a2 )
      case p @ ContractionRightRule( q, a1: Suc, a2: Suc ) =>
        ContractionRight( apply( q, p.getOccConnector parent info, subst ), a1, a2 )

      case p @ WeakeningLeftRule( q, f ) =>
        WeakeningLeft( apply( q, p.getOccConnector parent info, subst ), info( p.mainIndices.head )._1.map { _._2 }.map( sub ) -> subf( f ) )
      case p @ WeakeningRightRule( q, f ) =>
        WeakeningRight( apply( q, p.getOccConnector parent info, subst ), info( p.mainIndices.head )._1.map { _._2 }.map( sub ) -> subf( f ) )

      case p @ NegLeftRule( q, a: Suc ) =>
        val ( w, Neg( f ), ca ) = destruct( p, info )
        NegLeft( apply( q, p.getOccConnector parent info updated ( a, ( w, f, ca ) ), subst ), a )
      case p @ NegRightRule( q, a: Ant ) =>
        val ( w, Neg( f ), ca ) = destruct( p, info )
        NegRight( apply( q, p.getOccConnector parent info updated ( a, ( w, f, ca ) ), subst ), a )

      case p @ AndLeftRule( q, a1: Ant, a2: Ant ) =>
        val ( w, And( f, g ), ca ) = destruct( p, info )
        AndLeft( apply( q, p.getOccConnector parent info updated ( a1, ( w, f, ca ) ) updated ( a2, ( w, g, ca ) ), subst ), a1, a2 )
      case p @ OrRightRule( q, a1: Suc, a2: Suc ) =>
        val ( w, Or( f, g ), ca ) = destruct( p, info )
        OrRight( apply( q, p.getOccConnector parent info updated ( a1, ( w, f, ca ) ) updated ( a2, ( w, g, ca ) ), subst ), a1, a2 )
      case p @ ImpRightRule( q, a1: Ant, a2: Suc ) =>
        val ( w, Imp( f, g ), ca ) = destruct( p, info )
        ImpRight( apply( q, p.getOccConnector parent info updated ( a1, ( w, f, ca ) ) updated ( a2, ( w, g, ca ) ), subst ), a1, a2 )

      case p @ AndRightRule( q1, a1: Suc, q2, a2: Suc ) =>
        val ( w, And( f, g ), ca ) = destruct( p, info )
        AndRight(
          apply( q1, p.getLeftOccConnector parent info updated ( a1, ( w, f, ca ) ), subst ), a1,
          apply( q2, p.getRightOccConnector parent info updated ( a2, ( w, g, ca ) ), subst ), a2
        )
      case p @ OrLeftRule( q1, a1: Ant, q2, a2: Ant ) =>
        val ( w, Or( f, g ), ca ) = destruct( p, info )
        OrLeft(
          apply( q1, p.getLeftOccConnector parent info updated ( a1, ( w, f, ca ) ), subst ), a1,
          apply( q2, p.getRightOccConnector parent info updated ( a2, ( w, g, ca ) ), subst ), a2
        )
      case p @ ImpLeftRule( q1, a1: Suc, q2, a2: Ant ) =>
        val ( w, Imp( f, g ), ca ) = destruct( p, info )
        ImpLeft(
          apply( q1, p.getLeftOccConnector parent info updated ( a1, ( w, f, ca ) ), subst ), a1,
          apply( q2, p.getRightOccConnector parent info updated ( a2, ( w, g, ca ) ), subst ), a2
        )

      case p: EqualityRule =>
        val ( w, _, ca ) = info( p.auxInConclusion )
        Equality(
          apply( p.subProof, p.getOccConnector parent info
            updated ( p.aux, ( w, p.auxFormula, ca ) )
            updated ( p.eq, info( p.eqInConclusion ) ),
            subst ),
          p.eq.asInstanceOf[Ant], p.aux, p.leftToRight,
          p.replacementContext
        )

      case p @ CutRule( q1, a1: Suc, q2, a2: Ant ) =>
        Cut(
          apply( q1, p.getLeftOccConnector parent ( info, ( Seq(), p.cutFormula, true ) ), subst ), a1,
          apply( q2, p.getRightOccConnector parent ( info, ( Seq(), p.cutFormula, true ) ), subst ), a2
        )

      // cut-ancestors
      case p @ WeakQuantifierRule( q, a, _, term, bound, pol ) if info( p.mainIndices.head )._3 =>
        val main = p.mainFormulas.head
        val ( w, f, true ) = destruct( p, info )
        val q_ = apply( q, p.occConnectors.head parent info updated ( a, ( w, instantiate( f, term ), true ) ), subst )
        if ( pol ) ExRight( q_, a.asInstanceOf[Suc], subf( main ), sub( term ) )
        else AllLeft( q_, a.asInstanceOf[Ant], subf( main ), sub( term ) )
      case p @ StrongQuantifierRule( q, a, eigen, quant, pol ) if info( p.mainIndices.head )._3 =>
        val ( w, f, true ) = destruct( p, info )
        val q_ = apply( q, p.occConnectors.head parent info updated ( a, ( w, q.conclusion( a ), true ) ), subst )
        if ( pol ) AllRight( q_, a.asInstanceOf[Suc], subf( p.mainFormulas.head ), eigen )
        else ExLeft( q_, a.asInstanceOf[Ant], subf( p.mainFormulas.head ), eigen )

      // end-sequent ancestors
      case p @ WeakQuantifierRule( q, a, _, term, bound, pol ) if !info( p.mainIndices.head )._3 =>
        val main = p.mainFormulas.head
        val ( w, f, false ) = destruct( p, info )
        val freshVar = varNameGen fresh bound
        val q_ = apply( q, p.occConnectors.head parent info updated ( a, ( w :+ ( freshVar, term ), instantiate( f, freshVar ), false ) ), subst + ( freshVar -> term ) )
        if ( pol ) ExSkRight( q_, a.asInstanceOf[Suc], subf( main ), sub( term ) )
        else AllSkLeft( q_, a.asInstanceOf[Ant], subf( main ), sub( term ) )
      case p @ StrongQuantifierRule( q, a, eigen, quant, pol ) if !info( p.mainIndices.head )._3 =>
        val main = p.mainFormulas.head
        val ( w, f, false ) = destruct( p, info )
        val skolemDef0 = Abs( w.map { _._1 }, Substitution( subst -- w.map { _._1 } )( f ) )
        val addVars = freeVariables( skolemDef0 ).toSeq
        val skolemDef = Abs( addVars, skolemDef0 )
        val skolemConst0 = skolemDefs.getOrElseUpdate(
          skolemDef,
          Const( nameGen freshWithIndex "s", FunctionType( eigen.exptype, addVars.map { _.exptype } ++ w.map { _._1.exptype } ) )
        )
        val skolemConst = skolemConst0( addVars: _* )
        val skolemTerm = skolemConst( w.map { _._1 }: _* )
        val q_ = apply( q, p.occConnectors.head parent info updated ( a, ( w, instantiate( f, skolemTerm ), false ) ), subst + ( eigen -> skolemTerm ) )
        if ( pol ) AllSkRight( q_, a.asInstanceOf[Suc], subf( main ), skolemConst, skolemDef )
        else ExSkLeft( q_, a.asInstanceOf[Ant], subf( main ), skolemConst, skolemDef )
    }
  }

  private def destruct( p: LKProof, info: Sequent[Info] ): Info = info( p.mainIndices.head ) match {
    case ( weak, HOLAtom( _, _ ), isCutAnc ) =>
      ( weak, p.mainFormulas.head, isCutAnc )
    case ( weak, generalized, isCutAnc ) =>
      ( weak, generalized, isCutAnc )
  }
}

object LKToLKsk2 {
  def apply( p: LKProof ): LKskProof = {
    val p_ = regularize( p )
    val conv = new LKToLKsk2( constants( p_.subProofs.flatMap { _.conclusion.elements } ), variables( p ) )
    val psk = conv( p_, p_.endSequent map { f => ( Seq(), f, false ) }, Map() )
    psk
  }
}
