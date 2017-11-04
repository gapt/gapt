package at.logic.gapt.provers.viper.grammars2

import at.logic.gapt.expr._
import at.logic.gapt.grammars.induction2.InductionGrammar
import at.logic.gapt.grammars.induction2.InductionGrammar.Production
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.expansion.InstanceTermEncoding

case class InductionBUP( g: InductionGrammar, enc: InstanceTermEncoding, goal: Formula ) {
  val X = rename( Var( "X", FunctionType( To, Seq( g.alpha.ty, g.indTy ) ++ g.gamma.map( _.ty ) ) ), containedNames( g ) )

  trait BupSequent {
    def theoryFormulas: HOLSequent
    def gammas: Vector[List[Expr]]
    def sequent: HOLSequent
    def formula: Formula
  }

  case class IndCase( constructor: Const, theoryFormulas: HOLSequent, gammas: Vector[List[Expr]] ) extends BupSequent {
    val nu = g.nus( constructor )

    val indHyps: Vector[Formula] =
      for ( gam <- gammas; nui <- nu if nui.ty == g.indTy )
        yield X( g.alpha, nui )( gam: _* ).asInstanceOf[Formula]

    val indConcl: Formula = X( g.alpha, constructor( nu ) )( g.gamma: _* ).asInstanceOf[Formula]

    val sequent: HOLSequent = indHyps ++: theoryFormulas :+ indConcl

    val formula: Formula = All.Block( g.alpha +: nu ++: g.gamma, sequent.toImplication )
  }

  case class EndCut( theoryFormulas: HOLSequent, gammas: Vector[List[Expr]] ) extends BupSequent {
    val indFormulaInstances: Vector[Formula] =
      for ( gam <- gammas )
        yield X( g.alpha, g.alpha )( gam: _* ).asInstanceOf[Formula]

    val sequent: HOLSequent = indFormulaInstances ++: theoryFormulas :+ goal

    val formula: Formula = All( g.alpha, sequent.toImplication )
  }

  val indCases: Vector[IndCase] =
    g.nus.keys.toVector.map { c =>
      val prods = g.productions.filter( p => g.correspondingCase( p ).forall( _ == c ) )
      val tauProds = prods.collect { case Production( List( tau ), List( rhs ) ) if tau == g.tau => rhs }
      val gammaProds0 = prods.collect { case Production( gamma, rhs ) if gamma == g.gamma => rhs }
      val gammaProds = if ( gammaProds0.isEmpty ) Vector( g.gamma ) else gammaProds0
      IndCase( c, enc.decodeToInstanceSequent( tauProds ), gammaProds )
    }

  val endCut: EndCut = {
    val prods = g.productions.filter( p => freeVariables( p.rhs ).subsetOf( Set( g.alpha ) ) )
    val tauProds = prods.collect { case Production( List( tau ), List( rhs ) ) if tau == g.tau => rhs }
    val gammaProds0 = prods.collect { case Production( gamma, rhs ) if gamma == g.gamma => rhs }
    val gammaProds = if ( gammaProds0.isEmpty ) Vector( g.gamma ) else gammaProds0
    EndCut( enc.decodeToInstanceSequent( tauProds ), gammaProds )
  }

  val bupSequents: Vector[BupSequent] = indCases :+ endCut

  val sequents: Vector[HOLSequent] = bupSequents.map( _.sequent )

  val formula: Formula = Ex( X, And( bupSequents.map( _.formula ) ) )
}
