package at.logic.gapt.provers.viper.grammars2

import at.logic.gapt.expr._
import at.logic.gapt.grammars.induction2.InductionGrammar
import at.logic.gapt.grammars.induction2.InductionGrammar.Production
import at.logic.gapt.proofs.expansion.InstanceTermEncoding

object inductionBUP {
  def apply( g: InductionGrammar, enc: InstanceTermEncoding, goal: Formula ): Formula = {
    val nameGen = rename.awayFrom( containedNames( g ) )
    val X = Var( nameGen.fresh( "X" ), FunctionType( To, Seq( g.alpha.ty, g.indTy ) ++ g.gamma.map( _.ty ) ) )
    Ex( X, And(
      g.nus.toVector.map {
        case ( c, nu ) =>
          val prods = g.productions.filter( p => g.correspondingCase( p ).forall( _ == c ) )
          val tauProds = prods.collect { case Production( List( tau ), List( rhs ) ) if tau == g.tau => rhs }
          val gammaProds0 = prods.collect { case Production( gamma, rhs ) if gamma == g.gamma => rhs }
          val gammaProds = if ( gammaProds0.isEmpty ) Vector( g.gamma ) else gammaProds0
          All.Block(
            g.alpha +: nu ++: g.gamma,
            ( And( tauProds.map( enc.decodeToSignedFormula ) ) &
              And( for ( gam <- gammaProds; nui <- nu if nui.ty == g.indTy )
                yield X( g.alpha, nui )( gam: _* ) ) ) -->
              X( g.alpha, c( nu ) )( g.gamma: _* ) )
      } :+ {
        val prods = g.productions.filter( p => freeVariables( p.rhs ).subsetOf( Set( g.alpha ) ) )
        val tauProds = prods.collect { case Production( List( tau ), List( rhs ) ) if tau == g.tau => rhs }
        val gammaProds0 = prods.collect { case Production( gamma, rhs ) if gamma == g.gamma => rhs }
        val gammaProds = if ( gammaProds0.isEmpty ) Vector( g.gamma ) else gammaProds0
        All(
          g.alpha,
          ( And( tauProds.map( enc.decodeToSignedFormula ) ) &
            And( gammaProds.map( gam => X( g.alpha, g.alpha )( gam: _* ) ) ) ) --> goal )
      } ) )
  }
}
