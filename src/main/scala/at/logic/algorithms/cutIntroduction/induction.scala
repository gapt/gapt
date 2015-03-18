package at.logic.algorithms.cutIntroduction

import at.logic.language.fol.Utils.numeral
import at.logic.language.fol._

object SipGrammar {
  type Production = ( FOLVar, FOLTerm )

  def tau = FOLVar( "τ" )
  def beta = FOLVar( "β" )
  def gamma = FOLVar( "γ" )
  def gammaEnd = FOLVar( "γ_end" )

  def alpha = FOLVar( "α" )
  def nu = FOLVar( "ν" )

  def gamma_i( i: Int ) = FOLVar( s"γ_$i" )

  def instantiate( prod: Production, n: Int ): Seq[Production] = prod match {
    case ( `tau`, r ) if freeVariables( r ).contains( beta ) =>
      Seq( tau -> Substitution( alpha -> numeral( n ), beta -> gamma_i( 0 ) )( r ) )
    case ( `tau`, r ) => ( 0 until n ) map { i =>
      tau ->
        Substitution( alpha -> numeral( n ), nu -> numeral( i ), gamma -> gamma_i( i + 1 ) )( r )
    }
    case ( `gamma`, r ) => ( 0 until n ) map { i =>
      gamma_i( i ) -> Substitution( alpha -> numeral( n ), nu -> numeral( i ), gamma -> gamma_i( i + 1 ) )( r )
    }
    case ( `gammaEnd`, r ) => Seq( gamma_i( n ) -> Substitution( alpha -> numeral( n ) )( r ) )
  }
}

case class SipGrammar( productions: Seq[SipGrammar.Production] ) {
  override def toString = s"{${productions map { case ( d, t ) => s"$d -> $t" } mkString ", "}}"
}

object normalFormsSipGrammar {
  type InstanceLanguage = ( Int, Seq[FOLTerm] )

  // TODO: make sure we don't have productions of the form τ -> f(...) or γ -> r_i(...)

  def apply( instanceLanguages: Seq[InstanceLanguage] ) = {
    import SipGrammar._
    val nfs = normalForms( instanceLanguages flatMap ( _._2 ), Seq( gamma, alpha, nu ) )

    val prods = Seq.newBuilder[Production]

    for ( nf <- nfs ) {
      val fv = freeVariables( nf )

      if ( !fv.contains( nu ) ) prods += tau -> Substitution( gamma -> beta )( nf )
      prods += tau -> nf
      prods += gamma -> nf
      if ( !fv.contains( nu ) && !fv.contains( gamma ) ) prods += gammaEnd -> nf
    }

    SipGrammar( prods result )
  }
}
