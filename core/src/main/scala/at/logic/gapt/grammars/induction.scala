package at.logic.gapt.grammars

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.folSubTerms
import at.logic.gapt.expr.fol.Utils.numeral
import at.logic.gapt.expr.hol.{ atoms, lcomp, simplify, toNNF }
import at.logic.gapt.provers.maxsat.{ MaxSATSolver, bestAvailableMaxSatSolver }
import at.logic.gapt.utils.Logger

object SipGrammar {
  type Production = ( FOLVar, FOLTerm )

  val tau = FOLVar( "τ" )
  val beta = FOLVar( "β" )
  val gamma = FOLVar( "γ" )
  val gammaEnd = FOLVar( "γ_end" )

  val alpha = FOLVar( "α" )
  val nu = FOLVar( "ν" )

  def gamma_i( i: Int ) = FOLVar( s"γ_$i" )

  def instantiate( prod: Production, n: Int ): Set[VTRATG.Production] = ( prod match {
    case ( `tau`, r ) =>
      var instanceProductions = Set[Production]()
      if ( !freeVariables( r ).contains( gamma ) )
        instanceProductions ++= Seq( tau ->
          FOLSubstitution( alpha -> numeral( n ), nu -> numeral( 0 ), beta -> gamma_i( 0 ) )( r ) )
      if ( !freeVariables( r ).contains( beta ) )
        instanceProductions ++= ( 0 until n ) map { i =>
          tau ->
            FOLSubstitution( alpha -> numeral( n ), nu -> numeral( i ), gamma -> gamma_i( i + 1 ) )( r )
        }
      instanceProductions
    case ( `gamma`, r ) => ( 0 until n ) map { i =>
      gamma_i( i ) -> FOLSubstitution( alpha -> numeral( n ), nu -> numeral( i ), gamma -> gamma_i( i + 1 ) )( r )
    } toSet
    case ( `gammaEnd`, r ) => Set( gamma_i( n ) -> FOLSubstitution( alpha -> numeral( n ) )( r ) )
  } ).map { case ( l, r ) => List( l ) -> List( r ) }
}

case class SipGrammar( productions: Set[SipGrammar.Production] ) {
  import SipGrammar._

  override def toString: String = productions.map { case ( a, t ) => s"$a -> $t" }.toSeq.sorted.mkString( sys.props( "line.separator" ) )

  def instanceGrammar( n: Int ) =
    VTRATG( tau, List( tau ) +: ( 0 until n ).inclusive.map( gamma_i ).map( List( _ ) ),
      productions flatMap { p => instantiate( p, n ) } )
}

object stableSipGrammar {
  type InstanceLanguage = ( Int, Set[FOLTerm] )

  def apply( instanceLanguages: Seq[InstanceLanguage] ) = {
    import SipGrammar._

    val allTerms = instanceLanguages.flatMap( _._2 )
    val topLevelStableTerms = stableTerms( allTerms, Seq( gamma, alpha, nu ) ).filter( !_.isInstanceOf[FOLVar] )
    val argumentStableTerms = stableTerms(
      folSubTerms( allTerms flatMap { case FOLFunction( _, as ) => as } ),
      Seq( gamma, alpha, nu )
    )

    val prods = Set.newBuilder[Production]

    for ( st <- topLevelStableTerms ) {
      val fv = freeVariables( st )

      if ( !fv.contains( nu ) ) prods += tau -> FOLSubstitution( gamma -> beta )( st )
      prods += tau -> st
    }

    for ( st <- argumentStableTerms ) {
      val fv = freeVariables( st )

      prods += gamma -> st
      if ( !fv.contains( nu ) && !fv.contains( gamma ) ) prods += gammaEnd -> st
    }

    SipGrammar( prods.result )
  }
}

case class SipGrammarMinimizationFormula( g: SipGrammar ) {
  def productionIsIncluded( p: SipGrammar.Production ) = FOLAtom( s"sp,$p" )

  def coversLanguageFamily( langs: Seq[stableSipGrammar.InstanceLanguage] ) = {
    val cs = Seq.newBuilder[Formula]
    langs foreach {
      case ( n, lang ) =>
        val tratMinForm = new VectGrammarMinimizationFormula( g.instanceGrammar( n ) ) {
          override def productionIsIncluded( p: VTRATG.Production ) = FOLAtom( s"p,$n,$p" )
          override def valueOfNonTerminal( t: Expr, a: Var, rest: Expr ) = FOLAtom( s"v,$n,$t,$a=$rest" )
        }
        val instanceCovForm = tratMinForm.coversLanguage( lang )
        cs += instanceCovForm

        val atomsInInstForm = atoms( instanceCovForm )

        ( for ( p <- g.productions; instP <- SipGrammar.instantiate( p, n ) )
          yield instP -> p ).groupBy( _._1 ).values foreach { l =>
          val tratProdInc = tratMinForm.productionIsIncluded( l.head._1 )
          if ( atomsInInstForm contains tratProdInc )
            cs += Imp( tratProdInc, Or( l map ( _._2 ) map productionIsIncluded ) )
        }
    }
    And( cs.result )
  }
}

object minimizeSipGrammar extends Logger {
  def apply( g: SipGrammar, langs: Seq[stableSipGrammar.InstanceLanguage], maxSATSolver: MaxSATSolver = bestAvailableMaxSatSolver ): SipGrammar = {
    val formula = SipGrammarMinimizationFormula( g )
    val hard = formula.coversLanguageFamily( langs )
    debug( s"Logical complexity of the minimization formula: ${lcomp( simplify( toNNF( hard ) ) )}" )
    val atomsInHard = atoms( hard )
    val soft = g.productions map formula.productionIsIncluded filter atomsInHard.contains map ( Neg( _ ) -> 1 )
    maxSATSolver.solve( hard, soft ) match {
      case Some( interp ) => SipGrammar(
        g.productions filter { p => interp.interpret( formula.productionIsIncluded( p ) ) }
      )
      case None => throw new Exception( "Grammar does not cover language." )
    }
  }
}

object findMinimalSipGrammar {
  def apply( langs: Seq[stableSipGrammar.InstanceLanguage], maxSATSolver: MaxSATSolver = bestAvailableMaxSatSolver ) = {
    val polynomialSizedCoveringGrammar = stableSipGrammar( langs )
    minimizeSipGrammar( polynomialSizedCoveringGrammar, langs, maxSATSolver )
  }
}
