package at.logic.gapt.grammars

import at.logic.gapt.expr._
import at.logic.gapt.language.fol.FOLSubstitution
import at.logic.gapt.language.fol.Utils.numeral
import at.logic.gapt.provers.maxsat.{MaxSATSolver, MaxSat4j}

object SipGrammar {
  type Production = ( FOLVar, FOLTerm )

  val tau = FOLVar( "τ" )
  val beta = FOLVar( "β" )
  val gamma = FOLVar( "γ" )
  val gammaEnd = FOLVar( "γ_end" )

  val alpha = FOLVar( "α" )
  val nu = FOLVar( "ν" )

  def gamma_i( i: Int ) = FOLVar( s"γ_$i" )

  def instantiate( prod: Production, n: Int ): Seq[Production] = prod match {
    case ( `tau`, r ) =>
      var instanceProductions = Seq[Production]()
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
    }
    case ( `gammaEnd`, r ) => Seq( gamma_i( n ) -> FOLSubstitution( alpha -> numeral( n ) )( r ) )
  }
}

case class SipGrammar( productions: Seq[SipGrammar.Production] ) {
  import SipGrammar._

  override def toString = s"{${productions map { case ( d, t ) => s"$d -> $t" } mkString ", "}}"

  def instanceGrammar( n: Int ) =
    TratGrammar( tau, tau +: ( 0 until n ).inclusive.map( gamma_i ),
      productions flatMap { p => instantiate( p, n ) } distinct )
}

object normalFormsSipGrammar {
  type InstanceLanguage = ( Int, Seq[FOLTerm] )

  // TODO: better convention
  private def isFormulaSymbol( sym: String ) = sym.startsWith( "tuple" )

  def apply( instanceLanguages: Seq[InstanceLanguage] ) = {
    import SipGrammar._
    val nfs = tratNormalForms( instanceLanguages flatMap ( _._2 ), Seq( gamma, alpha, nu ) )

    val prods = Set.newBuilder[Production]

    for ( nf <- nfs ) {
      val fv = freeVariables( nf )

      nf match {
        case FOLFunction( f, _ ) if isFormulaSymbol( f ) =>
          if ( !fv.contains( nu ) ) prods += tau -> FOLSubstitution( gamma -> beta )( nf )
          prods += tau -> nf

        case _ =>
          prods += gamma -> nf
          if ( !fv.contains( nu ) && !fv.contains( gamma ) ) prods += gammaEnd -> nf
      }
    }

    SipGrammar( prods.result.toSeq )
  }
}

object atoms {
  def apply( f: FOLFormula ): Set[FOLFormula] = f match {
    case FOLAtom( _ )     => Set( f )
    case And( x, y )      => apply( x ) union apply( y )
    case Or( x, y )       => apply( x ) union apply( y )
    case Imp( x, y )      => apply( x ) union apply( y )
    case Neg( x )         => apply( x )
    case Top() | Bottom() => Set()
    case Ex( x, y )       => apply( y )
    case All( x, y )      => apply( y )
  }
}

// TODO: only supports one instance language at the moment
case class SipGrammarMinimizationFormula( g: SipGrammar ) {
  def productionIsIncluded( p: SipGrammar.Production ) = FOLAtom( s"sp,$p" )

  def coversLanguageFamily( langs: Seq[normalFormsSipGrammar.InstanceLanguage] ) = {
    val cs = Seq.newBuilder[FOLFormula]
    langs foreach {
      case ( n, lang ) =>
        val tratMinForm = new GrammarMinimizationFormula( g.instanceGrammar( n ) ) {
          override def productionIsIncluded( p: TratGrammar.Production ) = FOLAtom( s"p,$n,$p" )
          override def valueOfNonTerminal( t: FOLTerm, a: FOLVar, rest: FOLTerm ) = FOLAtom( s"v,$n,$t,$a=$rest" )
        }
        val instanceCovForm = tratMinForm.coversLanguage( lang )
        cs += instanceCovForm

        val atomsInInstForm = atoms( instanceCovForm )

        ( for ( p <- g.productions; instP <- SipGrammar.instantiate( p, n ) )
          yield instP -> p ).groupBy( _._1 ).values foreach { l =>
          val tratProdInc = tratMinForm.productionIsIncluded( l.head._1 )
          if ( atomsInInstForm contains tratProdInc )
            cs += Imp( tratProdInc, Or( l map ( _._2 ) map productionIsIncluded toList ) )
        }
    }
    And( cs.result toList )
  }
}

object minimizeSipGrammar {
  def apply( g: SipGrammar, langs: Seq[normalFormsSipGrammar.InstanceLanguage], maxSATSolver: MaxSATSolver = new MaxSat4j ): SipGrammar = {
    val formula = SipGrammarMinimizationFormula( g )
    val hard = formula.coversLanguageFamily( langs )
    val atomsInHard = atoms( hard )
    val soft = g.productions map formula.productionIsIncluded filter atomsInHard.contains map ( Neg( _ ) -> 1 )
    maxSATSolver.solveWPM( List( hard ), soft toList ) match {
      case Some( interp ) => SipGrammar(
        g.productions filter { p => interp.interpret( formula.productionIsIncluded( p ) ) } )
      case None => throw new Exception( "Grammar does not cover language." )
    }
  }
}

object findMinimalSipGrammar {
  def apply( langs: Seq[normalFormsSipGrammar.InstanceLanguage], maxSATSolver: MaxSATSolver = new MaxSat4j ) = {
    val polynomialSizedCoveringGrammar = normalFormsSipGrammar( langs )
    minimizeSipGrammar( polynomialSizedCoveringGrammar, langs, maxSATSolver )
  }
}
