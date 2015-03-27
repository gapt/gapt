package at.logic.algorithms.cutIntroduction

import at.logic.language.fol.Utils.numeral
import at.logic.language.fol._
import at.logic.language.lambda.symbols.SymbolA
import at.logic.provers.maxsat.MaxSATSolver.MaxSATSolver
import at.logic.provers.maxsat.{ MaxSATSolver, MaxSAT }

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
  import SipGrammar._

  override def toString = s"{${productions map { case ( d, t ) => s"$d -> $t" } mkString ", "}}"

  def instanceGrammar( n: Int ) = {
    TratGrammar( tau, productions flatMap { p => instantiate( p, n ) } distinct )
  }
}

object normalFormsSipGrammar {
  type InstanceLanguage = ( Int, Seq[FOLTerm] )

  // TODO: better convention
  private def isFormulaSymbol( sym: SymbolA ) = sym.toString.startsWith( "tuple" )

  def apply( instanceLanguages: Seq[InstanceLanguage] ) = {
    import SipGrammar._
    val nfs = tratNormalForms( instanceLanguages flatMap ( _._2 ), Seq( gamma, alpha, nu ) )

    val prods = Seq.newBuilder[Production]

    for ( nf <- nfs ) {
      val fv = freeVariables( nf )

      nf match {
        case FunctionOrConstant( f, _ ) if isFormulaSymbol( f ) =>
          if ( !fv.contains( nu ) ) prods += tau -> Substitution( gamma -> beta )( nf )
          prods += tau -> nf

        case _ =>
          prods += gamma -> nf
          if ( !fv.contains( nu ) && !fv.contains( gamma ) ) prods += gammaEnd -> nf
      }
    }

    SipGrammar( prods result )
  }
}

object atoms {
  def apply( f: FOLFormula ): Set[FOLFormula] = f match {
    case Atom( _ )      => Set( f )
    case And( x, y )    => apply( x ) union apply( y )
    case Or( x, y )     => apply( x ) union apply( y )
    case Imp( x, y )    => apply( x ) union apply( y )
    case Neg( x )       => apply( x )
    case TopC | BottomC => Set()
    case ExVar( x, y )  => apply( y )
    case AllVar( x, y ) => apply( y )
  }
}

// TODO: only supports one instance language at the moment
case class SipGrammarMinimizationFormula( g: SipGrammar ) {
  def productionIsIncluded( p: SipGrammar.Production ) = Atom( s"sp,$p" )

  def coversLanguageFamily( langs: Seq[normalFormsSipGrammar.InstanceLanguage] ) = {
    val cs = Seq.newBuilder[FOLFormula]
    langs foreach {
      case ( n, lang ) =>
        val tratMinForm = GrammarMinimizationFormula( g.instanceGrammar( n ) )
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
  def apply( g: SipGrammar, langs: Seq[normalFormsSipGrammar.InstanceLanguage], maxSATSolver: MaxSATSolver = MaxSATSolver.ToySAT ): SipGrammar = {
    val formula = SipGrammarMinimizationFormula( g )
    val hard = formula.coversLanguageFamily( langs )
    val atomsInHard = atoms( hard )
    val soft = g.productions map formula.productionIsIncluded filter atomsInHard.contains map ( Neg( _ ) -> 1 )
    new MaxSAT( maxSATSolver ).solvePWM( List( hard ), soft toList ) match {
      case Some( interp ) => SipGrammar(
        g.productions filter { p => interp.interpretAtom( formula.productionIsIncluded( p ) ) } )
      case None => throw new TreeGrammarDecompositionException( "Grammar does not cover language." )
    }
  }
}

object findMinimalSipGrammar {
  def apply( langs: Seq[normalFormsSipGrammar.InstanceLanguage] ) = {
    val polynomialSizedCoveringGrammar = normalFormsSipGrammar( langs )
    minimizeSipGrammar( polynomialSizedCoveringGrammar, langs )
  }
}
