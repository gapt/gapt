package gapt.cutintro

import gapt.expr._
import gapt.expr.hol.lcomp
import gapt.grammars.{ Pi2Grammar, VtratgParameter, findMinimalPi2Grammar, findMinimalVTRATG }
import gapt.proofs.Sequent
import gapt.proofs.expansion.InstanceTermEncoding
import gapt.proofs.lk.LKProof
import gapt.provers.maxsat.{ MaxSATSolver, bestAvailableMaxSatSolver }
import gapt.utils.Logger

object pi2GrammarToSEHS {
  def apply( g: Pi2Grammar, encoding: InstanceTermEncoding ): Pi2SeHs = {
    Pi2SeHs(
      reducedRepresentation =
        encoding.decodeToInstanceSequent( g.productions.filter( _._1 == g.startSymbol ).map( _._2 ) ),
      universalEigenvariable = g.alpha,
      existentialEigenvariables = g.betas.reverse.toList,
      substitutionsForAlpha = g.betas.reverse.map( beta => g.productions.find( _._1 == beta ).get._2 ).toList,
      substitutionsForBetaWithAlpha = g.productions.filter( _._1 == g.alpha ).map( _._2 ).toList )
  }
}

object Pi2CutIntroduction {
  val logger = Logger( "Pi2CutIntro" )
  import logger._

  def apply( p: CutIntroduction.InputProof, alpha: Var, betas: Vector[Var],
             solver: MaxSATSolver = bestAvailableMaxSatSolver ): Option[LKProof] = {
    val exp = p.expansionProof
    val grounding = Substitution( freeVariables( exp.deep ).map( v => v -> Const( v.name, v.ty ) ) )
    val ( lang, enc ) = InstanceTermEncoding( grounding( exp ) )
    info( s"Language size: ${lang.size}" )
    metric( "lang_trivial", lang.size == lang.map { case Apps( r, _ ) => r }.size )
    metric( "langsize", lang.size )
    println( "start computing grammar" )

    if ( betas == Vector() ) {
      val grammar = findMinimalVTRATG( lang, VtratgParameter.forFolTratg( 1 ) )
      val sehs = Pi2SeHs(
        Sequent( Seq(), grammar.rightHandSides( grammar.startSymbolNT ).head.map( x => {
          println( x )
          x.asInstanceOf[Formula]
        } ) ),
        alpha, List( fov"beta" ),
        grammar.productions.unzip._2.tail.head,
        List( fot"dummyTermGottIstTot" ) )
      println( "start computing cut formula" )
      val ( cutFormulaOpt, x, y ) = introducePi2Cut( sehs )
      cutFormulaOpt.flatMap { cutFormula =>
        metric( "cutformula", cutFormula.toString )
        metric( "cutformula_lcomp", lcomp( cutFormula ) )
        info( s"Cut formula: $cutFormula" )
        proveWithPi2Cut.giveProof( cutFormula, sehs, exp.shallow, x, y )
      }.orElse {
        info( s"Could not find cut formula." )
        None
      }
    } else {
      findMinimalPi2Grammar( lang, alpha, betas, solver ).flatMap { grammar =>
        info( s"Found grammar of size: ${grammar.size}\n$grammar" )
        metric( "grammarsize", grammar.size )
        metric( "alpha_prods", grammar.productions.count( _._1 == grammar.alpha ) )
        metric( "pi1_grammarsize", grammar.tratg.size )
        metric( "genlangsize", grammar.language.size )
        val sehs = pi2GrammarToSEHS( grammar, enc )
        println( "start computing cut formula" )
        val ( cutFormulaOpt, x, y ) = introducePi2Cut( sehs )
        cutFormulaOpt.flatMap { cutFormula =>
          metric( "cutformula", cutFormula.toString )
          metric( "cutformula_lcomp", lcomp( cutFormula ) )
          info( s"Cut formula: $cutFormula" )
          proveWithPi2Cut.giveProof( cutFormula, sehs, exp.shallow, x, y )
        }.orElse {
          info( s"Could not find cut formula." )
          None
        }
      }
    }

  }
}