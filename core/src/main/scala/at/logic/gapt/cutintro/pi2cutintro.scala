package at.logic.gapt.cutintro

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.lcomp
import at.logic.gapt.grammars.{ Pi2Grammar, findMinimalPi2Grammar }
import at.logic.gapt.proofs.expansion.InstanceTermEncoding
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.provers.maxsat.{ MaxSATSolver, bestAvailableMaxSatSolver }
import at.logic.gapt.utils.Logger

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
    findMinimalPi2Grammar( lang, alpha, betas, solver ).flatMap { grammar =>
      info( s"Found grammar of size: ${grammar.size}\n$grammar" )
      metric( "grammarsize", grammar.size )
      metric( "alpha_prods", grammar.productions.count( _._1 == grammar.alpha ) )
      metric( "pi1_grammarsize", grammar.tratg.size )
      metric( "genlangsize", grammar.language.size )
      val sehs = pi2GrammarToSEHS( grammar, enc )
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