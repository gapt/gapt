package at.logic.gapt.cutintro

import at.logic.gapt.expr._
import at.logic.gapt.grammars.{ Pi2Grammar, findMinimalPi2Grammar }
import at.logic.gapt.proofs.expansion.InstanceTermEncoding
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.provers.maxsat.{ MaxSATSolver, bestAvailableMaxSatSolver }

object pi2GrammarToSEHS {
  def apply( g: Pi2Grammar, encoding: InstanceTermEncoding ): Pi2SeHs = {
    Pi2SeHs(
      reducedRepresentation =
        encoding.decodeToInstanceSequent( g.productions.filter( _._1 == g.startSymbol ).map( _._2 ) ),
      universalEigenvariable = g.alpha,
      existentialEigenvariables = g.betas.reverse.toList,
      substitutionsForAlpha = g.betas.reverse.map( beta => g.productions.find( _._1 == beta ).get._2 ).toList,
      substitutionsForBetaWithAlpha = g.productions.filter( _._1 == g.alpha ).map( _._2 ).toList
    )
  }
}

object Pi2CutIntroduction {
  def apply( p: CutIntroduction.InputProof, alpha: Var, betas: Vector[Var],
             solver: MaxSATSolver = bestAvailableMaxSatSolver ): Option[LKProof] = {
    val exp = p.expansionProof
    val ( lang, enc ) = InstanceTermEncoding( exp )
    findMinimalPi2Grammar( lang, alpha, betas, solver ).flatMap { grammar =>
      val sehs = pi2GrammarToSEHS( grammar, enc )
      val ( cutFormulaOpt, x, y ) = introducePi2Cut( sehs )
      cutFormulaOpt.flatMap { cutFormula =>
        proveWithPi2Cut.giveProof( cutFormula, sehs, exp.shallow, x, y )
      }
    }
  }
}