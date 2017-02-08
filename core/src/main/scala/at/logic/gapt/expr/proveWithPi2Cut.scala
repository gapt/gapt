package at.logic.gapt.expr

import at.logic.gapt.proofs.{Context, Sequent}
import at.logic.gapt.proofs.gaptic.Lemma
import at.logic.gapt.proofs.gaptic.tactics
import at.logic.gapt.proofs.gaptic.tactics.CutTactic
import at.logic.gapt.proofs.lk.LKProof

/**
 * Created by root on 08.02.17.
 */
object proveWithPi2Cut {

  def apply(
    endSequent:                Sequent[FOLFormula],
    seHs:                      Pi2SeHs,
    nameOfExistentialVariable: FOLVar              = fov"yCut",
    nameOfUniversalVariable:   FOLVar              = fov"xCut"
  ): ( Option[LKProof] ) = {

    val ( cutFormulaWithoutQuantifiers: Option[FOLFormula], nameOfExVa: FOLVar, nameOfUnVa: FOLVar ) = introducePi2Cut( seHs, nameOfExistentialVariable, nameOfUniversalVariable )

    cutFormulaWithoutQuantifiers match {
      case Some( t ) => giveProof( t, seHs, endSequent, nameOfExVa, nameOfUnVa )
      case None => {
        println( "No cut formula has been found." )
        None
      }
    }
  }

  private def giveProof(
    cutFormulaWithoutQuantifiers: FOLFormula,
    seHs:                         Pi2SeHs,
    endSequent:                   Sequent[FOLFormula],
    nameOfExVa:                   FOLVar,
    nameOfUnVa:                   FOLVar
  ): ( Option[LKProof] ) = {

    val listAnt:Seq[String] = (for {
      i <- 0 until endSequent.antecedent.size
    } yield i.toString)
    val listSuc:Seq[String] = (for {
      i <- endSequent.antecedent.size until endSequent.antecedent.size + endSequent.succedent.size
    } yield i.toString).toList

    var ctx = Context.default
    ctx += Context.Sort( "i" )

    val proof = Lemma(
      (listAnt.zip(endSequent.antecedent),listSuc.zip(endSequent.succedent)).asInstanceOf[Sequent[(String,FOLFormula)]]
    ) {
      CutTactic("Cut",hof"!$nameOfUnVa?$nameOfExVa$cutFormulaWithoutQuantifiers")
    }

    None
  }

}
