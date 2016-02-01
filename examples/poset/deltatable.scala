package at.logic.gapt.examples.poset

import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.cutintro.{ GrammarFindingMethod, CutIntroduction }
import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.grammars.VectTratGrammar
import at.logic.gapt.grammars.deltatable.deltaTable
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk.{ LKToExpansionProof, extractRecSchem }
import at.logic.gapt.provers.eprover.EProver
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.sat.Sat4j

object dtable extends Script {

  val constructedProof = eliminateCutsET( LKToExpansionProof( proof.cycleImpliesEqual4 ) )
  //  println(extractRecSchem(proof.cycleImpliesEqual4))

  if ( false ) {
    val removeEq = Map[LambdaExpression, LambdaExpression]( EqC( Ti ) -> FOLAtomConst( "E", 2 ) )
    val automaticProof = replaceET(
      Prover9.getExpansionProof( proof.cycleImpliesEqual4.endSequent map { TermReplacement( _, removeEq ) } ).get,
      removeEq.map( _.swap )
    )
    val Some( autoMin ) = minimalExpansionSequent( automaticProof, Sat4j )
  }

  CutIntroduction.compressToLK( constructedProof, hasEquality = false, method = new GrammarFindingMethod {
    def findGrammars( lang: Set[FOLTerm] ): Option[VectTratGrammar] = {
      val dtable = deltaTable.createTable( lang.toSet, Some( 3 ) )

      val ( us, s ) = deltaTable.findGrammarFromDeltaTable( lang.toSet, dtable )

      Some( deltaTable.grammarToVTRATG( us, s ) )
    }

    def name = "3_dtable"
  }, verbose = true )

}
