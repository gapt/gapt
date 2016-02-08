package at.logic.gapt.examples.poset

import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.cutintro.{ beautifySolution, GrammarFindingMethod, CutIntroduction }
import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.grammars.VectTratGrammar
import at.logic.gapt.grammars.deltatable.{ DeltaTableMethodNew, deltaTable }
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk.{ LKToExpansionProof, extractRecSchem }
import at.logic.gapt.provers.eprover.EProver
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.sat.Sat4j

object dtable extends Script {

  val constructedProof = eliminateCutsET( LKToExpansionProof( proof.cycleImpliesEqual4 ) )
  //  println( extractRecSchem( proof.cycleImpliesEqual4 ) )
  //  InstanceTermEncoding( proof.cycleImpliesEqual4 )._1.toSeq sortBy { _.toString } foreach println

  if ( false ) {
    val removeEq = Map[LambdaExpression, LambdaExpression]( EqC( Ti ) -> FOLAtomConst( "E", 2 ) )
    val automaticProof = replaceET(
      Prover9.getExpansionProof( proof.cycleImpliesEqual4.endSequent map { TermReplacement( _, removeEq ) } ).get,
      removeEq.map( _.swap )
    )
    val Some( autoMin ) = minimalExpansionSequent( automaticProof, Sat4j )
  }

  CutIntroduction.compressToLK( constructedProof, hasEquality = false,
    method = DeltaTableMethodNew( singleQuantifier = false, tableSubsumption = true, Some( 3 ) ),
    verbose = true )

}
