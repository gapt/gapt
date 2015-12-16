package at.logic.gapt.proofs.shlk

import at.logic.gapt.formats.shlk.{ backToInt, maketogether }
import at.logic.gapt.expr._
import at.logic.gapt.expr.schema.{ leq, lessThan, sims, _ }
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lkOld._
import at.logic.gapt.proofs.lkOld.base._
import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.proofs.shlk._

import scala.Predef._

object applySchemaSubstitution2 {
  def apply( proof_name: String, number: Int, ProofLinkPassing: List[Tuple2[SchemaExpression, SchemaExpression]] ): LKProof = {
    val aa = function001( proof_name, number, ProofLinkPassing )
    println( aa._1.toString() )
    //CloneLKProof2(aa._2,"",aa._1,0,0,List())._2
    aa._2
  }
  def function001( proof_name: String, number: Int, ProofLinkPassing: List[Tuple2[SchemaExpression, SchemaExpression]] ): Tuple2[List[Tuple2[SchemaFormula, SchemaFormula]], LKProof] =
    if ( number == 0 ) CloneLKProof2( SchemaProofDB.get( proof_name ).base, proof_name, List(), 0, 1, ProofLinkPassing ) else anotherfunction( proof_name: String, maketogether( number ), ProofLinkPassing )
  def anotherfunction( proof_name: String, number: SchemaExpression, ProofLinkPassing: List[Tuple2[SchemaExpression, SchemaExpression]] ): Tuple2[List[Tuple2[SchemaFormula, SchemaFormula]], LKProof] = {
    val k = backToInt( number )
    if ( k == 0 ) CloneLKProof2( SchemaProofDB.get( proof_name ).base, proof_name, List(), k, 1, ProofLinkPassing )
    else {
      val proofist = CloneLKProof2( SchemaProofDB.get( proof_name ).rec, proof_name, List(), k - 1, 2, ProofLinkPassing )
      CloneLKProof2( proofist._2, proof_name, List(), k - 1, 1, ProofLinkPassing )
    }
  }
}
object CloneLKProof2 {
  val nLine = sys.props( "line.separator" )
  def apply( proof: LKProof, name: String, rewriterules: List[Tuple2[SchemaFormula, SchemaFormula]], proofSize: Int, version: Int, ProofLinkPassing: List[Tuple2[SchemaExpression, SchemaExpression]] ): Tuple2[List[Tuple2[SchemaFormula, SchemaFormula]], LKProof] = {
    proof match {
      case trsArrowLeftRule( p, s, a, m )  => if ( version == 0 ) Tuple2( List(), proof ) else if ( version == 1 ) apply( p, name, rewriterules, proofSize, version, ProofLinkPassing ) else if ( version == 2 ) Tuple2( List(), proof ) else Tuple2( List(), proof )
      case trsArrowRightRule( p, s, a, m ) => if ( version == 0 ) Tuple2( List(), proof ) else if ( version == 1 ) apply( p, name, rewriterules, proofSize, version, ProofLinkPassing ) else if ( version == 2 ) Tuple2( List(), proof ) else Tuple2( List(), proof )
      case foldLeftRule( p, s, a, m ) => {
        if ( version == 0 ) apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
        else if ( version == 1 ) {
          val aa = iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing )
          val mm = iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing )
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1 :+ rewriterulereplace( mm, aa ), foldLeftRule( new_p._2, aa, mm ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, foldLeftRule( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }
      case foldRightRule( p, s, a, m ) => {
        if ( version == 0 ) apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
        else if ( version == 1 ) {
          val aa = iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing )
          val mm = iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing )
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1 :+ rewriterulereplace( mm, aa ), foldRightRule( new_p._2, aa, mm ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, foldRightRule( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }
      case foldRule( p, s, a, m ) => if ( version == 0 ) Tuple2( List(), proof ) else if ( version == 1 ) apply( p, name, rewriterules, proofSize, version, ProofLinkPassing ) else if ( version == 2 ) Tuple2( List(), proof ) else Tuple2( List(), proof )

      case Axiom( ro ) => {
        if ( version == 0 ) Tuple2( List(), Axiom( ro.antecedent.map( fo => defineremove( fo.formula.asInstanceOf[SchemaFormula], rewriterules ) ), ro.succedent.map( fo => defineremove( fo.formula.asInstanceOf[SchemaFormula], rewriterules ) ) ) )
        else if ( version == 1 ) Tuple2( List(), Axiom( ro.antecedent.map( fo => iterateOnFormula( fo.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ), ro.succedent.map( fo => iterateOnFormula( fo.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) ) )
        else if ( version == 2 ) {
          Tuple2( List(), Axiom( ro.antecedent.map( fo => cloneMySol( fo.formula.asInstanceOf[SchemaFormula], proofSize ) ), ro.succedent.map( fo => cloneMySol( fo.formula.asInstanceOf[SchemaFormula], proofSize ) ) ) )
        } else Tuple2( List(), proof )
      }

      case AndLeftEquivalenceRule1( p, s, a, m ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, AndLeftEquivalenceRule1( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, AndLeftEquivalenceRule1( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, AndLeftEquivalenceRule1( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }
      case AndRightEquivalenceRule1( p, s, a, m ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, AndRightEquivalenceRule1( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, AndRightEquivalenceRule1( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, AndRightEquivalenceRule1( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }

      case OrRightEquivalenceRule1( p, s, a, m ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, OrRightEquivalenceRule1( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, OrRightEquivalenceRule1( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, OrRightEquivalenceRule1( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }
      case AndLeftEquivalenceRule3( p, s, a, m ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, AndLeftEquivalenceRule3( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, AndLeftEquivalenceRule3( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, AndLeftEquivalenceRule3( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }
      case AndRightEquivalenceRule3( p, s, a, m ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, AndRightEquivalenceRule3( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, AndRightEquivalenceRule3( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, AndRightEquivalenceRule3( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }

      case OrRightEquivalenceRule3( p, s, a, m ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, OrRightEquivalenceRule3( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, OrRightEquivalenceRule3( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, OrRightEquivalenceRule3( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }

      case WeakeningLeftRule( p, _, m ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          implicit val factory = defaultFormulaOccurrenceFactory
          Tuple2( new_p._1, WeakeningLeftRule( new_p._2, defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          implicit val factory = defaultFormulaOccurrenceFactory
          Tuple2( new_p._1, WeakeningLeftRule( new_p._2, iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          implicit val factory = defaultFormulaOccurrenceFactory
          Tuple2( new_p._1, WeakeningLeftRule( new_p._2, cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }

      case WeakeningRightRule( p, _, m ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          implicit val factory = defaultFormulaOccurrenceFactory
          Tuple2( new_p._1, WeakeningRightRule( new_p._2, defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          implicit val factory = defaultFormulaOccurrenceFactory
          Tuple2( new_p._1, WeakeningRightRule( new_p._2, iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          implicit val factory = defaultFormulaOccurrenceFactory
          Tuple2( new_p._1, WeakeningRightRule( new_p._2, cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }

      case CutRule( p1, p2, _, a1, a2 ) => {
        if ( version == 0 ) {
          val new_p1 = apply( p1, name, rewriterules, proofSize, version, ProofLinkPassing )
          val new_p2 = apply( p2, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p1._1 ++ new_p2._1, CutRule( new_p1._2, new_p2._2, defineremove( a2.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p1 = apply( p1, name, rewriterules, proofSize, version, ProofLinkPassing )
          val new_p2 = apply( p2, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p1._1 ++ new_p2._1, CutRule( new_p1._2, new_p2._2, iterateOnFormula( a2.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p1 = apply( p1, name, rewriterules, proofSize, version, ProofLinkPassing )
          val new_p2 = apply( p2, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p1._1 ++ new_p2._1, CutRule( new_p1._2, new_p2._2, cloneMySol( a2.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }

      case OrLeftRule( p1, p2, _, a1, a2, m ) => {
        if ( version == 0 ) {
          val new_p1 = apply( p1, name, rewriterules, proofSize, version, ProofLinkPassing )
          val new_p2 = apply( p2, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p1._1 ++ new_p2._1, OrLeftRule( new_p1._2, new_p2._2, defineremove( a1.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( a2.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p1 = apply( p1, name, rewriterules, proofSize, version, ProofLinkPassing )
          val new_p2 = apply( p2, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p1._1 ++ new_p2._1, OrLeftRule( new_p1._2, new_p2._2, iterateOnFormula( a1.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( a2.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p1 = apply( p1, name, rewriterules, proofSize, version, ProofLinkPassing )
          val new_p2 = apply( p2, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p1._1 ++ new_p2._1, OrLeftRule( new_p1._2, new_p2._2, cloneMySol( a1.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( a2.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }

      case AndRightRule( p1, p2, _, a1, a2, m ) => {
        if ( version == 0 ) {
          val new_p1 = apply( p1, name, rewriterules, proofSize, version, ProofLinkPassing )
          val new_p2 = apply( p2, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p1._1 ++ new_p2._1, AndRightRule( new_p1._2, new_p2._2, defineremove( a1.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( a2.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p1 = apply( p1, name, rewriterules, proofSize, version, ProofLinkPassing )
          val new_p2 = apply( p2, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p1._1 ++ new_p2._1, AndRightRule( new_p1._2, new_p2._2, iterateOnFormula( a1.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( a2.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p1 = apply( p1, name, rewriterules, proofSize, version, ProofLinkPassing )
          val new_p2 = apply( p2, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p1._1 ++ new_p2._1, AndRightRule( new_p1._2, new_p2._2, cloneMySol( a1.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( a2.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }
      case ImpLeftRule( p1, p2, s, a1, a2, m ) => {
        if ( version == 0 ) {
          val new_p1 = apply( p1, name, rewriterules, proofSize, version, ProofLinkPassing )
          val new_p2 = apply( p2, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p1._1 ++ new_p2._1, ImpLeftRule( new_p1._2, new_p2._2, defineremove( a1.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( a2.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p1 = apply( p1, name, rewriterules, proofSize, version, ProofLinkPassing )
          val new_p2 = apply( p2, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p1._1 ++ new_p2._1, ImpLeftRule( new_p1._2, new_p2._2, iterateOnFormula( a1.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( a2.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p1 = apply( p1, name, rewriterules, proofSize, version, ProofLinkPassing )
          val new_p2 = apply( p2, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p1._1 ++ new_p2._1, ImpLeftRule( new_p1._2, new_p2._2, cloneMySol( a1.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( a2.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }

      case NegLeftRule( p, _, a, m ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, NegLeftRule( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, NegLeftRule( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, NegLeftRule( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }

      case AndLeft1Rule( p, r, a, m ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          val a2 = m.formula match { case And( l, right ) => right }
          Tuple2( new_p._1, AndLeft1Rule( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( a2.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          val a2 = m.formula match { case And( l, right ) => right }
          Tuple2( new_p._1, AndLeft1Rule( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( a2.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          val a2 = m.formula match { case And( l, right ) => right }
          Tuple2( new_p._1, AndLeft1Rule( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( a2.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }

      case AndLeft2Rule( p, r, a, m ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          val a2 = m.formula match { case And( l, _ ) => l }
          Tuple2( new_p._1, AndLeft2Rule( new_p._2, defineremove( a2.asInstanceOf[SchemaFormula], rewriterules ), defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          val a2 = m.formula match { case And( l, _ ) => l }
          Tuple2( new_p._1, AndLeft2Rule( new_p._2, iterateOnFormula( a2.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          val a2 = m.formula match { case And( l, _ ) => l }
          Tuple2( new_p._1, AndLeft2Rule( new_p._2, cloneMySol( a2.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }

      case OrRight1Rule( p, r, a, m ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          val a2 = m.formula match { case Or( _, ra ) => ra }
          Tuple2( new_p._1, OrRight1Rule( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( a2.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          val a2 = m.formula match { case Or( _, ra ) => ra }
          Tuple2( new_p._1, OrRight1Rule( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( a2.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          val a2 = m.formula match { case Or( _, ra ) => ra }
          Tuple2( new_p._1, OrRight1Rule( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( a2.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }

      case OrRight2Rule( p, r, a, m ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          val a2 = m.formula match { case Or( l, _ ) => l }
          Tuple2( new_p._1, OrRight2Rule( new_p._2, defineremove( a2.asInstanceOf[SchemaFormula], rewriterules ), defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          val a2 = m.formula match { case Or( l, _ ) => l }
          Tuple2( new_p._1, OrRight2Rule( new_p._2, iterateOnFormula( a2.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          val a2 = m.formula match { case Or( l, _ ) => l }
          Tuple2( new_p._1, OrRight2Rule( new_p._2, cloneMySol( a2.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }

      case NegRightRule( p, _, a, m ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, NegRightRule( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, NegRightRule( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, NegRightRule( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }

      case ContractionLeftRule( p, _, a1, a2, m ) => {

        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          println( "fdkjskjf  " + defineremove( a1.formula.asInstanceOf[SchemaFormula], rewriterules ) )
          println( "fdkjskjssdfdsf  " + new_p._2.root )
          Tuple2( new_p._1, ContractionLeftRule( new_p._2, defineremove( a1.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ContractionLeftRule( new_p._2, iterateOnFormula( a1.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ContractionLeftRule( new_p._2, cloneMySol( a1.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }

      case ContractionRightRule( p, _, a1, a2, m ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ContractionRightRule( new_p._2, defineremove( a1.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ContractionRightRule( new_p._2, iterateOnFormula( a1.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ContractionRightRule( new_p._2, cloneMySol( a1.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }
      // QUANTIFIER WILL NEED EXTRA WORK FOR TERM ->>
      case ForallLeftRule( p, seq, a, m, t ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          println( defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ).toString + "   " + defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ).toString )
          Tuple2( new_p._1, ForallLeftRule( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ), t ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ForallLeftRule( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( t.asInstanceOf[SchemaExpression], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ForallLeftRule( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMyTerm( t.asInstanceOf[SchemaExpression], proofSize ) ) )
        } else Tuple2( List(), proof )
      }
      case ForallRightRule( p, seq, a, m, v ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ForallRightRule( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ), v ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ForallRightRule( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( v.asInstanceOf[SchemaExpression], ProofLinkPassing ).asInstanceOf[Var] ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ForallRightRule( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMyTerm( v.asInstanceOf[SchemaExpression], proofSize ).asInstanceOf[Var] ) )
        } else Tuple2( List(), proof )
      }

      case ExistsRightRule( p, seq, a, m, t ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ExistsRightRule( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ), t ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ExistsRightRule( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( t.asInstanceOf[SchemaExpression], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ExistsRightRule( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMyTerm( t.asInstanceOf[SchemaExpression], proofSize ) ) )
        } else Tuple2( List(), proof )
      }
      case ExistsLeftRule( p, seq, a, m, v ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ExistsLeftRule( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ), v ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ExistsLeftRule( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( v.asInstanceOf[SchemaExpression], ProofLinkPassing ).asInstanceOf[Var] ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ExistsLeftRule( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMyTerm( v.asInstanceOf[SchemaExpression], proofSize ).asInstanceOf[Var] ) )
        } else Tuple2( List(), proof )
      }

      case ExistsHyperRightRule( p, seq, a, m, t ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ExistsHyperRightRule( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ), t.asInstanceOf[SchemaExpression] ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ExistsHyperRightRule( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( t.asInstanceOf[SchemaExpression], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ExistsHyperRightRule( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMyTerm( t.asInstanceOf[SchemaExpression], proofSize ) ) )
        } else Tuple2( List(), proof )
      }
      case ExistsHyperLeftRule( p, seq, a, m, v ) => {
        if ( version == 0 ) apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
        else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ExistsHyperLeftRule( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ), v.asInstanceOf[Var] ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ExistsHyperLeftRule( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMyTerm( v.asInstanceOf[SchemaExpression], proofSize ).asInstanceOf[Var] ) )
        } else Tuple2( List(), proof )
      }
      case ForallHyperLeftRule( p, seq, a, m, t ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ForallHyperLeftRule( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ), t.asInstanceOf[SchemaExpression] ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ForallHyperLeftRule( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( t.asInstanceOf[SchemaExpression], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ForallHyperLeftRule( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMyTerm( t.asInstanceOf[SchemaExpression], proofSize ) ) )
        } else Tuple2( List(), proof )
      }
      case ForallHyperRightRule( p, seq, a, m, v ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ForallHyperRightRule( new_p._2, defineremove( a.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( m.formula.asInstanceOf[SchemaFormula], rewriterules ), v.asInstanceOf[Var] ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ForallHyperRightRule( new_p._2, iterateOnFormula( a.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( m.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( v.asInstanceOf[SchemaExpression], ProofLinkPassing ).asInstanceOf[Var] ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ForallHyperRightRule( new_p._2, cloneMySol( a.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( m.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMyTerm( v.asInstanceOf[SchemaExpression], proofSize ).asInstanceOf[Var] ) )
        } else Tuple2( List(), proof )
      }

      case ImpRightRule( p, s, a1, a2, m ) => {
        if ( version == 0 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ImpRightRule( new_p._2, defineremove( a1.formula.asInstanceOf[SchemaFormula], rewriterules ), defineremove( a2.formula.asInstanceOf[SchemaFormula], rewriterules ) ) )
        } else if ( version == 1 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ImpRightRule( new_p._2, iterateOnFormula( a1.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ), iterateOnFormula( a2.formula.asInstanceOf[SchemaFormula], ProofLinkPassing ) ) )
        } else if ( version == 2 ) {
          val new_p = apply( p, name, rewriterules, proofSize, version, ProofLinkPassing )
          Tuple2( new_p._1, ImpRightRule( new_p._2, cloneMySol( a1.formula.asInstanceOf[SchemaFormula], proofSize ), cloneMySol( a2.formula.asInstanceOf[SchemaFormula], proofSize ) ) )
        } else Tuple2( List(), proof )
      }
      case FOSchemaProofLinkRule( s, name2, l ) => {
        if ( version == 0 ) Tuple2( List(), proof )

        else if ( version == 1 ) {
          val next = backToInt( l.head )
          val newList = l.tail.map( x => iterateOnFormula( x, ProofLinkPassing ) )
          if ( next == 0 ) {
            if ( SchemaProofDB.getLinkTerms( name2 ).length != 0 && SchemaProofDB.getLinkTerms( name2 ).length == newList.length ) {

              val ProofLinkPassingNew = SchemaProofDB.getLinkTerms( name2 ).zip( newList )
              CloneLKProof2( SchemaProofDB.get( name2 ).base, name2, rewriterules, 0, version, ProofLinkPassingNew )
            } else if ( SchemaProofDB.getLinkTerms( name2 ).length == 0 && SchemaProofDB.getLinkTerms( name2 ).length == newList.length )
              CloneLKProof2( SchemaProofDB.get( name2 ).base, name2, rewriterules, 0, version, List() )
            else throw new Exception( "ERROR ProofLinks are wrong !" + nLine )
          } else {
            if ( SchemaProofDB.getLinkTerms( name2 ).length != 0 && SchemaProofDB.getLinkTerms( name2 ).length == newList.length ) {
              val ProofLinkPassingNew = SchemaProofDB.getLinkTerms( name2 ).zip( newList )
              applySchemaSubstitution2.function001( name2, next, ProofLinkPassingNew )
            } else if ( SchemaProofDB.getLinkTerms( name2 ).length == 0 && SchemaProofDB.getLinkTerms( name2 ).length == newList.length )
              applySchemaSubstitution2.function001( name2, next, List() )
            else throw new Exception( "ERROR ProofLinks are wrong !" + nLine )
          }
        } else if ( version == 2 ) Tuple2( List(), FOSchemaProofLinkRule(
          new HOLSequent(
            s.antecedent.map( x => cloneMySol( x.formula.asInstanceOf[SchemaFormula], proofSize ) ),
            s.succedent.map( x => cloneMySol( x.formula.asInstanceOf[SchemaFormula], proofSize ) )
          ), name2, l.map( x => cloneMyTerm( x, proofSize ) )
        ) )
        else Tuple2( List(), proof )
      }
      case _ => throw new Exception( "ERROR in unfolding: CloneLKProof2: missing rule !" + nLine + proof.rule + nLine )
    }
  }
}

object defineremove { def apply( form: SchemaFormula, rewriterules: List[Tuple2[SchemaFormula, SchemaFormula]] ): SchemaFormula = rewriterules.foldLeft( Tuple2( true, form ) )( ( f, p ) => if ( AtomMatch( f._2, p._1 ) && f._1 ) Tuple2( false, cloneMySol( p._2, rewriterules ) ) else f )._2 }
object rewriterulereplace {
  def apply( p: Tuple2[SchemaFormula, SchemaFormula] ): Tuple2[SchemaFormula, SchemaFormula] = if ( AtomMatch( p._1 ) ) {
    val pairone: SchemaFormula = { p._1 match { case SchemaAtom( x, y ) => y case _ => List() } }.tail.foldLeft( Tuple2( 0, p._2 ) )( ( pairppair, t ) => ( pairppair._1 + 1, genterm( pairppair._1, pairppair._2, t ) ) )._2
    Tuple2( p._1 match {
      case SchemaAtom( x, y ) => SchemaAtom( x, List( y.head ) ++ y.tail.foldLeft( Tuple2( 0, List().asInstanceOf[List[SchemaExpression]] ) )( ( pair, t ) => ( pair._1 + 1, pair._2.asInstanceOf[List[SchemaExpression]] :+ Const( ( "!" + pair._1 + "!" ), Ti ) ) )._2 )
      case x                  => x
    }, pairone )
  } else p
}
object iterateOnFormula {
  def apply( form: SchemaFormula, ProofLinkPassing: List[Tuple2[SchemaExpression, SchemaExpression]] ): SchemaFormula = ProofLinkPassing.foldLeft( form )( ( f, pair ) => cloneMySol( f, pair._1, pair._2 ) )
  def apply( term: SchemaExpression, ProofLinkPassing: List[Tuple2[SchemaExpression, SchemaExpression]] ): SchemaExpression = ProofLinkPassing.foldLeft( term )( ( t, pair ) => { cloneMyTerm( t, pair._1, pair._2 ) } )
}
object genterm {
  val nLine = sys.props( "line.separator" )
  def apply( n: Int, p: SchemaFormula, t: SchemaExpression ): SchemaFormula = {
    p match {
      case Neg( nF ) => {
        val finForm = apply( n, nF, t )
        Neg( finForm )
      }
      case And( lF, rF ) => {
        val finFormL = apply( n, lF, t )
        val finFormR = apply( n, rF, t )
        And( finFormL, finFormR )
      }
      case Or( lF, rF ) => {
        val finFormL = apply( n, lF, t )
        val finFormR = apply( n, rF, t )
        Or( finFormL, finFormR )
      }
      case Imp( lF, rF ) => {
        val finFormL = apply( n, lF, t )
        val finFormR = apply( n, rF, t )
        Imp( finFormL, finFormR )
      }
      case All( aV, aF ) => {
        val finForm = apply( n, aF, t )
        All( aV, finForm )
      }
      case Ex( aV, aF ) => {
        val finForm = apply( n, aF, t )
        Ex( aV, finForm )
      }
      case Eq( l, r ) => Eq( apply( n, l, t ), apply( n, r, t ) )
      case lessThan( l, r ) => lessThan( apply( n, l, t ), apply( n, r, t ) )
      case sims( l, r ) => sims( apply( n, l, t ), apply( n, r, t ) )
      case leq( l, r ) => leq( apply( n, l, t ), apply( n, r, t ) )
      case SchemaAtom( x, y ) if isIndexSort( y.head ) => SchemaAtom( x, List( y.head ) ++ y.map( x => apply( n, x, t ) ) )
      case SchemaAtom( x, y ) => SchemaAtom( x, y.map( x => apply( n, x, t ) ) )
      case _ => throw new Exception( "ERROR in unfolding missing formula !" + nLine + p.toString + nLine )
    }
  }
  def apply( ii: Int, p: SchemaExpression, t: SchemaExpression ): SchemaExpression = {
    t match {
      case SchemaFunction( head, l, Tindex )  => t
      case Var( name, Tindex ) if name == "k" => t
      case SchemaFunction( head, l, Ti ) => p match {
        case SchemaFunction( headi, li, Ti ) //if head.name == headi.name && l.length == li.length &&
        if head == headi && l.length == li.length &&
          l.zip( li ).foldLeft( true, true )( ( b, pair ) => if ( equalterms( pair._1, pair._2 ) && b._2 ) b else ( b._1, false ) )._1 => Const( "!" + ii + "!", Ti )
        case SchemaFunction( headi, li, Ti ) => SchemaFunction( head, li.map( x => apply( ii, x, t ) ) )
        case _                               => p
      }
      case Var( head, `->`( Tindex, Ti ) ) => p match {
        case SchemaFunction( headi, li, Ti ) if headi == head => SchemaFunction( Const( "!" + ii + "!", FunctionType( Ti, li.map( _.exptype ) ) ), li )
        case _ => p
      }
      case Var( head, Ti ) => p match {
        case Var( head2, Ti ) if head2 == head => Const( "!" + ii + "!", Ti )
        case _                                 => p
      }
      case Const( head, tt ) => p match {
        case Const( head2, t2 ) if tt == t2 && head2 == head => Const( "!" + ii + "!", Ti )
        case _ => p
      }
      case Abs( x, tt ) => p match { case Abs( x2, t2 ) if x == x2 && equalterms( tt, t2 ) => apply( ii, t2, t ) }
      case _            => throw new Exception( "ERROR in unfolding missing formula !" + nLine + t.toString + nLine )

    }
  }
}

object cloneMySol {
  val nLine = sys.props( "line.separator" )
  def apply( form: SchemaFormula, proofSize: Int ): SchemaFormula = {
    form match {
      case Neg( nF ) => {
        val finForm = apply( nF.asInstanceOf[SchemaFormula], proofSize )
        Neg( finForm )
      }
      case And( lF, rF ) => {
        val finFormL = apply( lF, proofSize )
        val finFormR = apply( rF, proofSize )
        And( finFormL, finFormR )
      }
      case Or( lF, rF ) => {
        val finFormL = apply( lF, proofSize )
        val finFormR = apply( rF, proofSize )
        Or( finFormL, finFormR )
      }
      case Imp( lF, rF ) => {
        val finFormL = apply( lF, proofSize )
        val finFormR = apply( rF, proofSize )
        Imp( finFormL, finFormR )
      }
      case All( aV, aF ) => {
        val finForm = apply( aF, proofSize )
        All( aV, finForm )
      }
      case Ex( aV, aF ) => {
        val finForm = apply( aF, proofSize )
        Ex( aV, finForm )
      }
      case Eq( l, r )       => Eq( cloneMyTerm( l, proofSize ), cloneMyTerm( r, proofSize ) )
      case lessThan( l, r ) => lessThan( cloneMyTerm( l, proofSize ), cloneMyTerm( r, proofSize ) )
      case sims( l, r )     => sims( cloneMyTerm( l, proofSize ), cloneMyTerm( r, proofSize ) )
      case leq( l, r )      => leq( cloneMyTerm( l, proofSize ), cloneMyTerm( r, proofSize ) )
      case SchemaAtom( head, sollist ) => {
        val finSOLList = sollist.map( x => cloneMyTerm( x, proofSize ) )
        SchemaAtom( head, finSOLList )
      }
      case _ => throw new Exception( "ERROR in unfolding missing formula !" + nLine + form.toString + nLine )
    }
  }
  def apply( form: SchemaFormula, IN: SchemaExpression, OUT: SchemaExpression ): SchemaFormula = {
    form match {
      case Neg( nF ) => {
        val finForm = apply( nF.asInstanceOf[SchemaFormula], IN, OUT )
        Neg( finForm )
      }
      case And( lF, rF ) => {
        val finFormL = apply( lF, IN, OUT )
        val finFormR = apply( rF, IN, OUT )
        And( finFormL, finFormR )
      }
      case Or( lF, rF ) => {
        val finFormL = apply( lF, IN, OUT )
        val finFormR = apply( rF, IN, OUT )
        Or( finFormL, finFormR )
      }
      case Imp( lF, rF ) => {
        val finFormL = apply( lF, IN, OUT )
        val finFormR = apply( rF, IN, OUT )
        Imp( finFormL, finFormR )
      }
      case All( aV, aF ) => {
        val finForm = apply( aF, IN, OUT )
        All( aV, finForm )
      }
      case Ex( aV, aF ) => {
        val finForm = apply( aF, IN, OUT )
        Ex( aV, finForm )
      }
      case Eq( l, r )       => Eq( cloneMyTerm( l, IN, OUT ), cloneMyTerm( r, IN, OUT ) )
      case lessThan( l, r ) => lessThan( cloneMyTerm( l, IN, OUT ), cloneMyTerm( r, IN, OUT ) )
      case sims( l, r )     => sims( cloneMyTerm( l, IN, OUT ), cloneMyTerm( r, IN, OUT ) )
      case leq( l, r )      => leq( cloneMyTerm( l, IN, OUT ), cloneMyTerm( r, IN, OUT ) )
      case SchemaAtom( head, sollist ) => {
        val finSOLList = sollist.map( x => cloneMyTerm( x, IN, OUT ) )
        SchemaAtom( head, finSOLList )
      }
      case _ => throw new Exception( "ERROR in unfolding missing formula !" + nLine + form.toString + nLine )
    }
  }
  def apply( form: SchemaFormula, rewriterules: List[Tuple2[SchemaFormula, SchemaFormula]] ): SchemaFormula = {
    form match {
      case Neg( nF ) => {
        val finForm = apply( nF.asInstanceOf[SchemaFormula], rewriterules )
        Neg( finForm )
      }
      case And( lF, rF ) => {
        val finFormL = apply( lF, rewriterules )
        val finFormR = apply( rF, rewriterules )
        And( finFormL, finFormR )
      }
      case Or( lF, rF ) => {
        val finFormL = apply( lF, rewriterules )
        val finFormR = apply( rF, rewriterules )
        Or( finFormL, finFormR )
      }
      case Imp( lF, rF ) => {
        val finFormL = apply( lF, rewriterules )
        val finFormR = apply( rF, rewriterules )
        Imp( finFormL, finFormR )
      }
      case All( aV, aF ) => {
        val finForm = apply( aF, rewriterules )
        All( aV, finForm )
      }
      case Ex( aV, aF ) => {
        val finForm = apply( aF, rewriterules )
        Ex( aV, finForm )
      }
      case Eq( l, r )         => Eq( l, r )
      case lessThan( l, r )   => lessThan( l, r )
      case sims( l, r )       => sims( l, r )
      case leq( l, r )        => leq( l, r )
      case SchemaAtom( _, _ ) => defineremove( form, rewriterules )
      case _                  => throw new Exception( "ERROR in unfolding missing formula !" + nLine + form.toString + nLine )
    }
  }
}

// TODO (Daniel): I introduced this function during the merge with the new_lambda_calculus
// branch. Due to the way that the Function.unapply method is set up, and the fact that
// the code in this file often needs to access the name of some variable or constant,
// this utility function was helpful. It should be removed once the unapply functions of
// Function and Atom are improved (see comments there).
object getName {
  def apply( term: SchemaExpression ) = term match {
    case Const( sym, _ ) => sym
    case Var( sym, _ )   => sym
  }
}

object cloneMyTerm {
  val nLine = sys.props( "line.separator" )
  def apply( term: SchemaExpression, proofSize: Int ): SchemaExpression = {
    term match {
      case SchemaFunction( n, l, t ) if getName( n ) == "schS" && t == Tindex => SchemaFunction( n, l.map( x => apply( x, proofSize ) ) )
      case Var( n, t ) if n == "k" && t == Tindex => maketogether( proofSize )
      case SchemaFunction( n, l, t ) if t == Tindex => SchemaFunction( n, l.map( x => apply( x, proofSize ) ) )
      case SchemaFunction( n, l, t ) if t == Ti => SchemaFunction( n, l.map( x => apply( x, proofSize ) ) )
      case Var( n, t ) if t == Ti | t == Tindex -> Ti => Var( n, t )
      case Const( n, t ) => Const( n, t )
      case Abs( x, t ) => Abs( x, apply( t, proofSize ) )
      case _ => throw new Exception( "ERROR in unfolding missing formula !" + nLine + term.toString + nLine )

    }
  }
  def apply( term: SchemaExpression, IN: SchemaExpression, OUT: SchemaExpression ): SchemaExpression = {
    term match {
      case SchemaFunction( head, l, Tindex ) if getName( head ) == "schS" => SchemaFunction( head, l )
      case Var( n, Tindex ) if n == "k"                                   => Var( n, Tindex )
      case SchemaFunction( n, l, Tindex )                                 => SchemaFunction( n, l.map( x => apply( x, IN, OUT ) ) )
      case SchemaFunction( n, l, Ti ) => IN match {
        case SchemaFunction( ni, li, Ti ) if n == ni && l.length == li.length && l.zip( li ).foldLeft( true, true )( ( b, pair ) => if ( equalterms( pair._1, pair._2 ) && b._2 ) b else ( b._1, false ) )._1 => OUT
        case SchemaFunction( ni, li, Ti ) if n == ni => OUT match {
          // FIXME (Daniel): I don't understand the following line.
          // commented out to make compile, fix later.
          //case Var(no,Ti) =>  Function(no,li)
          case _ => SchemaFunction( ni, li )
        }
        case _ => SchemaFunction( n, l.map( x => apply( x, IN, OUT ) ) )
      }
      case Var( n, t ) if t == Ti | t == Tindex -> Ti => IN match {
        case Var( ni, ti ) if t == ti && ni == n => OUT
        case _                                   => Var( n, t )
      }
      case Const( n, t ) => IN match {
        case Const( ni, ti ) if t == ti && ni == n => OUT
        case _                                     => Const( n, t )
      }
      case Abs( x, t ) => Abs( x, apply( t, IN, OUT ) )
      case _           => throw new Exception( "ERROR in unfolding missing formula !" + nLine + term.toString + nLine )

    }
  }
}

object equalforms {
  val nLine = sys.props( "line.separator" )
  def apply( form: SchemaFormula, form2: SchemaFormula ): Boolean = {
    form match {
      case Neg( nF ) => form2 match {
        case Neg( nF2 ) => apply( nF, nF2 )
        case _          => false
      }
      case And( lF, rF ) => form2 match {
        case And( lF2, rF2 ) => apply( lF, lF2 ) && apply( rF, rF2 )
        case _               => false
      }
      case Or( lF, rF ) => form2 match {
        case Or( lF2, rF2 ) => apply( lF, lF2 ) && apply( rF, rF2 )
        case _              => false
      }
      case Imp( lF, rF ) => form2 match {
        case Imp( lF2, rF2 ) => apply( lF, lF2 ) && apply( rF, rF2 )
        case _               => false
      }
      case All( aV, aF ) => form2 match {
        case All( aV2, aF2 ) if aV == aV2 => apply( aF, aF2 )
        case _                            => false
      }
      case Ex( aV, aF ) => form2 match {
        case Ex( aV2, aF2 ) if aV == aV2 => apply( aF, aF2 )
        case _                           => false
      }
      case Eq( l, r ) => form2 match {
        case Eq( l2, r2 ) => equalterms( l, l2 ) && equalterms( r, r2 )
        case _            => false
      }
      case lessThan( l, r ) => form2 match {
        case lessThan( l2, r2 ) => equalterms( l, l2 ) && equalterms( r, r2 )
        case _                  => false
      }
      case sims( l, r ) => form2 match {
        case sims( l2, r2 ) => equalterms( l, l2 ) && equalterms( r, r2 )
        case _              => false
      }
      case leq( l, r ) => form2 match {
        case leq( l2, r2 ) => equalterms( l, l2 ) && equalterms( r, r2 )
        case _             => false
      }
      case SchemaAtom( x, y ) => form2 match {
        case SchemaAtom( x2, y2 ) if x == x2 =>
          y.zip( y2 ).foldLeft( Tuple2( true, true ) )( ( b, pair ) => if ( equalterms( pair._1, pair._2 ) && b._2 ) b else Tuple2( b._1, false ) )._1
        case _ => false
      }
      case _ => throw new Exception( "ERROR in unfolding missing formula !" + nLine + form.toString + nLine )
    }
  }
}

object equalterms {
  val nLine = sys.props( "line.separator" )
  def apply( term: SchemaExpression, term2: SchemaExpression ): Boolean = {
    term match {
      case SchemaFunction( head, l, Tindex ) if getName( head ) == "schS" => term2 match {
        case SchemaFunction( head2, l2, Tindex ) if getName( head2 ) == "schS" =>
          l.zip( l2 ).foldLeft( Tuple2( true, true ) )( ( b, pair ) => if ( apply( pair._1, pair._2 ) && b._2 ) b else Tuple2( b._1, false ) )._1
        case _ => false
      }
      case Var( "k", Tindex ) => term2 match {
        case Var( "k", Tindex ) => true
        case _                  => false
      }
      case SchemaFunction( n, l, Tindex ) => term2 match {
        case SchemaFunction( n2, l2, Tindex ) if n == n2 && l.length == l2.length =>
          l.zip( l2 ).foldLeft( Tuple2( true, true ) )( ( b, pair ) => if ( apply( pair._1, pair._2 ) && b._2 ) b else Tuple2( b._1, false ) )._1
        case _ => false
      }
      case SchemaFunction( n, l, Ti ) => term2 match {
        case SchemaFunction( n2, l2, Ti ) if n == n2 && l.length == l2.length =>
          l.zip( l2 ).foldLeft( Tuple2( true, true ) )( ( b, pair ) => if ( apply( pair._1, pair._2 ) && b._2 ) b else Tuple2( b._1, false ) )._1
        case _ => false
      }
      case Var( n, `->`( Tindex, Ti ) ) => term2 match {
        case Var( n2, `->`( Tindex, Ti ) ) if n2 == n => true
        case _                                        => false
      }
      case Var( n, Ti ) => term2 match {
        case Var( n2, Ti ) if n2 == n => true
        case _                        => false
      }
      case Const( n, t ) => term2 match {
        case Const( n2, t2 ) if t == t2 && n2 == n => true
        case _                                     => false
      }
      case Abs( x, t ) => term2 match { case Abs( x2, t2 ) if x == x2 => apply( t, t2 ) }
      case _           => throw new Exception( "ERROR in unfolding missing formula !" + nLine + term.toString + nLine )

    }
  }
}
object AtomMatch {
  def apply( form: SchemaFormula, fform: SchemaFormula ): Boolean = {
    form match {
      case Neg( nF )        => apply( nF.asInstanceOf[SchemaFormula], fform )
      case And( lF, rF )    => apply( lF, fform ) || apply( rF, fform )
      case Or( lF, rF )     => apply( lF, fform ) || apply( rF, fform )
      case Imp( lF, rF )    => apply( lF, fform ) || apply( rF, fform )
      case All( aV, aF )    => apply( aF, fform )
      case Ex( aV, aF )     => apply( aF, fform )
      case Eq( l, r )       => false
      case lessThan( l, r ) => false
      case sims( l, r )     => false
      case leq( l, r )      => false
      case SchemaAtom( x, y ) => fform match {
        case SchemaAtom( xx, yy ) if xx == x && yy.length == y.length && isIndexSort( y.head ) && isIndexSort( yy.head ) =>
          y.zip( yy ).foldLeft( Tuple2( true, true ) )( ( b, pair ) => if ( equalterms( pair._1, pair._2 ) && b._2 ) b else Tuple2( b._1, false ) )._1 case _ => false
      }
      case SchemaAtom( x, y ) => false
      case _                  => false
    }
  }
  def apply( form: SchemaFormula ): Boolean = {
    form match {
      case SchemaAtom( x, y ) => isIndexSort( y.head )
      case _                  => false
    }
  }
}
object isIndexSort {
  def apply( term: SchemaExpression ): Boolean = {
    term match {
      case SchemaFunction( head, l, Tindex ) if getName( head ) == "schS" => apply( l.head )
      case Var( "k", Tindex ) => true
      case Const( "0", Tindex ) => true
      case _ => false

    }
  }
}

