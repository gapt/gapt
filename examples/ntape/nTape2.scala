package gapt.examples

import gapt.expr.formula.Atom
import gapt.expr.formula.fol.Hol2FolDefinitions
import gapt.expr.formula.fol.replaceAbstractions
import gapt.expr.ty.To
import gapt.expr.{ Abs, Const, Expr }
import gapt.formats.ClasspathInputFile
import gapt.proofs.ceres_omega.AnalysisWithCeresOmega
import gapt.formats.llk.loadLLK
import gapt.proofs.expansion.{ ETAnd, ETImp, ETSkolemQuantifier, ETWeakQuantifier, ExpansionProof, ExpansionTree }
import gapt.utils.Counter

/**
 * Version 2 of the higher-order n-Tape proof.
 */
class nTape2 extends AnalysisWithCeresOmega {

  override def proofdb() = loadLLK( ClasspathInputFile( "ntape/ntape2.llk" ) )

  override def root_proof() = "TAPEPROOF"

  override def printStatistics() = {
    super.printStatistics()
    nTapeInstances.printInstances( this.expansion_proof, this.proofdb().Definitions )
  }
}

object nTape2 extends nTape2

object nTapeInstances {
  def printInstances( expansion_proof: ExpansionProof, definitions: Map[Const, Expr] ) = {
    println( "------------ Witness Terms from Expansion Proof --------------" )
    val ( base1, base2, step1, step2, map ) = computeInstances( expansion_proof, definitions )
    println( "base 1 simplified: " + base1 )
    println( "base 2 simplified: " + base2 )
    println( "step 1 simplified: " + step1 )
    println( "step 2 simplified: " + step2 )

    println( "With shortcuts:" )
    for ( ( term, sym ) <- map ) {
      println( "Symbol: " + sym )
      println( "Term:   " + term )
    }
  }

  //prints the interesting terms from the expansion sequent
  def computeInstances( expansion_proof: ExpansionProof, definitions: Map[Const, Expr] ) = {

    //FIXME: we are using the induction axiom to find its expansion tree now, but antecedent(1) is still not perfect
    val conjuncts = decompose( expansion_proof.expansionSequent.antecedent( 1 ) )
    val ind_atom = Atom( Const( "IND", To ), List() )
    val ind_axiom = definitions.find( _._1 == ind_atom ).get._2
    val indet = conjuncts.find( _.shallow == ind_axiom ).get

    val List( ind1, ind2 ): List[ExpansionTree] = indet match {
      case ETWeakQuantifier( _, instances ) =>
        instances.values.toList
    }

    val ( ind1base, ind1step ) = ind1 match {
      case ETImp( ETAnd(
        ETWeakQuantifier( _, base_instances ),
        ETSkolemQuantifier( _, _,
          ETImp( _, ETWeakQuantifier( f, step_instances ) )
          )
        ), _ ) =>
        val List( ( base, _ ) ) = base_instances.toList
        val List( ( step, _ ) ) = step_instances.toList
        ( base, step )
    }

    val ( ind2base, ind2step ) = ind2 match {
      case ETImp( ETAnd(
        ETWeakQuantifier( _, base_instances ),
        ETSkolemQuantifier( _, _,
          ETImp( _, ETWeakQuantifier( f, step_instances ) )
          )
        ), _ ) =>
        val List( ( base, _ ) ) = base_instances.toList
        val List( ( step, _ ) ) = step_instances.toList
        ( base, step )
    }

    ( ( ind1base, ind1step, ind2base, ind2step ): @unchecked ) match {
      case ( Abs( xb, sb ), Abs( xs, ss ), Abs( yb, tb ), Abs( ys, ts ) ) =>
        implicit val defs = new Hol2FolDefinitions()

        val sb1 = replaceAbstractions( sb )
        val ss1 = replaceAbstractions( ss )
        val tb1 = replaceAbstractions( tb )
        val ts1 = replaceAbstractions( ts )

        ( Abs( xb, sb1 ), Abs( yb, tb1 ), Abs( xs, ss1 ), Abs( ys, ts1 ), defs.toLegacyMap )
    }
  }

  private def decompose( et: ExpansionTree ): List[ExpansionTree] = et match {
    case ETAnd( x, y ) => decompose( x ) ++ decompose( y );
    case _             => List( et )
  }
}
