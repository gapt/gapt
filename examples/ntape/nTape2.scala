package gapt.examples

import gapt.expr.fol.{ Counter, replaceAbstractions }
import gapt.expr.{ Abs, Const, Atom, Expr, To }
import gapt.formats.ClasspathInputFile
import gapt.proofs.ceres_omega.AnalysisWithCeresOmega
import gapt.formats.llk.loadLLK
import gapt.proofs.expansion.{ ETAnd, ETImp, ETSkolemQuantifier, ETWeakQuantifier, ExpansionProof, ExpansionTree }

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
  //prints the interesting terms from the expansion sequent
  def printInstances( expansion_proof: ExpansionProof, definitions: Map[Const, Expr] ) = {
    println( "------------ Witness Terms from Expansion Proof --------------" )

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
        ETSkolemQuantifier( _, _, _,
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
        ETSkolemQuantifier( _, _, _,
          ETImp( _, ETWeakQuantifier( f, step_instances ) )
          )
        ), _ ) =>
        val List( ( base, _ ) ) = base_instances.toList
        val List( ( step, _ ) ) = step_instances.toList
        ( base, step )
    }

    ( ind1base, ind1step, ind2base, ind2step ) match {
      case ( Abs( xb, sb ), Abs( xs, ss ), Abs( yb, tb ), Abs( ys, ts ) ) =>
        val map = Map[Expr, String]()
        val counter = new Counter

        val ( map1, sb1 ) = replaceAbstractions( sb, map, counter )
        val ( map2, ss1 ) = replaceAbstractions( ss, map1, counter )
        val ( map3, tb1 ) = replaceAbstractions( tb, map2, counter )
        val ( map4, ts1 ) = replaceAbstractions( ts, map3, counter )

        println( "base 1 simplified: " + Abs( xb, sb1 ) )
        println( "base 2 simplified: " + Abs( yb, tb1 ) )
        println( "step 1 simplified: " + Abs( xs, ss1 ) )
        println( "step 2 simplified: " + Abs( ys, ts1 ) )

        println( "With shortcuts:" )
        for ( ( term, sym ) <- map4 ) {
          println( "Symbol: " + sym )
          println( "Term:   " + term )
        }
    }

  }

  private def decompose( et: ExpansionTree ): List[ExpansionTree] = et match {
    case ETAnd( x, y ) => decompose( x ) ++ decompose( y );
    case _             => List( et )
  }
}
