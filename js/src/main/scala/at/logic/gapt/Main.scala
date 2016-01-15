package at.logic.gapt

import at.logic.gapt.examples.LinearExampleProof
import at.logic.gapt.proofs.expansionTrees.ExpansionProofToLK
import at.logic.gapt.proofs.lk.LKToExpansionProof

import scala.scalajs.js

object Main extends js.JSApp {
  def main(): Unit = {
    val p = LinearExampleProof( 6 )
    val e = LKToExpansionProof( p )
    val p2 = ExpansionProofToLK( e )
    println( p2 )
  }
}
