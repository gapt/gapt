package at.logic.gapt.proofs.lk

import at.logic.gapt.proofs.lk.base.LKProof

object printProofStats {
  def apply( p: LKProof ) = {
    val stats = getStatistics( p )
    val total = rulesNumber( p )
    val quant = quantRulesNumber( p )
    val weakQuant = weakQuantRulesNumber( p )
    println( "------------- Statistics ---------------" )
    println( "Cuts: " + stats.cuts )
    println( "Number of quantifier inferences: " + quant )
    println( "Number of inferences: " + total )
    println( "Quantifier complexity: " + weakQuant )
    println( "----------------------------------------" )
  }
}
