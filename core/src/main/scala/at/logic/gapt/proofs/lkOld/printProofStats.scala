package at.logic.gapt.proofs.lkOld

import at.logic.gapt.proofs.lkOld.base.LKProof

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
