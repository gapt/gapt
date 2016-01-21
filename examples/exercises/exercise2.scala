package at.logic.gapt.examples.autded

object exercise2 {
  println(
    """
  Get the 5th Buss tautology by:
  gapt> BussTautology( 5 )

  Get the n-th pigeon hole principle tautology by:
  gapt> PigeonHolePrinciple( n, n-1 )

  Apply minisat to these by:
  gapt> MiniSAT.isValid( PigeonHolePrinciple( 5, 4 ))
  gapt> MiniSAT.isValid( BussTautology( 5 ))

  * What are (approximately) the largest n s.t. minisat finishes on the respective tautology within 5 seconds?

  * What are |φ_n| for these n?
"""
  )
}

