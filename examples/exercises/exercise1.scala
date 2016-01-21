package at.logic.gapt.examples.autded

object exercise1 {
  println(
    """
  Get the formula φ_3 from Example 2.1 of the course notes by:
  gapt> PQPairs( 3 )

  Transform it to CNF using the distributivity-based algorithm by:
  gapt> CNFp( PQPairs( 3 ))

  Transform it to CNF using the Tseitin-transformation by:
  gapt> TseitinCNF( PQPairs( 3 ))

  Transform φ_n for a few n larger than 3 to CNF using both of the above methods.

  * What are (approximately) the largest n s.t. CNFp/TseitinCNF finishes within 5 seconds?

  * What are |φ_n| for these n?

  You can measure the time a command needs as follows:
  gapt> time { TseitinCNF( PQPairs( 3 )) }

  You can compute the logical complexity |φ_3| of φ_3 as follows:
  gapt> lcomp( PQPairs( 3 ))
"""
  )
}

