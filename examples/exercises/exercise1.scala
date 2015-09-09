// setup
import at.logic.gapt.examples._
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs.resolution.TseitinCNF
import at.logic.gapt.provers.minisat.MiniSATProver
val minisat = new MiniSATProver

println( """
* Exercise A
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

* Exercise B
  Get the 5th Buss tautology by:
  gapt> BussTautology( 5 )

  Get the n-th pigeon hole principle tautology by:
  gapt> PigeonHolePrinciple( n, n-1 )

  Apply minisat to these by:
  gapt> minisat.isValid( PigeonHolePrinciple( 5, 4 ))
  gapt> minisat.isValid( BussTautology( 5 ))

 * What are (approximately) the largest n s.t. minisat finishes on the respective tautology within 5 seconds?

 * What are |φ_n| for these n?
""" )

