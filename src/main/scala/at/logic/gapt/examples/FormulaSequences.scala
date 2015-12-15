package at.logic.gapt.examples
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ FOLClause, HOLSequent }

/**
 * Creates the n-th formula of a sequence where distributivity-based
 * algorithm produces only exponential CNFs.
 */
object PQPairs {
  def apply( n: Int ): FOLFormula = {
    assert( n >= 1 )
    if ( n == 1 )
      And( p( 1 ), q( 1 ) )
    else
      Or( apply( n - 1 ), And( p( n ), q( n ) ) )
  }

  def p( i: Int ) = FOLAtom( "p_" + i, Nil )
  def q( i: Int ) = FOLAtom( "q_" + i, Nil )
}

/**
 * Given n >= 2 creates an unsatisfiable first-order clause set based on a
 * statement about the permutations in S_n.
 */
object Permutations {
  def apply( n: Int ): List[FOLClause] = {
    assert( n >= 2 )
    val Rord = FOLAtom( "R", List.range( 1, n + 1 ).map( x( _ ) ) )
    val Rtransp = FOLAtom( "R", x( 2 ) :: x( 1 ) :: List.range( 3, n + 1 ).map( x( _ ) ) )
    val Rrot = FOLAtom( "R", x( n ) :: List.range( 1, n ).map( x( _ ) ) )

    val Rord_c = FOLAtom( "R", List.range( 1, n + 1 ).map( c( _ ) ) )
    val even = List.range( 2, n + 1 ).sliding( 1, 2 ).flatten.toList
    val odd = List.range( 1, n + 1 ).sliding( 1, 2 ).flatten.toList
    val Revenodd_c = FOLAtom( "R", ( odd ++ even ).map( c( _ ) ) )

    val Ctransp = FOLClause( Rord :: Nil, Rtransp :: Nil )
    val Crot = FOLClause( Rord :: Nil, Rrot :: Nil )
    val Goalpos = FOLClause( Nil, Rord_c :: Nil )
    val Goalneg = FOLClause( Revenodd_c :: Nil, Nil )

    Ctransp :: Crot :: Goalpos :: Goalneg :: Nil
  }

  /**
   * return the set of constants which occur in the n-th clause set
   */
  def constants( n: Int ): Set[FOLTerm] = List.range( 1, n + 1 ).map( c( _ ) ).toSet

  private def x( i: Int ) = FOLVar( "x_" + i )
  private def c( i: Int ) = FOLConst( "c_" + i )
}

/**
 * Creates the n-th tautology of a sequence that has only exponential-size cut-free proofs
 *
 * This sequence is taken from: S. Buss. "Weak Formal Systems and Connections to
 * Computational Complexity". Lecture Notes for a Topics Course, UC Berkeley, 1988,
 * available from: http://www.math.ucsd.edu/~sbuss/ResearchWeb/index.html
 */
object BussTautology {
  def apply( n: Int ): HOLSequent = HOLSequent( Ant( n ), c( n ) :: d( n ) :: Nil )

  def c( i: Int ) = FOLAtom( "c_" + i, Nil )
  def d( i: Int ) = FOLAtom( "d_" + i, Nil )
  def F( i: Int ): FOLFormula = if ( i == 1 ) Or( c( 1 ), d( 1 ) ) else And( F( i - 1 ), Or( c( i ), d( i ) ) )
  def A( i: Int ) = if ( i == 1 ) c( 1 ) else Imp( F( i - 1 ), c( i ) )
  def B( i: Int ) = if ( i == 1 ) d( 1 ) else Imp( F( i - 1 ), d( i ) )

  // the antecedens of the final sequent
  def Ant( i: Int ): List[FOLFormula] = if ( i == 0 ) Nil else Or( A( i ), B( i ) ) :: Ant( i - 1 )
}

/**
 * Constructs a formula representing the pigeon hole principle. More precisely:
 * PigeonHolePrinciple( p, h ) states that if p pigeons are put into h holes
 * then there is a hole which contains two pigeons. PigeonHolePrinciple( p, h )
 * is a tautology iff p > h.
 *
 * Since we want to avoid empty disjunctions, we assume > 1 pigeons.
 */
object PigeonHolePrinciple {
  // The binary relation symbol.
  val rel = "R"

  /**
   * @param ps the number of pigeons
   * @param hs the number of holes
   */
  def apply( ps: Int, hs: Int ) = {
    assert( ps > 1 )
    Imp(
      And( ( 1 to ps ).map( p =>
        Or( ( 1 to hs ).map( h => atom( p, h ) ).toList ) ).toList ),
      Or( ( 1 to hs ).map( h =>
        Or( ( 2 to ps ).map( p =>
          Or( ( ( 1 to p - 1 ) ).map( pp =>
            And( atom( p, h ), atom( pp, h ) ) ).toList ) ).toList ) ).toList )
    )
  }

  def atom( p: Int, h: Int ) = FOLAtom( rel, pigeon( p ) :: hole( h ) :: Nil )

  def pigeon( i: Int ) = FOLConst( "p_" + i )

  def hole( i: Int ) = FOLConst( "h_" + i )
}
