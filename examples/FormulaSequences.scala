package at.logic.gapt.examples
import at.logic.gapt.language.fol._
import at.logic.gapt.proofs.lk.base._

/*
 * Creates the n-th formula of a sequence where distributivity-based
 * algorithm produces only exponential CNFs.
 *
 */
object PQPairs {
  def apply( n: Int ): FOLFormula = {
    assert( n >= 1 )
    if ( n == 1 )
      FOLAnd( p( 1 ), q( 1 ))
    else
      FOLOr( apply( n - 1 ), FOLAnd( p( n ), q( n )))
  }

  def p( i: Int ) = FOLAtom( "p_" + i, Nil )
  def q( i: Int ) = FOLAtom( "q_" + i, Nil )
}

/*
 * Creates the n-th tautology of a sequence that has only exponential-size cut-free proofs
 *
 * This sequence is taken from: S. Buss. "Weak Formal Systems and Connections to
 * Computational Complexity". Lecture Notes for a Topics Course, UC Berkeley, 1988,
 * available from: http://www.math.ucsd.edu/~sbuss/ResearchWeb/index.html
 *
 */
object BussTautology {
  def apply( n: Int ) : FSequent = FSequent( Ant( n ), c( n )::d( n )::Nil )

  def c( i: Int ) = FOLAtom( "c_" + i, Nil )
  def d( i: Int ) = FOLAtom( "d_" + i, Nil )
  def F( i: Int ) : FOLFormula = if ( i == 1 ) FOLOr( c( 1 ), d( 1 ) ) else FOLAnd( F( i - 1 ), FOLOr( c( i ), d( i ) ) )
  def A( i: Int ) = if ( i == 1 ) c( 1 ) else FOLImp( F( i - 1 ), c( i ) )
  def B( i: Int ) = if ( i == 1 ) d( 1 ) else FOLImp( F( i - 1 ), d( i ) )

  // the antecedens of the final sequent
  def Ant( i: Int ) : List[FOLFormula] = if ( i == 0 ) Nil else FOLOr( A( i ), B( i ))::Ant( i - 1 )
}

/*
 * Constructs a formula representing the pigeon hole principle. More precisely:
 * PigeonHolePrinciple( p, h ) states that if p pigeons are put into h holes
 * then there is a hole which contains two pigeons. PigeonHolePrinciple( p, h )
 * is a tautology iff p > h.
 *
 * Since we want to avoid empty disjunctions, we assume > 1 pigeons.
 *
 */
object PigeonHolePrinciple {
  // The binary relation symbol.
  val rel = "R"

  /*
   * @param ps the number of pigeons
   * @param hs the number of holes
   **/
  def apply( ps: Int, hs: Int ) = {
    assert( ps > 1 )
    FOLImp( FOLAnd( (1 to ps).map( p =>
            FOLOr( (1 to hs).map( h => atom(p, h) ).toList ) ).toList ),
          FOLOr( (1 to hs).map ( h =>
            FOLOr( (2 to ps).map( p =>
              FOLOr( ((1 to p - 1)).map( pp =>
                FOLAnd(atom(p, h),atom(pp,h))).toList)).toList)).toList))
  }

  def atom( p: Int, h: Int ) = FOLAtom(rel, pigeon(p)::hole(h)::Nil)

  def pigeon(i: Int) = FOLConst("p_" + i)

  def hole(i: Int) = FOLConst("h_" + i)
}
