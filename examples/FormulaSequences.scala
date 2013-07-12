/**********
 * Example formula sequences, usage example from CLI:
 *
 * scala> :load ../examples/FormulaSequences.scala
 * scala> val f = PigeonHolePrinciple( 4, 3 )
 **********/

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

  def c( i: Int ) = Atom( new ConstantStringSymbol("c_" + i), Nil )
  def d( i: Int ) = Atom( new ConstantStringSymbol("d_" + i), Nil )
  def F( i: Int ) : FOLFormula = if ( i == 1 ) Or( c( 1 ), d( 1 ) ) else And( F( i - 1 ), Or( c( i ), d( i ) ) )
  def A( i: Int ) = if ( i == 1 ) c( 1 ) else Imp( F( i - 1 ), c( i ) )
  def B( i: Int ) = if ( i == 1 ) d( 1 ) else Imp( F( i - 1 ), d( i ) )

  // the antecedens of the final sequent
  def Ant( i: Int ) : List[FOLFormula] = if ( i == 0 ) Nil else Or( A( i ), B( i ))::Ant( i - 1 )
}

/*
 * Constructs a formula representing the pigeon hole principle.
 *
 * Since we want to avoid empty disjunctions, we assume > 1 pigeons.
 *
 */
object PigeonHolePrinciple {
  // The binary relation symbol.
  val rel = ConstantStringSymbol("R")

  def apply( ps: Int, hs: Int ) = {
    assert( ps > 1 )
    Imp( Utils.andN( (1 to ps).map( p =>
            Utils.orN( (1 to hs).map( h => atom(p, h) ).toList ) ).toList ),
          Utils.orN( (1 to hs).map ( h =>
            Utils.orN( (2 to ps).map( p =>
              Utils.orN( ((1 to p - 1)).map( pp =>
                And(atom(p, h),atom(pp,h))).toList)).toList)).toList))
  }

  def atom( p: Int, h: Int ) = Atom(rel, pigeon(p)::hole(h)::Nil)

  def pigeon(i: Int) = FOLConst(ConstantStringSymbol("p_" + i))

  def hole(i: Int) = FOLConst(ConstantStringSymbol("h_" + i))
}
