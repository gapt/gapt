package gapt.examples.sequence

import gapt.expr.formula.fol.{ FOLConst, FOLFunction, FOLTerm, FOLVar }
import gapt.expr.formula.hol.universalClosure
import gapt.expr.formula.{ All, Eq }
import gapt.proofs.lk.rules.macros.{ ContractionMacroRule, WeakeningContractionMacroRule, WeakeningLeftMacroRule }
import gapt.proofs.lk.rules._
import gapt.proofs.lk.{ LKProof, rules }
import gapt.proofs.{ HOLSequent, ProofBuilder }

object FactorialFunctionEqualityExampleProof2 extends ProofSequence {
  import gapt.expr.formula.fol.Utils.{ numeral => num }

  val zero = FOLConst( "0" )
  val one = s( zero )
  val alpha = FOLVar( "α" )
  val beta = FOLVar( "β" )
  val nu = FOLVar( "ν" )
  val gamma = FOLVar( "γ" )

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val z = FOLVar( "z" )
  val w = FOLVar( "w" )

  def s( x: FOLTerm ) = FOLFunction( "s", List( x ) )
  def m( x: FOLTerm, y: FOLTerm ) = FOLFunction( "*", x, y )
  def f( x: FOLTerm ) = FOLFunction( "f", List( x ) )
  def g( x: FOLTerm, y: FOLTerm ) = FOLFunction( "g", x, y )

  def f0 = Eq( f( zero ), s( zero ) )
  def fST( x: FOLTerm ) = Eq( f( s( x ) ), m( s( x ), f( x ) ) )
  def g0( x: FOLTerm ) = Eq( g( x, zero ), x )
  def gST( x: FOLTerm, y: FOLTerm ) = Eq( g( x, s( y ) ), g( m( x, s( y ) ), y ) )
  def uR( x: FOLTerm ) = Eq( m( x, s( zero ) ), x )
  def uL( x: FOLTerm ) = Eq( m( s( zero ), x ), x )
  def ASSO( x: FOLTerm, y: FOLTerm, z: FOLTerm ) = Eq( m( m( x, y ), z ), m( x, m( y, z ) ) )
  def target( x: FOLTerm ) = Eq( f( x ), g( s( zero ), x ) )

  def apply( n: Int ): LKProof = {
    /**
     * Computes 1 * n * (n- 1) * … * k, associated to the left.
     *
     */
    def product( k: Int ) =
      ( k until n + 1 ).reverse.foldLeft( one ) { ( acc: FOLTerm, i: Int ) =>
        m( acc, num( i ) )
      }

    val p1 = ( ProofBuilder
      c ReflexivityAxiom( product( 1 ) )
      u ( WeakeningLeftMacroRule( _, Seq( uR( product( 1 ) ), f0, g0( product( 1 ) ) ) ) )
      u ( EqualityRightRule( _, uR( product( 1 ) ), Eq( product( 1 ), product( 1 ) ),
        Eq( m( product( 1 ), one ), product( 1 ) ) ) )
        u ( EqualityRightRule( _, f0, Eq( m( product( 1 ), one ), product( 1 ) ),
          Eq( m( product( 1 ), f( zero ) ), product( 1 ) ) ) )
          u ( EqualityRightRule( _, g0( product( 1 ) ),
            Eq( m( product( 1 ), f( zero ) ), product( 1 ) ),
            Eq( m( product( 1 ), f( zero ) ), g( product( 1 ), zero ) ) ) )
            u ( ForallLeftRule( _, All( x, uR( x ) ), product( 1 ) ) )
            u ( ForallLeftRule( _, All( x, g0( x ) ), product( 1 ) ) ) qed )

    val p2 = ( 0 until n ).foldLeft[LKProof]( p1 ) { ( acc: LKProof, i: Int ) =>
      ( ProofBuilder
        c acc
        u ( WeakeningLeftMacroRule( _, Seq(
          ASSO( product( i + 2 ), num( i + 1 ), f( num( i ) ) ),
          fST( num( i ) ),
          gST( product( i + 2 ), num( i ) ) ) ) )
        u ( EqualityRightRule( _, ASSO( product( i + 2 ), num( i + 1 ), f( num( i ) ) ),
          Eq( m( product( i + 1 ), f( num( i ) ) ), g( product( i + 1 ), num( i ) ) ),
          Eq( m( product( i + 2 ), m( num( i + 1 ), f( num( i ) ) ) ), g( product( i + 1 ), num( i ) ) ) ) )
          u ( macros.ForallLeftBlock( _, universalClosure( ASSO( x, y, z ) ),
            List( product( i + 2 ), num( i + 1 ), f( num( i ) ) ) ) )
            u ( EqualityRightRule( _, fST( num( i ) ),
              Eq( m( product( i + 2 ), m( num( i + 1 ), f( num( i ) ) ) ), g( product( i + 1 ), num( i ) ) ),
              Eq( m( product( i + 2 ), f( num( i + 1 ) ) ), g( product( i + 1 ), num( i ) ) ) ) )
              u ( EqualityRightRule( _, gST( product( i + 2 ), num( i ) ),
                Eq( m( product( i + 2 ), f( num( i + 1 ) ) ), g( product( i + 1 ), num( i ) ) ),
                Eq( m( product( i + 2 ), f( num( i + 1 ) ) ), g( product( i + 2 ), num( i + 1 ) ) ) ) )
                u ( ForallLeftRule( _, universalClosure( fST( x ) ), num( i ) ) )
                u ( rules.macros.ForallLeftBlock( _, universalClosure( gST( x, y ) ), List( product( i + 2 ), num( i ) ) ) )
                u ( ContractionMacroRule( _ ) ) qed )
    }

    ( ProofBuilder
      c p2
      u ( WeakeningLeftRule( _, uL( f( num( n ) ) ) ) )
      u ( EqualityRightRule( _, uL( f( num( n ) ) ),
        Eq( m( one, f( num( n ) ) ), g( one, num( n ) ) ),
        target( num( n ) ) ) )
        u ( ForallLeftRule( _, All( x, uL( x ) ), f( num( n ) ) ) )
        u ( WeakeningContractionMacroRule( _, endSequent( n ) ) ) qed )
  }

  def endSequent( n: Int ): HOLSequent = HOLSequent(
    List(
      f0,
      fST( x ),
      g0( x ),
      gST( x, y ),
      uR( x ),
      uL( x ),
      ASSO( x, y, z ) ) map universalClosure.apply,
    List(
      target( num( n ) ) ) )
}
