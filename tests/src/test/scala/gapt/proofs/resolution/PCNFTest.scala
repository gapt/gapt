package gapt.proofs.resolution

import gapt.expr._
import gapt.proofs._
import gapt.proofs.lk._
import org.specs2.mutable._

class PCNFTest extends Specification {
  def checkPCNF( sequent: HOLSequent, clause: HOLClause ) = {
    val projection = PCNF( sequent, clause )
    projection.endSequent isSubMultisetOf ( sequent ++ clause ) aka s"${projection.endSequent} isSubMultisetOf ($sequent ++ $clause)" must_== true
  }

  "PCNF" should {
    val Seq( p, q, r, s ) = Seq( "P", "Q", "R", "S" ) map { FOLAtomConst( _, 1 ) }
    val a = FOLConst( "a" )
    "an atom Pa in the CNF(-s) where s is the sequent" in {
      "|- ¬Pa" in { checkPCNF( Sequent() :+ -p( a ), Clause() :+ p( a ) ) }
      "Pa |-" in { checkPCNF( p( a ) +: Sequent(), Clause() :+ p( a ) ) }
      "|- ¬Pa ∨ Qa" in { checkPCNF( Sequent() :+ ( -p( a ) | q( a ) ), Clause() :+ p( a ) ) }
      "|- Qa ∨ ¬Pa" in { checkPCNF( Sequent() :+ ( q( a ) | -p( a ) ), Clause() :+ p( a ) ) }
      "Pa ∧ Qa |-" in { checkPCNF( ( p( a ) & q( a ) ) +: Sequent(), Clause() :+ p( a ) ) }
      "Qa ∧ Pa |-" in { checkPCNF( ( q( a ) & p( a ) ) +: Sequent(), Clause() :+ p( a ) ) }
      "Sa, Qa ∧ Pa |- Ra" in { checkPCNF( s( a ) +: ( q( a ) & p( a ) ) +: Sequent() :+ r( a ), Clause() :+ p( a ) ) }
      "Qa |- ¬Pa ∧ Qa" in { checkPCNF( q( a ) +: Sequent() :+ ( -p( a ) | q( a ) ), Clause() :+ p( a ) ) }
    }
    "an atom Px in the CNF(-f(s)) where s is the sequent" in {
      val x = FOLVar( "x" )
      "∀xPx |-" in { checkPCNF( All( x, p( x ) ) +: Sequent(), Clause() :+ p( x ) ) }
      "|- ∃xPx" in { checkPCNF( Sequent() :+ Ex( x, -p( x ) ), Clause() :+ p( x ) ) }
    }
    "weird bug" in {
      val Seq( a, b, c, d, e, f, g, h, i, j ) = 'a' to 'j' map { _.toString } map { FOLAtom( _ ) }
      val formula = ( ( ( ( ( ( ( a & b ) & ( ( c | -d ) | -e ) ) & d ) & f ) & g ) & e ) & h ) & ( ( ( i | -f ) | -i ) | -j )
      val clause = d +: e +: Clause() :+ c
      checkPCNF( formula +: Sequent(), clause )
    }
  }
}
