package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lkNew._
import org.specs2.mutable._

class PCNFTest extends Specification {
  implicit def expr2atom( expr: LambdaExpression ): HOLAtom = expr.asInstanceOf[HOLAtom]
  implicit def sequent2hol( seq: Sequent[LambdaExpression] ): HOLSequent = seq map { _.asInstanceOf[HOLFormula] }

  def checkPCNF( sequent: HOLSequent, clause: HOLClause ) = {
    val projection = PCNF( sequent, clause )
    projection.endSequent multiSetEquals ( sequent ++ clause ) aka s"${projection.endSequent} multiSetEquals ($sequent ++ $clause)" must_== true
    projection.subProofs filter { _.isInstanceOf[ArbitraryAxiom] } must beEmpty
  }

  "PCNF" should {
    val Seq( p, q, r, s ) = Seq( "P", "Q", "R", "S" ) map { FOLAtomHead( _, 1 ) }
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
    "variable renamings" in {
      val Seq( x, y ) = Seq( "x", "y" ) map { FOLVar( _ ) }
      "∀xPx |-" in { checkPCNF( All( x, p( x ) ) +: Sequent(), Clause() :+ p( y ) ) }
    }
  }
}
