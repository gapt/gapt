package gapt.proofs.expansion

import gapt.expr._
import gapt.proofs.{ HOLSequent, Sequent }
import org.specs2.mutable._

class TermExtractionTest extends Specification {
  val Seq( x, y ) = Seq( "x", "y" ).map( FOLVar( _ ) )
  val esP = All( x, FOLAtom( "P", x, y ) )
  val esR = Ex( x, FOLAtom( "R", x ) )
  val endSequent = hos"!x P x y :- ?x R x"

  val expansion = ExpansionProof(
    ETWeakQuantifier( hof"!x P x d", Map(
      le"c" -> ETAtom( hoa"P c d", Polarity.InAntecedent ),
      le"d" -> ETAtom( hoa"P d d", Polarity.InAntecedent ) ) ) +: Sequent() )

  "extractInstances" in {
    extractInstances( expansion ).antecedent must contain( exactly( hof"P c d", hof"P d d" ) )
  }

  "TermInstanceEncoding" should {
    val encoding = InstanceTermEncoding( endSequent )
    "encode the instance terms as arguments" in {
      encoding.encode( expansion ).map {
        case Apps( _, as ) => as
      } must contain( exactly( Seq( le"c" ), Seq( le"d" ) ) )
    }
    "decode correctly" in {
      encoding.decodeToPolarizedFormula( encoding.encode( hof"P c d" ) ) must_== ( hof"P c y", Polarity.InAntecedent )
    }
  }
}