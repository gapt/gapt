package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLSequent
import org.specs2.mutable._

class TermExtractionTest extends Specification {
  val Seq( x, y ) = Seq( "x", "y" ).map( FOLVar( _ ) )
  val esP = All( x, FOLAtom( "P", x, y ) )
  val esR = Ex( x, FOLAtom( "R", x ) )
  val endSequent = HOLSequent(
    Seq( esP ),
    Seq( esR )
  )

  val instP = All( x, FOLAtom( "P", x, FOLConst( "d" ) ) )
  val expTreeP = ETWeakQuantifier( instP, Map(
    FOLConst( "c" ) -> ETAtom( FOLAtom( "P", FOLConst( "c" ), FOLConst( "d" ) ), false ),
    FOLConst( "d" ) -> ETAtom( FOLAtom( "P", FOLConst( "d" ), FOLConst( "d" ) ), false )
  ) )

  val expSeq = ExpansionSequent( Seq( expTreeP ), Seq() )

  "extractInstances" in {
    extractInstances( expSeq ).antecedent must contain( exactly(
      FOLAtom( "P", FOLConst( "c" ), FOLConst( "d" ) ).asInstanceOf[HOLFormula],
      FOLAtom( "P", FOLConst( "d" ), FOLConst( "d" ) )
    ) )
  }

  "TermInstanceEncoding" should {
    val encoding = FOLInstanceTermEncoding( endSequent )
    "encode the instance terms as arguments" in {
      encoding.encode( expSeq ).map {
        case FOLFunction( _, args ) => args
      } must contain( exactly( Seq( FOLConst( "c" ).asInstanceOf[FOLTerm] ), Seq( FOLConst( "d" ) ) ) )
    }
    "decode correctly" in {
      encoding.decodeToPolarizedFormula( encoding.encode( -FOLAtom( "P", FOLConst( "c" ), FOLConst( "d" ) ) ) ) must_==
        ( FOLAtom( "P", FOLConst( "c" ), FOLVar( "y" ) ) -> false )
    }
  }
}