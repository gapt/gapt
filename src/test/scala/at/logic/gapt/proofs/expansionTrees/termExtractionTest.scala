package at.logic.gapt.proofs.expansionTrees

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.base.HOLSequent
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
  val expTreeP = ETWeakQuantifier( instP, Seq(
    ETAtom( FOLAtom( "P", FOLConst( "c" ), FOLConst( "d" ) ) )
      -> FOLConst( "c" ),
    ETAtom( FOLAtom( "P", FOLConst( "d" ), FOLConst( "d" ) ) )
      -> FOLConst( "d" )
  ) ).asInstanceOf[ExpansionTree]

  val expSeq = ExpansionSequent( Seq( expTreeP ), Seq() )

  "extractInstanceTerms" should {
    "expansion trees" in {
      val instanceTerms = extractInstanceTerms( expTreeP )
      instanceTerms must contain( exactly(
        instP -> Seq( FOLConst( "c" ).asInstanceOf[FOLTerm] ),
        instP -> Seq( FOLConst( "d" ) )
      ) )
    }
    "expansion sequents" in {
      val instanceTerms = extractInstanceTerms( expSeq )
      instanceTerms must contain( exactly(
        ( instP -> Seq( FOLConst( "c" ).asInstanceOf[FOLTerm] ) ) -> true,
        ( instP -> Seq( FOLConst( "d" ) ) ) -> true
      ) )
    }
  }

  "extractInstances" in {
    extractInstances( expSeq ).antecedent must contain( exactly(
      FOLAtom( "P", FOLConst( "c" ), FOLConst( "d" ) ).asInstanceOf[HOLFormula],
      FOLAtom( "P", FOLConst( "d" ), FOLConst( "d" ) )
    ) )
  }

  "TermInstanceEncoding" should {
    val encoding = InstanceTermEncoding( endSequent )
    "encode the instance terms as arguments" in {
      encoding.encode( expSeq ).map {
        case FOLFunction( _, args ) => args
      } must contain( exactly( Seq( FOLConst( "c" ).asInstanceOf[FOLTerm] ), Seq( FOLConst( "d" ) ) ) )
    }
    "decode correctly" in {
      encoding.decode( encoding.encode( FOLAtom( "P", FOLConst( "c" ), FOLConst( "d" ) ) -> true ) ) must_==
        ( FOLAtom( "P", FOLConst( "c" ), FOLVar( "y" ) ) -> true )
    }
  }
}