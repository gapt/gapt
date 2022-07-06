package gapt.formats.verit

import gapt.formats.verit.alethe.AletheProof
import gapt.formats.verit.alethe.Application
import gapt.formats.verit.alethe.Assume
import gapt.formats.verit.alethe.Forall
import gapt.formats.verit.alethe.Identifier
import gapt.formats.verit.alethe.Sort
import gapt.formats.verit.alethe.Step
import gapt.formats.verit.alethe.VariableDeclaration
import gapt.formats.verit.alethe.parseAletheProof
import org.specs2.mutable._

class AletheParserTest extends Specification {

  "alethe parser should" should {

    val i1 = "(assume h1 (and A B))"
    val h1 = Assume(
      "h1",
      Application( "and", List( Identifier( "A", None ), Identifier( "B", None ) ) ) )
    "parse syntactically well-formed assumption" in {
      val expectedOutput = AletheProof( List( h1 ) )
      parseAletheProof( i1 ) must_== expectedOutput
    }

    val i2 = "(assume h2 (forall ((x S1)) (P x)))"
    val h2 = Assume(
      "h2",
      Forall(
        List( VariableDeclaration( "x", Some( Sort( "S1" ) ) ) ),
        Application( "P", List( Identifier( "x", None ) ) ) ) )
    "parse syntactically well-formed assumption with quantifiers" in {
      val expectedOutput = AletheProof( List( h2 ) )
      parseAletheProof( i2 ) must_== expectedOutput
    }

    val i3 = "(step t3 (cl (= t1 t2)) :rule r1)"
    val t3 = Step( "r1", "t3",
      List( Application( "=", List( Identifier( "t1", None ), Identifier( "t2", None ) ) ) ),
      List(), List() )
    "parse well-formed step without premises and arguments" in {
      val expectedOutput = AletheProof( List( t3 ) )
      parseAletheProof( i3 ) must_== expectedOutput
    }

    val i4 = "(step t4 (cl) :rule r2 :premises (t3 h2))"
    val t4 = Step( "r2", "t4", List(), List( "t3", "h2" ), List() )
    "parse well-formed step with premises without arguments" in {
      val expectedOutput = AletheProof( List( t4 ) )
      parseAletheProof( i4 ) must_== expectedOutput
    }

    val input = i1 + "\n" + i2 + "\n" + i3 + "\n" + i4
    "parse commands in correct order" in {
      val expectedOutput = AletheProof( List( h1, h2, t3, t4 ) )
      parseAletheProof( input ) must_== expectedOutput
    }
  }
}
