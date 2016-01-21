package at.logic.gapt.formats.ivy

import org.specs2.mutable._
import at.logic.gapt.formats.lisp._
import java.io.File.separator
import scala.io.Source
import scala.util.{ Success, Failure }

/**
 * Test for the Ivy interface.
 */
class IvyTest extends Specification {
  def parseClasspathFile( filename: String ) =
    SExpressionParser parseString Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( filename ) ).mkString

  "The Ivy Parser " should {
    " parse an empty list " in {
      SExpressionParser.tryParseString( "()" ) must_== Success( List( LList() ) )
    }

    " not parse an empty list + garbage" in {
      SExpressionParser.tryParseString( "())" ) must beLike { case Failure( _ ) => ok }
    }

    " parse the atom a1" in {
      SExpressionParser.tryParseString( "a1" ) must_== Success( List( LAtom( "a1" ) ) )
    }

    " parse the atom a2(space)" in {
      SExpressionParser.tryParseString( "a2    " ) must_== Success( List( LAtom( "a2" ) ) )
    }

    """ parse the atom "a b c" """ in {
      SExpressionParser.tryParseString( """"a b c"""" ) must_== Success( List( LAtom( "a b c" ) ) )
    }

    " parse the list (c1 (c2 c2) c) " in {
      SExpressionParser.tryParseString( "(c1 (c2 c2) c)" ) must_== Success(
        LFun( "c1", LFun( "c2", LAtom( "c2" ) ), LAtom( "c" ) ) :: Nil
      )
    }

    " parse the list c4;;comment" in {
      SExpressionParser.tryParseString( "c4;;comment" ) must_== Success(
        LAtom( "c4" ) :: Nil
      )
    }

    " parse the comments ;;comment 1<newline>;;comment 2" in {
      SExpressionParser.tryParseString( ";;comment 1\r\n;;comment 2" ) must_== Success( List() )
    }

    " parse the list ;;comment<newline>c5" in {
      SExpressionParser.tryParseString( ";;comment\nc5" ) must_== Success( List( LAtom( "c5" ) ) )
    }

    " parse the list (c1 (c2 c2) c) ;;comment" in {
      SExpressionParser.tryParseString( "(c1 (c2 c2) c);;comment" ) must_== Success(
        LFun( "c1", LFun( "c2", LAtom( "c2" ) ), LAtom( "c" ) ) :: Nil
      )
    }

    " parse the list (c1 (c2 c2)  ;;comment<newline>c)" in {
      SExpressionParser.tryParseString( "(c1 (c2 c2) c);;comment" ) must_== Success(
        LFun( "c1", LFun( "c2", LAtom( "c2" ) ), LAtom( "c" ) ) :: Nil
      )
    }

    " parse the list (c1 \"c2 c2\" c) " in {
      SExpressionParser.tryParseString( "(c1 \"c2 c2\" c)" ) must_== Success(
        List( LFun( "c1", LAtom( "c2 c2" ), LAtom( "c" ) ) )
      )
    }

    " parse the list_ a1 b " in {
      SExpressionParser.tryParseString( "a1 b" ) must_== Success( List( LAtom( "a1" ), LAtom( "b" ) ) )
    }

    " parse the list ;;comment 1\n(c1 (c2 c2)  ;;comment 2\nc)" in {
      SExpressionParser.tryParseString( "(\n;;comment 1\nc1 (c2 c2) c);;comment 2" ) must_== Success(
        List( LFun( "c1", LFun( "c2", LAtom( "c2" ) ), LAtom( "c" ) ) )
      )
    }

    " parse the test file simple.ivy " in {
      val result = ( parseClasspathFile( "simple.ivy" ) )
      result must not beEmpty
      val proof = result.head
      proof match {
        case LList( input1, input2, instantiate8, paramod3, input4, input5, instantiate9, resolve6, resolve7 ) =>
          val pinput1 = IvyParser.parse( LList( input1 ) )
          //debug(pinput1)
          val pinput2 = IvyParser.parse( LList( input2 ) )
          //debug(pinput2)
          val pinput3 = IvyParser.parse( LList( input1, instantiate8 ) )
        //debug(pinput3)

        case _ =>
          //            "The first two rules of simple.ivy must parse correctly" must beEqualTo("failed")
          "The proof in simple.ivy must have 9 inferences" must beEqualTo( "failed" )
      }
      ok
    }

    " parse the test file instantiations.ivy " in {
      val result = ( parseClasspathFile( "instantiations.ivy" ) )
      result must not beEmpty
      val proof = result.head
      proof match {
        case LList( input1, input2, instantiate8, paramod3, input4, input5, instantiate9, resolve6, resolve7, instantiate10 ) =>
          val pinput3 = IvyParser.parse( LList( paramod3, instantiate9 ) )
          //debug(pinput3)
          val pinput4 = IvyParser.parse( LList( instantiate10 ) )
        //debug(pinput4)
        /*
            pinput4 match {
              case Instantiate(id, exp, sub, clause, parent) =>
                "instantiate" must beEqualTo("instantiate")
              case _ =>
                "last inference must be instantiate" must beEqualTo("failed")
            } */

        case _ =>
          //            "The first two rules of simple.ivy must parse correctly" must beEqualTo("failed")
          "The proof in instantiations.ivy must have 9 inferences" must beEqualTo( "failed" )
      }
      ok
    }

    " parse the test file flip.ivy " in {
      val result = ( parseClasspathFile( "flip.ivy" ) )
      result must not beEmpty
      val proof = result.head
      proof match {
        case l @ LList( input0, input1, flip2, input3, para4a, inst6, resolve4 ) =>
          val pinput3 = IvyParser.parse( LList( input1, flip2 ) )
          //debug(pinput3)
          val pinput4 = IvyParser.parse( l )
        //println("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
        //println(pinput4)
        //println("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")

        case LList( list @ _* ) =>
          //println(list)
          //println(list.length)
          "The proof in flip.ivy must have 7, not " + list.length + " inferences" must beEqualTo( "failed" )
        case _ =>
          "The proof in flip.ivy must be a nonempty list" must beEqualTo( "failed" )
      }
      ok
    }

    " parse the test file resulution.ivy " in {
      val result = ( parseClasspathFile( "resolution.ivy" ) )
      result must not beEmpty
      val proof = result.head
      proof match {
        case LList( input1, input2, instantiate8, paramod3, input4, input5, instantiate9, resolve6, resolve7 ) =>
          val pinput = IvyParser.parse( proof )
        //debug("resolution: "+pinput)

        case _ =>
          //            "The first two rules of simple.ivy must parse correctly" must beEqualTo("failed")
          "The proof in resolution.ivy must have 9 inferences" must beEqualTo( "failed" )
      }
      ok
    }

    " parse the test files factor.ivy and factor2.ivy " in {
      val result = ( parseClasspathFile( "factor.ivy" ) )
      result must not beEmpty
      val proof = result.head
      proof match {
        case LList( _* ) =>
          val pinput = IvyParser.parse( proof )
        //debug("resolution: "+pinput)

        case _ =>
          "The proof in factor.ivy must have some inferences" must beEqualTo( "failed" )
      }

      val result2 = ( parseClasspathFile( "factor2.ivy" ) )
      result2 must not beEmpty
      val proof2 = result2.head
      proof2 match {
        case LList( _* ) =>
          val pinput = IvyParser.parse( proof2 )
        //debug("resolution: "+pinput)

        case _ =>
          "The proof in factor.ivy must have some inferences" must beEqualTo( "failed" )
      }
      ok
    }

    " parse the test file manyliterals.ivy " in {
      val result = ( parseClasspathFile( "manyliterals.ivy" ) )
      result must not beEmpty
      val proof = result.head
      proof match {
        case LList( _* ) =>
          val pinput = IvyParser.parse( proof )
        //debug("resolution: "+pinput)

        case _ =>
          //            "The first two rules of simple.ivy must parse correctly" must beEqualTo("failed")
          "The proof in manyliterals.ivy must have some inferences" must beEqualTo( "failed" )
      }
      ok
    }

    " parse the test file simple2.ivy " in {
      val result = ( parseClasspathFile( "simple2.ivy" ) )
      ok
    }
  }

  " parse the test file prime1-0sk.ivy (clause set of the 0 instance of the prime proof) " in {
    val result = ( parseClasspathFile( "prime1-0sk.ivy" ) )
    result must not beEmpty
    val proof = result.head
    proof match {
      case LList( _* ) =>
        val pinput = IvyParser.parse( proof )
      //debug("resolution: "+pinput)

      case _ =>
        //            "The first two rules of simple.ivy must parse correctly" must beEqualTo("failed")
        "The proof in prime1-0sk.ivy must have some inferences" must beEqualTo( "failed" )
    }
    ok
  }

  " parse the test file GRA014+1.ivy " in {
    val result = ( parseClasspathFile( "GRA014+1.ivy" ) )
    result must not beEmpty
    val proof = result.head
    proof match {
      case LList( _* ) =>
        val pinput = IvyParser.parse( proof )
      //debug("resolution: "+pinput)

      case _ =>
        //            "The first two rules of simple.ivy must parse correctly" must beEqualTo("failed")
        "The proof in manyliterals.ivy must have some inferences" must beEqualTo( "failed" )
    }
    ok
  }

  " parse the test file GEO037-2.ivy " in {
    val result = ( parseClasspathFile( "GEO037-2.ivy" ) )
    result must not beEmpty
    val proof = result.head
    proof match {
      case LList( _* ) =>
        val pinput = IvyParser.parse( proof )
      //debug("resolution: "+pinput)

      case _ =>
        //            "The first two rules of simple.ivy must parse correctly" must beEqualTo("failed")
        "The proof in GEO037-2.ivy must have some inferences" must beEqualTo( "failed" )
    }
    ok
  }

  " parse the test file issue221.ivy " in {
    val result = ( parseClasspathFile( "issue221.ivy" ) )
    result must not beEmpty
    val proof = result.head
    proof match {
      case LList( _* ) =>
        val pinput = IvyParser.parse( proof )
      //debug("resolution: "+pinput)

      case _ =>
        //            "The first two rules of simple.ivy must parse correctly" must beEqualTo("failed")
        "The proof in issue221.ivy must have some inferences" must beEqualTo( "failed" )
    }
    ok
  }

}

