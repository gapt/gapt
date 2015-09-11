package at.logic.gapt.formats.ivy

import at.logic.gapt.utils.testing.ClasspathFileCopier
import org.specs2.mutable._
import at.logic.gapt.formats.lisp
import java.io.File.separator
import util.parsing.input.Reader
import lisp.{ SExpressionParser }

/**
 * Test for the Ivy interface.
 */
class IvyTest extends Specification with ClasspathFileCopier {
  val nLine = sys.props( "line.separator" )

  def dumpreader[T]( r: Reader[T] ) = {
    var reader = r
    println( "=== dumping reader! ===" )
    while ( !reader.atEnd ) {
      print( reader.first )
      reader = reader.rest
    }
    println()
  }

  def debug( s: String ) = {} //{println("Debug: "+s)}

  sequential
  "The Ivy Parser " should {
    " parse an empty list " in {
      val parser = new SExpressionParser
      parser.parse( "()" ) match {
        case parser.Success( result, rest ) =>
          debug( "parsing ok!" )
          "parsing ok!" must beEqualTo( "parsing ok!" )
        case parser.NoSuccess( msg, rest ) =>
          debug( "parser failed: " + msg + " at " + rest.pos )
          "msg: " + msg must beEqualTo( "failed" )
      }
    }

    " not parse an empty list + garbage" in {
      val parser = new SExpressionParser
      parser.parse( "())" ) match {
        case parser.Success( result, rest ) =>
          debug( "parsing ok!" )
          "parsing ok! " + result must beEqualTo( "fail!" )
        case parser.NoSuccess( msg, rest ) =>
          debug( "correctly failed!" )
          "parsing failed as expected" must beEqualTo( "parsing failed as expected" )
      }
    }

    " parse the atom a1" in {
      val parser = new SExpressionParser
      parser.parse( "a1" ) match {
        case parser.Success( result, rest ) =>
          debug( "parsing ok!" )
          "parsing ok!" must beEqualTo( "parsing ok!" )
        case parser.NoSuccess( msg, rest ) =>
          debug( "parser failed: " + msg )
          "msg: " + msg must beEqualTo( "failed" )
      }
    }

    " parse the atom a2(space)" in {
      //this test passes because regexpparsers strip whitespace!
      val parser = new SExpressionParser
      parser.parse( "a2    " ) match {
        case parser.Success( result, rest ) =>
          debug( "parsing ok!" )
          true must beEqualTo( true )
        case parser.NoSuccess( msg, rest ) =>
          debug( "parsing wrong! " + msg )
          true must beEqualTo( false )
      }
    }

    """ parse the atom "a b c" """ in {
      //this test passes because regexpparsers strip whitespace!
      val parser = new SExpressionParser
      parser.parse( """"a b c"""" ) match {
        case parser.Success( result, rest ) =>
          debug( "parsing ok!" )
          true must beEqualTo( true )
        case parser.NoSuccess( msg, rest ) =>
          debug( "parsing wrong! " + msg )
          true must beEqualTo( false )
      }
    }

    " parse the list (c1 (c2 c2) c) " in {
      val parser = new SExpressionParser
      parser.parse( "(c1 (c2 c2) c)" ) match {
        case parser.Success( result, rest ) =>
          result match {
            case lisp.List( lisp.Atom( "c1" ) ::
              lisp.List( lisp.Atom( "c2" ) :: lisp.Atom( "c2" ) :: Nil ) ::
              lisp.Atom( "c" ) :: Nil ) :: Nil =>
              "matched correct list" must beEqualTo( "matched correct list" )
            case _ =>
              //debug(result)
              //dumpreader(rest)
              "matched correct list " + result must beEqualTo( "failed" )
          }
        case parser.NoSuccess( msg, rest ) =>
          "parser returned success " + msg must beEqualTo( "failed" )
      }
    }

    " parse the list c4;;comment" in {
      val parser = new SExpressionParser
      parser.parse( "c4;;comment" ) match {
        case parser.Success( result, rest ) =>
          result match {
            case lisp.Atom( "c4" ) :: Nil =>
              "matched correct list" must beEqualTo( "matched correct list" )
            case _ =>
              //debug(result)
              "matched correct list" must beEqualTo( "failed" )
          }
        case parser.NoSuccess( msg, rest ) =>
          "parser returned success" must beEqualTo( "failed" )
      }
    }

    " parse the comments ;;comment 1" + nLine + ";;comment 2" in {
      val parser = new SExpressionParser
      parser.parse( ";;comment 1" + nLine + ";;comment 2" + nLine ) match {
        case parser.Success( result, rest ) =>
          result match {
            case Nil =>
              "matched correct list" must beEqualTo( "matched correct list" )
            case _ =>
              //debug("correct result:")
              //debug(result)
              "matched correct list" must beEqualTo( "failed" )
          }
        case parser.NoSuccess( msg, rest ) =>
          //debug(msg)
          //dumpreader(rest)
          "parser returned success" must beEqualTo( "failed" )
      }
    }

    " parse the list ;;comment" + nLine + "c5" in {
      //debug(" parse the list ;;comment\nc5")
      val parser = new SExpressionParser
      parser.parse( ";;comment" + nLine + "c5" ) match {
        case parser.Success( result, rest ) =>
          result match {
            case lisp.Atom( "c5" ) :: Nil =>
              "matched correct list" must beEqualTo( "matched correct list" )
            case _ =>
              //debug(result)
              "matched correct list " + result must beEqualTo( "failed" )
          }
        case parser.NoSuccess( msg, rest ) =>
          //debug(msg)
          //dumpreader(rest)
          "parser returned success " + msg must beEqualTo( "failed" )
      }
    }

    " parse the list (c1 (c2 c2) c) ;;comment" in {
      val parser = new SExpressionParser
      parser.parse( "(c1 (c2 c2) c);;comment" ) match {
        case parser.Success( result, rest ) =>
          result match {
            case lisp.List( lisp.Atom( "c1" ) ::
              lisp.List( lisp.Atom( "c2" ) :: lisp.Atom( "c2" ) :: Nil ) ::
              lisp.Atom( "c" ) :: Nil ) :: Nil =>
              "matched correct list" must beEqualTo( "matched correct list" )
            case _ =>
              //debug(result)
              "matched correct list " + result must beEqualTo( "failed" )
          }
        case parser.NoSuccess( msg, rest ) =>
          "parser returned success" + msg must beEqualTo( "failed" )
      }
    }

    " parse the list (c1 (c2 c2)  ;;comment" + nLine + "c)" in {
      val parser = new SExpressionParser
      parser.parse( "(c1 (c2 c2) c);;comment" ) match {
        case parser.Success( result, rest ) =>
          result match {
            case lisp.List( lisp.Atom( "c1" ) ::
              lisp.List( lisp.Atom( "c2" ) :: lisp.Atom( "c2" ) :: Nil ) ::
              lisp.Atom( "c" ) :: Nil ) :: Nil =>
              "matched correct list" must beEqualTo( "matched correct list" )
            case _ =>
              //debug(result)
              "matched correct list " + result must beEqualTo( "failed" )
          }
        case parser.NoSuccess( msg, rest ) =>
          "parser returned success" + msg must beEqualTo( "failed" )
      }
    }

    " parse the list (c1 \"c2 c2\" c) " in {
      val parser = new SExpressionParser
      parser.parse( "(c1 \"c2 c2\" c)" ) match {
        case parser.Success( result, rest ) =>
          //          debug("parsing ok!")
          true must beEqualTo( true )
        case parser.NoSuccess( msg, rest ) =>
          //          debug("parser failed: "+msg)
          true must beEqualTo( false )
      }
    }

    " parse the list_ a1 b " in {
      val parser = new SExpressionParser
      parser.parse( "a1 b" ) match {
        case parser.Success( result, rest ) =>
          //          debug("parsing ok!")
          true must beEqualTo( true )
        case parser.NoSuccess( msg, rest ) =>
          //          debug("parser failed: "+msg)
          true must beEqualTo( false )
      }
    }

    " parse the list ;;comment 1" + nLine + "(c1 (c2 c2)  ;;comment 2" + nLine + "c)" in {
      val parser = new SExpressionParser
      parser.parse( "(" + nLine + ";;comment 1" + nLine + "c1 (c2 c2) c);;comment 2" ) match {
        case parser.Success( result, rest ) =>
          result match {
            case lisp.List( lisp.Atom( "c1" ) ::
              lisp.List( lisp.Atom( "c2" ) :: lisp.Atom( "c2" ) :: Nil ) ::
              lisp.Atom( "c" ) :: Nil ) :: Nil =>
              "matched correct list" must beEqualTo( "matched correct list" )
            case _ =>
              //debug(result)
              //dumpreader(rest)
              "matched correct list" must beEqualTo( "failed" )
          }
        case parser.NoSuccess( msg, rest ) =>
          //debug(msg)
          //dumpreader(rest)
          "parser returned success" must beEqualTo( "failed" )
      }
    }

    " parse the test file simple.ivy " in {
      val result = SExpressionParser( tempCopyOfClasspathFile( "simple.ivy" ) )
      result must not beEmpty
      val proof = result.head
      proof match {
        case lisp.List( input1 :: input2 :: instantiate8 :: paramod3 :: input4 :: input5 :: instantiate9 :: resolve6 :: resolve7 :: Nil ) =>
          val pinput1 = IvyParser.parse( lisp.List( input1 :: Nil ) )
          //debug(pinput1)
          val pinput2 = IvyParser.parse( lisp.List( input2 :: Nil ) )
          //debug(pinput2)
          val pinput3 = IvyParser.parse( lisp.List( input1 :: instantiate8 :: Nil ) )
        //debug(pinput3)

        case _ =>
          //            "The first two rules of simple.ivy must parse correctly" must beEqualTo("failed")
          "The proof in simple.ivy must have 9 inferences" must beEqualTo( "failed" )
      }
      ok
    }

    " parse the test file instantiations.ivy " in {
      val result = SExpressionParser( tempCopyOfClasspathFile( "instantiations.ivy" ) )
      result must not beEmpty
      val proof = result.head
      proof match {
        case lisp.List( input1 :: input2 :: instantiate8 :: paramod3 :: input4 :: input5 :: instantiate9 :: resolve6 :: resolve7 :: instantiate10 :: Nil ) =>
          val pinput3 = IvyParser.parse( lisp.List( paramod3 :: instantiate9 :: Nil ) )
          //debug(pinput3)
          val pinput4 = IvyParser.parse( lisp.List( instantiate10 :: Nil ) )
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
      val result = SExpressionParser( tempCopyOfClasspathFile( "flip.ivy" ) )
      result must not beEmpty
      val proof = result.head
      proof match {
        case l @ lisp.List( input0 :: input1 :: flip2 :: input3 :: para4a :: inst6 :: resolve4 :: Nil ) =>
          val pinput3 = IvyParser.parse( lisp.List( input1 :: flip2 :: Nil ) )
          //debug(pinput3)
          val pinput4 = IvyParser.parse( l )
        //println("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
        //println(pinput4)
        //println("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")

        case lisp.List( list ) =>
          //println(list)
          //println(list.length)
          "The proof in flip.ivy must have 7, not " + list.length + " inferences" must beEqualTo( "failed" )
        case _ =>
          "The proof in flip.ivy must be a nonempty list" must beEqualTo( "failed" )
      }
      ok
    }

    " parse the test file resulution.ivy " in {
      val result = SExpressionParser( tempCopyOfClasspathFile( "resolution.ivy" ) )
      result must not beEmpty
      val proof = result.head
      proof match {
        case lisp.List( input1 :: input2 :: instantiate8 :: paramod3 :: input4 :: input5 :: instantiate9 :: resolve6 :: resolve7 :: Nil ) =>
          val pinput = IvyParser.parse( proof )
        //debug("resolution: "+pinput)

        case _ =>
          //            "The first two rules of simple.ivy must parse correctly" must beEqualTo("failed")
          "The proof in resolution.ivy must have 9 inferences" must beEqualTo( "failed" )
      }
      ok
    }

    " parse the test files factor.ivy and factor2.ivy " in {
      val result = SExpressionParser( tempCopyOfClasspathFile( "factor.ivy" ) )
      result must not beEmpty
      val proof = result.head
      proof match {
        case lisp.List( _ ) =>
          val pinput = IvyParser.parse( proof )
        //debug("resolution: "+pinput)

        case _ =>
          "The proof in factor.ivy must have some inferences" must beEqualTo( "failed" )
      }

      val result2 = SExpressionParser( tempCopyOfClasspathFile( "factor2.ivy" ) )
      result2 must not beEmpty
      val proof2 = result2.head
      proof2 match {
        case lisp.List( _ ) =>
          val pinput = IvyParser.parse( proof2 )
        //debug("resolution: "+pinput)

        case _ =>
          "The proof in factor.ivy must have some inferences" must beEqualTo( "failed" )
      }
      ok
    }

    " parse the test file manyliterals.ivy " in {
      val result = SExpressionParser( tempCopyOfClasspathFile( "manyliterals.ivy" ) )
      result must not beEmpty
      val proof = result.head
      proof match {
        case lisp.List( _ ) =>
          val pinput = IvyParser.parse( proof )
        //debug("resolution: "+pinput)

        case _ =>
          //            "The first two rules of simple.ivy must parse correctly" must beEqualTo("failed")
          "The proof in manyliterals.ivy must have some inferences" must beEqualTo( "failed" )
      }
      ok
    }

    " parse the test file simple2.ivy " in {
      val result = SExpressionParser( tempCopyOfClasspathFile( "simple2.ivy" ) )
      ok
    }
  }

  " parse the test file prime1-0sk.ivy (clause set of the 0 instance of the prime proof) " in {
    val result = SExpressionParser( tempCopyOfClasspathFile( "prime1-0sk.ivy" ) )
    result must not beEmpty
    val proof = result.head
    proof match {
      case lisp.List( _ ) =>
        val pinput = IvyParser.parse( proof )
      //debug("resolution: "+pinput)

      case _ =>
        //            "The first two rules of simple.ivy must parse correctly" must beEqualTo("failed")
        "The proof in prime1-0sk.ivy must have some inferences" must beEqualTo( "failed" )
    }
    ok
  }

  " parse the test file GRA014+1.ivy " in {
    val result = SExpressionParser( tempCopyOfClasspathFile( "GRA014+1.ivy" ) )
    result must not beEmpty
    val proof = result.head
    proof match {
      case lisp.List( _ ) =>
        val pinput = IvyParser.parse( proof )
      //debug("resolution: "+pinput)

      case _ =>
        //            "The first two rules of simple.ivy must parse correctly" must beEqualTo("failed")
        "The proof in manyliterals.ivy must have some inferences" must beEqualTo( "failed" )
    }
    ok
  }

  " parse the test file GEO037-2.ivy " in {
    val result = SExpressionParser( tempCopyOfClasspathFile( "GEO037-2.ivy" ) )
    result must not beEmpty
    val proof = result.head
    proof match {
      case lisp.List( _ ) =>
        val pinput = IvyParser.parse( proof )
      //debug("resolution: "+pinput)

      case _ =>
        //            "The first two rules of simple.ivy must parse correctly" must beEqualTo("failed")
        "The proof in GEO037-2.ivy must have some inferences" must beEqualTo( "failed" )
    }
    ok
  }

  " parse the test file issue221.ivy " in {
    val result = SExpressionParser( tempCopyOfClasspathFile( "issue221.ivy" ) )
    result must not beEmpty
    val proof = result.head
    proof match {
      case lisp.List( _ ) =>
        val pinput = IvyParser.parse( proof )
      //debug("resolution: "+pinput)

      case _ =>
        //            "The first two rules of simple.ivy must parse correctly" must beEqualTo("failed")
        "The proof in issue221.ivy must have some inferences" must beEqualTo( "failed" )
    }
    ok
  }

}

