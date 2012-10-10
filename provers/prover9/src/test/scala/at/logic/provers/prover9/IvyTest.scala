package at.logic.provers.prover9

import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mutable.SpecificationWithJUnit
import collection.immutable
import at.logic.provers.prover9.Ivy.IvyParser
import java.io.File.separator
import util.parsing.input.Reader

/**
 * Test for the Ivy interface.
 */
@RunWith(classOf[JUnitRunner])
class IvyTest extends SpecificationWithJUnit {
  def dumpreader[T](r:Reader[T]) = {
    var reader = r
    println("=== dumping reader! ===")
    while (! reader.atEnd) {
      print(reader.first)
      reader = reader.rest
    }
    println()
  }

  "The Ivy Parser " should {
       " parse an empty list " in {
         val parser = new Ivy.IvyParser
         parser.parseAll(parser.list,"()") match {
           case parser.Success(result, rest) =>
//             println("parsing ok!")
             true must beEqualTo(true)
           case parser.NoSuccess(msg, rest) =>
//             println("parser failed: "+msg)
             true must beEqualTo(false)
         }
       }

    " parse the atom a1" in {
      val parser = new Ivy.IvyParser
      parser.parseAll(parser.atom,"a1") match {
        case parser.Success(result, rest) =>
//          println("parsing ok!")
          true must beEqualTo(true)
        case parser.NoSuccess(msg, rest) =>
//          println("parser failed: "+msg)
          true must beEqualTo(false)
      }
    }

    " parse the atom a2(space)" in {
      //this test passes because regexpparsers strip whitespace!
      val parser = new Ivy.IvyParser
      parser.parseAll(parser.word  ,"a2    ") match {
        case parser.Success(result, rest) =>
          //          println("parsing ok!)
          true must beEqualTo(true)
        case parser.NoSuccess(msg, rest) =>
          //          println("parsing wrong!")
          true must beEqualTo(false)
      }
    }

    """ parse the atom "a b c" """ in {
      //this test passes because regexpparsers strip whitespace!
      val parser = new Ivy.IvyParser
      parser.parseAll(parser.string ,""""a b c"""") match {
        case parser.Success(result, rest) =>
          //          println("parsing ok!)
          true must beEqualTo(true)
        case parser.NoSuccess(msg, rest) =>
          //          println("parsing wrong!")
          true must beEqualTo(false)
      }
    }


    " parse the list (c1 (c2 c2) c) " in {
        val parser = new Ivy.IvyParser
      parser.parseAll(parser.list,"(c1 (c2 c2) c)") match {
        case parser.Success(result, rest) =>
          result match {
            case Lisp.List(Lisp.Atom("c1")::
                           Lisp.List(Lisp.Atom("c2"):: Lisp.Atom("c2"):: Nil)::
                           Lisp.Atom("c")::Nil) =>
              "matched correct list" must beEqualTo("matched correct list")
            case _ =>
              println(result)
              dumpreader(rest)
              "matched correct list" must beEqualTo("failed")
          }
        case parser.NoSuccess(msg, rest) =>
          "parser returned success" must beEqualTo("failed")
      }
    }


    " parse the list c4;;comment" in {
      val parser = new Ivy.IvyParser
      parser.parseAll(parser.sexpression,"c4;;comment") match {
        case parser.Success(result, rest) =>
          result match {
            case Lisp.Atom("c4") =>
              "matched correct list" must beEqualTo("matched correct list")
            case _ =>
              println(result)
              "matched correct list" must beEqualTo("failed")
          }
        case parser.NoSuccess(msg, rest) =>
          "parser returned success" must beEqualTo("failed")
      }
    }

    " parse the comments ;;comment 1\n;;comment 2" in {
      val parser = new Ivy.IvyParser
      parser.parseAll(parser.comments,";;comment 1\n;;comment 2\n") match {
        case parser.Success(result, rest) =>
          result match {
            case ";;comment 1;;comment 2" =>
              "matched correct list" must beEqualTo("matched correct list")
            case _ =>
              println("correct result:")
              println(result)
              "matched correct list" must beEqualTo("failed")
          }
        case parser.NoSuccess(msg, rest) =>
          println(msg)
          dumpreader(rest)
          "parser returned success" must beEqualTo("failed")
      }
    }

    " parse the list ;;comment\nc5" in {
      println(" parse the list ;;comment\nc5")
      val parser = new Ivy.IvyParser
      parser.parseAll(parser.sexpression,";;comment\nc5") match {
        case parser.Success(result, rest) =>
          result match {
            case Lisp.Atom("c5") =>
              "matched correct list" must beEqualTo("matched correct list")
            case _ =>
              println(result)
              "matched correct list" must beEqualTo("failed")
          }
        case parser.NoSuccess(msg, rest) =>
          println(msg)
          dumpreader(rest)
          "parser returned success" must beEqualTo("failed")
      }
    }

    " parse the list (c1 (c2 c2) c) ;;comment" in {
      val parser = new Ivy.IvyParser
      parser.parseAll(parser.sexpression,"(c1 (c2 c2) c);;comment") match {
        case parser.Success(result, rest) =>
          result match {
            case Lisp.List(Lisp.Atom("c1")::
              Lisp.List(Lisp.Atom("c2"):: Lisp.Atom("c2"):: Nil)::
              Lisp.Atom("c")::Nil) =>
              "matched correct list" must beEqualTo("matched correct list")
            case _ =>
              println(result)
              "matched correct list" must beEqualTo("failed")
          }
        case parser.NoSuccess(msg, rest) =>
          "parser returned success" must beEqualTo("failed")
      }
    }

    " parse the list (c1 (c2 c2)  ;;comment\nc)" in {
      val parser = new Ivy.IvyParser
      parser.parseAll(parser.sexpression,"(c1 (c2 c2) c);;comment") match {
        case parser.Success(result, rest) =>
          result match {
            case Lisp.List(Lisp.Atom("c1")::
              Lisp.List(Lisp.Atom("c2"):: Lisp.Atom("c2"):: Nil)::
              Lisp.Atom("c")::Nil) =>
              "matched correct list" must beEqualTo("matched correct list")
            case _ =>
              println(result)
              "matched correct list" must beEqualTo("failed")
          }
        case parser.NoSuccess(msg, rest) =>
          "parser returned success" must beEqualTo("failed")
      }
    }


    " parse the list (c1 \"c2 c2\" c) " in {
      val parser = new Ivy.IvyParser
      parser.parseAll(parser.sexpression,"(c1 \"c2 c2\" c)") match {
        case parser.Success(result, rest) =>
          //          println("parsing ok!")
          true must beEqualTo(true)
        case parser.NoSuccess(msg, rest) =>
          //          println("parser failed: "+msg)
          true must beEqualTo(false)
      }
    }


    " parse the list_ a1 b " in {
      val parser = new Ivy.IvyParser
      parser.parseAll(parser.list_,"a1 b") match {
        case parser.Success(result, rest) =>
//          println("parsing ok!")
          true must beEqualTo(true)
        case parser.NoSuccess(msg, rest) =>
//          println("parser failed: "+msg)
          true must beEqualTo(false)
      }
    }

    " parse the list ;;comment 1\n(c1 (c2 c2)  ;;comment 2\nc)" in {
      val parser = new Ivy.IvyParser
      parser.parseAll(parser.lisp_file, "(\n;;comment 1\nc1 (c2 c2) c);;comment 2") match {
        case parser.Success(result, rest) =>
          result match {
            case Lisp.List(Lisp.Atom("c1")::
              Lisp.List(Lisp.Atom("c2"):: Lisp.Atom("c2"):: Nil)::
              Lisp.Atom("c")::Nil) :: Nil =>
              "matched correct list" must beEqualTo("matched correct list")
            case _ =>
              println(result)
              dumpreader(rest)
              "matched correct list" must beEqualTo("failed")
          }
        case parser.NoSuccess(msg, rest) =>
          println(msg)
          dumpreader(rest)
          "parser returned success" must beEqualTo("failed")
      }
    }


    " parse the test file simple.ivy " in {
      try {
        val result = IvyParser("target" + separator + "test-classes" + separator +"simple.ivy")
        true must beEqualTo(true)
      } catch {
        case e:Exception =>
        println("Exception parsing simple.ivy: "+e.getMessage)
        true must beEqualTo(false)

      }
    }

    " parse the test file simple2.ivy " in {
      try {
        val result = IvyParser("target" + separator + "test-classes" + separator +"simple2.ivy")
        true must beEqualTo(true)
      } catch {
        case e:Exception =>
          println("Exception parsing simple.ivy: "+e.getMessage)
          true must beEqualTo(false)

      }
    }
  }


}