package at.logic.gapt.formats.babel

import at.logic.gapt.expr._
import org.specs2.mutable.Specification
import org.specs2.specification.core.Fragments

class BabelTest extends Specification {

  "hol impl" in {
    val x = Var( "x", To )
    BabelParser.parse( "x -> x" ) must_== ( x --> x )
  }

  "many sorted quant" in {
    BabelParser.parse( "!P ?(x:Nat) !y P x y" ) must beLike {
      case All( p, Ex( _, All( _, Apps( p_, _ ) ) ) ) => p must_== p_
    }
  }

  "equation chain" in {
    BabelParser.parse( "!P ?x !y P x y + 1 = y = P(x)(y) + 1 = P(x,y) + 1" ) must beLike {
      case All( _, Ex( _, All( _, _ ) ) ) => ok
    }
  }

  "quoted names" in {
    BabelParser.parse(
      """
        '\u2200' (^'""' ('""' '\'' : o)) : o
      """ ) must beLike {
        case All( v, App( v_, Const( "'", Ti ) ) ) if v == v_ => ok
      }
  }

  "quantifiers bind more closely than disjunction" in {
    BabelParser.parse( "?x P(x) | Q(x)" ) must beLike {
      case Or( Ex( _, _ ), _ ) => ok
    }
  }

  "unicode connectives" in {
    BabelParser.parse( "∃x P(x) ∨ Q(x)" ) must beLike {
      case Or( Ex( _, _ ), _ ) => ok
    }
  }

  "variable and constant literals" in {
    BabelParser.parse( "#c(x : o > o > o) #v(c : o) x" ) must_==
      Apps( Const( "x", To -> ( To -> To ) ), Var( "c", To ), Var( "x", To ) )
  }

  "round-trip safety" in {
    val strings = Seq(
      "#c(x : o > o > o) #v(c : o) x",
      "(qrev(qrev(x, nil), nil): list) = x",
      "(qrev(qrev(x, nil), nil: list): list) = x",
      "!a?b a(b,c)",
      "(a:t1) + (b:t2) : t3",
      "(a:t1) <= (b:t2) < (c:t3) = (d:t3)",
      "(a:i)+(b:i)=a & #c('+':t>t>t) c d = d",
      "(a:t1) <= b & #c('<=':t2>t3>o) b c",
      "(x*y)*z = x*(y*z)",
      "'<=' x y : i",
      "true & p(#c('⊤': i))",
      "^('⊤': i) #c('⊤': o) & p('⊤': i)",
      "''",
      "'\\u0000'",
      "true", "'true'", "'all' x" )
    Fragments.foreach( strings ) { string =>
      string in {
        val expr = BabelParser.parse( string )

        val expr2 = BabelParser.parse( expr.toString )
        expr syntaxEquals expr2 must beTrue

        val expr3 = BabelParser.parse( expr.toAsciiString )
        expr syntaxEquals expr3 must beTrue
      }
    }
  }

  "correct ascii conversion" in {
    val strings = Seq( "ößfð", "'fßðf fßð'", "^z!x?y (true & false & x -> y & -z | x & x!=x)", "'\\u0000'" )
    Fragments.foreach( strings ) { string =>
      string in {
        val expr = BabelParser parse string
        expr.toAsciiString must beMatching( """\p{ASCII}+""".r )
      }
    }
  }

  "limited llk compatibility" in {
    val formulas = Seq(
      "p(X)", "A", "-p(y)", "-p(Y)",
      "P(X)", "a", "-P(y)", "-P(Y)",
      "P(x) & P(b)", "q(x) &q(x) & p(y)", "A&B", "X&Y&Z",
      "(P(x) & P(b))", "(q(x) &q(x) & p(y))", "(A&B)", "(X&Y&Z)",
      "q(x) &(q(x) & p(y))", "(X&Y)&Z",
      "p(X)", "A", "-p(y)", "-p(Y)",
      "P(X)", "a", "-P(y)", "-P(Y)",
      "P(x) & P(b)", "q(x) &q(x) & p(y)", "A&B", "X&Y&Z",
      "(P(x) & P(b))", "(q(x) &q(x) & p(y))", "(A&B)", "(X&Y&Z)",
      "P(x) | P(b)", "q(x) |q(x) | p(y)", "A|B", "X|Y|Z",
      "(P(x) | P(b))", "(q(x) |q(x) | p(y))", "(A|B)", "(X|Y|Z)",
      "P(x) -> P(b)", "A->B", "X->Y->Z", "q(x) ->q(x) -> p(y)",
      "(P(x) -> P(b))", "(A->B)", "(X->Y->Z)", "(q(x) ->q(x) -> p(y))",
      "P(x) <-> P(b)", "A<->B", "X<->Y<->Z", "q(x) <->q(x) <-> p(y)",
      "(P(x) <-> P(b))", "(A<->B)", "(X<->Y<->Z)", "(q(x) <->q(x) <-> p(y))",
      "q(x) &(q(x) & p(y))", "(X&Y)&Z",
      "a = b", "1+X", "1+(X*2)", "P(1+(X*2))", "f(1+X)= (X*0)+X" )

    formulas foreach BabelParser.parse

    ok
  }

}
