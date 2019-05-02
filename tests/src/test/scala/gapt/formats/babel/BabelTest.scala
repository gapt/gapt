package gapt.formats.babel

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Ex
import gapt.expr.formula.Or
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.ty.Ti
import gapt.expr.ty.To
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

  "quoted names" in {
    BabelParser.parse(
      """
        ('\u2200' {i>o}) (^'""' ('""' '\'' : o)) : o
      """ ) must beLike {
        case All( v, App( v_, Const( "'", Ti, Nil ) ) ) if v == v_ => ok
      }
  }

  "associativity" in {
    BabelParser.parse( "a -> b -> c" ) must_== ( FOLAtom( "a" ) --> ( FOLAtom( "b" ) --> FOLAtom( "c" ) ) )
    BabelParser.parse( "a & b & c" ) must_== And( Seq( FOLAtom( "a" ), FOLAtom( "b" ), FOLAtom( "c" ) ) )
    BabelParser.parse( "a | b | c" ) must_== Or( Seq( FOLAtom( "a" ), FOLAtom( "b" ), FOLAtom( "c" ) ) )
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

  "true constant" in {
    hof"#c(true:o)".toString must_== "#c(true: o)"
  }

  "variable and constant literals" in {
    BabelParser.parse( "#c(x : o > o > o) #v(c : o) x" ) must_==
      Apps( Const( "x", To ->: To ->: To ), Var( "c", To ), Var( "x", To ) )
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
      "c = c{}", "c = c{?a}", "c{?a} = c{?b}",
      "∃ 🙋 (🍷 🙋 → ∀ 🙍 (🍷 🙍))",
      "'-2' = (-2)",
      "''",
      "#c('='{nat} : nat>nat>o)",
      "(->) ((x:nat) != 0)",
      "foldr{(nat) (nat)} : (nat>nat>nat) > nat > list nat > nat",
      "^(y:i) #v(y:j)",
      "'\\u0000'",
      "#c(true: o)",
      "'\\\\'", "'\\\\' a", "'^' a b", "'^'",
      "true", "'true'", "'all' x" )
    Fragments.foreach( strings ) { string =>
      string in {
        val expr = BabelParser.parse( string )

        val expr2 = BabelParser.parse( expr.toString )
        require( expr == expr2 )
        expr syntaxEquals expr2 must beTrue

        val expr3 = BabelParser.parse( expr.toAsciiString )
        require( expr == expr3 )
        expr syntaxEquals expr3 must beTrue

        val expr4 = BabelParser.parse( expr.toRawString )
        require( expr == expr4 )
        expr syntaxEquals expr4 must beTrue
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
