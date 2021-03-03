package gapt.formats.leancop

import gapt.expr._
import gapt.expr.formula.Iff
import gapt.formats.ClasspathInputFile
import gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class LeanCoPParserTest extends Specification with SatMatchers {

  "parse conjunctions and disjunctions left associatively" in {
    LeanCoPParser.parseAll(
      LeanCoPParser.formula,
      "'A' & 'B' & 'C'" ) match {
        case LeanCoPParser.Success( f, _ ) =>
          f must_== fof"(A & B) & C"
        case _ => failure
      }
    LeanCoPParser.parseAll(
      LeanCoPParser.formula,
      "'A' | 'B' | 'C'" ) match {
        case LeanCoPParser.Success( f, _ ) =>
          f must_== fof"(A | B) | C"
        case _ => failure
      }
    ok
  }

  "conjunctions bind stronger than disjunctions" in {
    LeanCoPParser.parseAll(
      LeanCoPParser.formula,
      "'A' & 'B' & 'C' | 'D'" ) match {
        case LeanCoPParser.Success( f, _ ) =>
          f must_== fof"((A & B) & C) | D"
        case _ => failure
      }
    ok
  }

  "parse implications right associatively" in {
    LeanCoPParser.parseAll(
      LeanCoPParser.formula,
      "'A' => 'B' => 'C'" ) match {
        case LeanCoPParser.Success( f, _ ) =>
          f must_== fof"A -> (B -> C)"
        case _ => failure
      }
    ok
  }

  "implications bind stronger than biconditionals" in {
    LeanCoPParser.parseAll( LeanCoPParser.formula, "'A' <=> 'B' => 'C'" ) match {
      case LeanCoPParser.Success( f, _ ) =>
        f must_== fof"A <-> (B -> C)"
      case _ => failure
    }
    ok
  }

  "parse biconditional to two implications" in {
    LeanCoPParser.parseAll( LeanCoPParser.formula, "'P' <=> 'Q'" ) match {
      case LeanCoPParser.Success( f, _ ) =>
        f must_== fof"P <-> Q"
      case _ => failure
    }
    ok
  }

  "parse universally quantified formula" in {
    LeanCoPParser.parseAll( LeanCoPParser.quantified, "! [_X, _Y] : ('P'(_X, _Y))" ) match {
      case LeanCoPParser.Success( f, _ ) =>
        f must_== fof"!x !y #c(P:i>i>o)(x,y)"
      case _ => failure
    }
    ok
  }

  "parse existentially quantified formula" in {
    LeanCoPParser.parseAll( LeanCoPParser.quantified, "? [_X, _Y] : ('P'(_X, _Y))" ) match {
      case LeanCoPParser.Success( f, _ ) =>
        f must_== fof"?x ?y #c(P:i>i>o)(x,y)"
      case _ => failure
    }
    ok
  }

  "parse negation" in {
    LeanCoPParser.parseAll( LeanCoPParser.formula, "- 'P'" ) match {
      case LeanCoPParser.Success( f, _ ) =>
        f must_== fof"- #c(P:o)"
      case _ => failure
    }
    ok
  }

  "parse clause" in {
    LeanCoPParser.parseAll( LeanCoPParser.clause, "[-'A', 'B', 'C']" ) match {
      case LeanCoPParser.Success( f, _ ) =>
        f must_== fos"A :- B, C"
      case e => failure( e.toString )
    }
    ok
  }

  "parse clause with superfluous parentheses" in {
    LeanCoPParser.parseAll( LeanCoPParser.clause, "[-('A'), 'B', 'C']" ) match {
      case LeanCoPParser.Success( f, _ ) =>
        f must_== fos"A :- B, C"
      case e => failure( e.toString )
    }
    LeanCoPParser.parseAll( LeanCoPParser.clause, "[(-'A'), 'B', 'C']" ) match {
      case LeanCoPParser.Success( f, _ ) =>
        f must_== fos"A :- B, C"
      case e => failure( e.toString )
    }
    ok
  }

  "irrationals" in {
    LeanCoPParser.getExpansionProof( ClasspathInputFile( "irrationals.leancop.s" ) ) must beLike {
      case Some( expansion ) =>
        expansion.deep must beEValidSequent
    }
  }

}
