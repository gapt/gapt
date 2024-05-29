package gapt.formats.prover9

import org.specs2.mutable._
import gapt.expr._
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFunction

class Prover9ParserTest extends Specification {
  "The Prover9 language parser" should {
    "handle conjunctions and atoms" in {
      List(
        "p(X)",
        "A",
        "-p(y)",
        "-p(Y)",
        "P(X)",
        "a",
        "-P(y)",
        "-P(Y)",
        "P(x) & P(b)",
        "q(x) &q(x) & p(y)",
        "A&B",
        "X&Y&Z",
        "(P(x) & P(b))",
        "(q(x) &q(x) & p(y))",
        "(A&B)",
        "(X&Y&Z)",
        "q(x) &(q(x) & p(y))",
        "(X&Y)&Z"
      ) map { s =>
        Prover9TermParser.parseFormula(s)
        ok
      }
    }

    "handle simple formulas" in {
      List(
        "p(X)",
        "A",
        "-p(y)",
        "-p(Y)",
        "P(X)",
        "a",
        "-P(y)",
        "-P(Y)",
        "P(x) & P(b)",
        "q(x) &q(x) & p(y)",
        "A&B",
        "X&Y&Z",
        "(P(x) & P(b))",
        "(q(x) &q(x) & p(y))",
        "(A&B)",
        "(X&Y&Z)",
        "P(x) | P(b)",
        "q(x) |q(x) | p(y)",
        "A|B",
        "X|Y|Z",
        "(P(x) | P(b))",
        "(q(x) |q(x) | p(y))",
        "(A|B)",
        "(X|Y|Z)",
        "P(x) -> P(b)",
        "A->B", // "X->Y->Z", "q(x) ->q(x) -> p(y)",
        "(P(x) -> P(b))",
        "(A->B)", // "(X->Y->Z)", "(q(x) ->q(x) -> p(y))",
        "P(x) <- P(b)",
        "A<-B", // "X<-Y<-Z", , "q(x) <-q(x) <- p(y)"
        "(P(x) <- P(b))",
        "(A<-B)", // "(X<-Y<-Z)", "(q(x) <-q(x) <- p(y))",
        "P(x) <-> P(b)",
        "A<->B", // "X<->Y<->Z", "q(x) <->q(x) <-> p(y)",
        "(P(x) <-> P(b))",
        "(A<->B)", // "(X<->Y<->Z)", "(q(x) <->q(x) <-> p(y))",
        "q(x) &(q(x) & p(y))",
        "(X&Y)&Z",
        "(all X p(X))",
        "(exists X p(X))",
        "-(all X p(X))",
        "-(exists X p(X))",
        "-(all X --p(X))",
        "--(exists X p(X))"
      ) map { s =>
        Prover9TermParser.parseFormula(s)
        ok
      }
    }

    "handle complex formulas" in {
      List(
        "(all X (P(X) & Q(X)))",
        "(all X (P(X) & Q(X) & R(X,X)))",
        "(exists X (P(X) & Q(X)))",
        "(exists X (P(X) & Q(X) & R(X,X)))",
        "(all X (P(X) | Q(X)))",
        "(all X (P(X) | Q(X) | R(X,X)))",
        "(exists X (P(X) | Q(X)))",
        "(exists X (P(X) | Q(X) | R(X,X)))",
        "(all X (q(X,f(X)) | q(X,g(X))))"
      ) map { s =>
        Prover9TermParser.parseFormula(s)
        ok
      }
    }

    "goat puzzle endsequent" in {
      val oendsequent =
        """p(south,south,south,south,start) &
          | (all T (p(south,north,south,north,T) -> p(north,north,south,north,go_alone(T)))) &
          | (all T1 (p(north,north,south,north,T1) -> p(south,north,south,north,go_alone(T1)))) &
          | (all T2 (p(south,south,north,south,T2) -> p(north,south,north,south,go_alone(T2)))) &
          | (all T3 (p(north,south,north,south,T3) -> p(south,south,north,south,go_alone(T3)))) &
          | (all T4 (p(south,south,south,north,T4) -> p(north,north,south,north,take_wolf(T4)))) &
          | (all T5 (p(north,north,south,north,T5) -> p(south,south,south,north,take_wolf(T5)))) &
          | (all T6 (p(south,south,north,south,T6) -> p(north,north,north,south,take_wolf(T6)))) &
          | (all T7 (p(north,north,north,south,T7) -> p(south,south,north,south,take_wolf(T7)))) &
          | (all X all Y all U (p(south,X,south,Y,U) -> p(north,X,north,Y,take_goat(U)))) &
          | (all X1 all Y1 all V (p(north,X1,north,Y1,V) -> p(south,X1,south,Y1,take_goat(V)))) &
          | (all T8 (p(south,north,south,south,T8) -> p(north,north,south,north,take_cabbage(T8)))) &
          | (all T9 (p(north,north,south,north,T9) -> p(south,north,south,south,take_cabbage(T9)))) &
          | (all U1 (p(south,south,north,south,U1) -> p(north,south,north,north,take_cabbage(U1)))) &
          | (all V1 (p(north,south,north,north,V1) -> p(south,south,north,south,take_cabbage(V1)))) ->
          | (exists Z p(north,north,north,north,Z))""".stripMargin

      Prover9TermParser.parseFormula(oendsequent)
      ok
    }

    "parse infix formulas" in {
      List("a = b", "P(1+(X*2))", "f(1+X)= (X*0)+X", "(all X f(1+X)= (X*0)+X)", "(all X f(1+X)= (X*0)+X) | (all X f(1+X)= (X*0)+X)") map { s =>
        Prover9TermParser.parseFormula(s)
        ok
      }
    }

    "parse large formula 1" in {
      val str = """-(all U (ssList(U) -> (all V (ssList(V) -> (all W (ssList(W) -> (all X (ssList(X) -> V != X | U != W |
-neq(V,nil) | (all Y (ssList(Y) -> app(W,Y) != X | -totalorderedP(W) | (exists Z (ssItem(Z) & (exists X1 (ssList(X1) &
app(cons(Z,nil),X1) = Y & (exists X2 (ssItem(X2) & (exists X3 (ssList(X3) & app(X3,cons(X2,nil)) = W &
leq(X2,Z))))))))))) | nil != X & nil = W | neq(U,nil) & frontsegP(V,U)))))))))"""
      Prover9TermParser.parseFormula(str)
      ok
    }

    "parse large formula 2" in {
      val str = """--(exists X -(-(all Y (-r1(X,Y) | p7(Y))) | -((all Y (-r1(X,Y) | (-(all X (-r1(Y,X) | -(-p16(X) & -p116(X) &
p115(X)))) & -(all X (-r1(Y,X) | -(p16(X) & -p116(X) & p115(X)))) | -(-p115(Y) & p114(Y))) & (-(all X (-r1(Y,X) |
-(-p15(X) & -p115(X) & p114(X)))) & -(all X (-r1(Y,X) | -(p15(X) & -p115(X) & p114(X)))) | -(-p114(Y) & p113(Y))) &
(-(all X (-r1(Y,X) | -(-p14(X) & -p114(X) & p113(X)))) & -(all X (-r1(Y,X) | -(p14(X) & -p114(X) & p113(X)))) |
-(-p113(Y) & p112(Y))) & (-(all X (-r1(Y,X) | -(-p13(X) & -p113(X) & p112(X)))) & -(all X (-r1(Y,X) | -(p13(X) &
-p113(X) & p112(X)))) | -(-p112(Y) & p111(Y))) & (-(all X (-r1(Y,X) | -(-p12(X) & -p112(X) & p111(X)))) & -(all X
(-r1(Y,X) | -(p12(X) & -p112(X) & p111(X)))) | -(-p111(Y) & p110(Y))) & (-(all X (-r1(Y,X) | -(-p11(X) & -p111(X) &
p110(X)))) & -(all X (-r1(Y,X) | -(p11(X) & -p111(X) & p110(X)))) | -(-p110(Y) & p109(Y))) & (-(all X (-r1(Y,X) |
-(-p10(X) & -p110(X) & p109(X)))) & -(all X (-r1(Y,X) | -(p10(X) & -p110(X) & p109(X)))) | -(-p109(Y) & p108(Y))) &
(-(all X (-r1(Y,X) | -(-p9(X) & -p109(X) & p108(X)))) & -(all X (-r1(Y,X) | -(p9(X) & -p109(X) & p108(X)))) | -(-p108(Y)
& p107(Y))) & (-(all X (-r1(Y,X) | -(-p8(X) & -p108(X) & p107(X)))) & -(all X (-r1(Y,X) | -(p8(X) & -p108(X) &
p107(X)))) | -(-p107(Y) & p106(Y))) & (-(all X (-r1(Y,X) | -(-p7(X) & -p107(X) & p106(X)))) & -(all X (-r1(Y,X) |
-(p7(X) & -p107(X) & p106(X)))) | -(-p106(Y) & p105(Y))) & (-(all X (-r1(Y,X) | -(-p6(X) & -p106(X) & p105(X)))) & -(all
X (-r1(Y,X) | -(p6(X) & -p106(X) & p105(X)))) | -(-p105(Y) & p104(Y))) & (-(all X (-r1(Y,X) | -(-p5(X) & -p105(X) &
p104(X)))) & -(all X (-r1(Y,X) | -(p5(X) & -p105(X) & p104(X)))) | -(-p104(Y) & p103(Y))) & (-(all X (-r1(Y,X) |
-(-p4(X) & -p104(X) & p103(X)))) & -(all X (-r1(Y,X) | -(p4(X) & -p104(X) & p103(X)))) | -(-p103(Y) & p102(Y))) & (-(all
X (-r1(Y,X) | -(-p3(X) & -p103(X) & p102(X)))) & -(all X (-r1(Y,X) | -(p3(X) & -p103(X) & p102(X)))) | -(-p102(Y) &
p101(Y))) & (-(all X (-r1(Y,X) | -(-p2(X) & -p102(X) & p101(X)))) & -(all X (-r1(Y,X) | -(p2(X) & -p102(X) & p101(X))))
| -(-p101(Y) & p100(Y))) & (((all X (-r1(Y,X) | -p16(X) | -p115(X))) | p16(Y)) & ((all X (-r1(Y,X) | p16(X) | -p115(X)))
| -p16(Y)) | -p115(Y)) & (((all X (-r1(Y,X) | -p15(X) | -p114(X))) | p15(Y)) & ((all X (-r1(Y,X) | p15(X) | -p114(X))) |
-p15(Y)) | -p114(Y)) & (((all X (-r1(Y,X) | -p14(X) | -p113(X))) | p14(Y)) & ((all X (-r1(Y,X) | p14(X) | -p113(X))) |
-p14(Y)) | -p113(Y)) & (((all X (-r1(Y,X) | -p13(X) | -p112(X))) | p13(Y)) & ((all X (-r1(Y,X) | p13(X) | -p112(X))) |
-p13(Y)) | -p112(Y)) & (((all X (-r1(Y,X) | -p12(X) | -p111(X))) | p12(Y)) & ((all X (-r1(Y,X) | p12(X) | -p111(X))) |
-p12(Y)) | -p111(Y)) & (((all X (-r1(Y,X) | -p11(X) | -p110(X))) | p11(Y)) & ((all X (-r1(Y,X) | p11(X) | -p110(X))) |
-p11(Y)) | -p110(Y)) & (((all X (-r1(Y,X) | -p10(X) | -p109(X))) | p10(Y)) & ((all X (-r1(Y,X) | p10(X) | -p109(X))) |
-p10(Y)) | -p109(Y)) & (((all X (-r1(Y,X) | -p9(X) | -p108(X))) | p9(Y)) & ((all X (-r1(Y,X) | p9(X) | -p108(X))) |
-p9(Y)) | -p108(Y)) & (((all X (-r1(Y,X) | -p8(X) | -p107(X))) | p8(Y)) & ((all X (-r1(Y,X) | p8(X) | -p107(X))) |
-p8(Y)) | -p107(Y)) & (((all X (-r1(Y,X) | -p7(X) | -p106(X))) | p7(Y)) & ((all X (-r1(Y,X) | p7(X) | -p106(X))) |
-p7(Y)) | -p106(Y)) & (((all X (-r1(Y,X) | -p6(X) | -p105(X))) | p6(Y)) & ((all X (-r1(Y,X) | p6(X) | -p105(X))) |
-p6(Y)) | -p105(Y)) & (((all X (-r1(Y,X) | -p5(X) | -p104(X))) | p5(Y)) & ((all X (-r1(Y,X) | p5(X) | -p104(X))) |
-p5(Y)) | -p104(Y)) & (((all X (-r1(Y,X) | -p4(X) | -p103(X))) | p4(Y)) & ((all X (-r1(Y,X) | p4(X) | -p103(X))) |
-p4(Y)) | -p103(Y)) & (((all X (-r1(Y,X) | -p3(X) | -p102(X))) | p3(Y)) & ((all X (-r1(Y,X) | p3(X) | -p102(X))) |
-p3(Y)) | -p102(Y)) & (((all X (-r1(Y,X) | -p2(X) | -p101(X))) | p2(Y)) & ((all X (-r1(Y,X) | p2(X) | -p101(X))) |
-p2(Y)) | -p101(Y)) & (((all X (-r1(Y,X) | -p1(X) | -p100(X))) | p1(Y)) & ((all X (-r1(Y,X) | p1(X) | -p100(X))) |
-p1(Y)) | -p100(Y)) & (p115(Y) | -p116(Y)) & (p114(Y) | -p115(Y)) & (p113(Y) | -p114(Y)) & (p112(Y) | -p113(Y)) &
(p111(Y) | -p112(Y)) & (p110(Y) | -p111(Y)) & (p109(Y) | -p110(Y)) & (p108(Y) | -p109(Y)) & (p107(Y) | -p108(Y)) &
(p106(Y) | -p107(Y)) & (p105(Y) | -p106(Y)) & (p104(Y) | -p105(Y)) & (p103(Y) | -p104(Y)) & (p102(Y) | -p103(Y)) &
(p101(Y) | -p102(Y)) & (p100(Y) | -p101(Y)))) & -p101(X) & p100(X))))"""
      Prover9TermParser.parseFormula(str)
      ok
    }

    "parse infix v" in {
      Prover9TermParser.parseTerm("a v b") must beEqualTo(FOLFunction("v", List(FOLConst("a"), FOLConst("b"))))
    }

  }

  "issue 719" in {
    Prover9TermParser.parseTerm("X'") must beEqualTo(le"'\'' X")
  }

  "infix \\" in {
    Prover9TermParser.parseTerm("X \\ Y") must_== le"'\\' X Y"
  }

}
