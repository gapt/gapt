package gapt.formats.tip

import gapt.expr._
import gapt.formats.{ InputFile, StringInputFile }
import gapt.formats.tip.compiler.TipSmtToTipProblemCompiler
import gapt.formats.tip.parser.TipSmtParser
import org.specs2.mutable.Specification

class TipProblemCompilerTest extends Specification {

  "Compiler should simplify problem definitions properly" in {
    val inputProblem = new TipSmtToTipProblemCompiler( TipSmtParser.parse(
      StringInputFile( """
        |(declare-datatypes ()
        |  ((Nat (Z) (S (P Nat)))))
        |
        |(declare-datatypes ()
        | ((list (nil)
        |    (cons (head Nat) (tail list)))))
        |
        |(define-fun-rec f ((x list)) Nat
        |  ( match x
        |    (case (cons y ys) (f ys))
        |    (case default Z)
        |  )
        |)
      """.stripMargin ) ) ).compileTipProblem().toProblem

    implicit val ctx = inputProblem.ctx

    inputProblem.functions( 0 ).definitions.toSet must_==
      Set( hof"f(nil) = Z", hof"!y !ys f(cons(y,ys)) = f(ys)" )
  }

  "Compiler should compile inductive datatypes properly" in {
    val inputProblem = new TipSmtToTipProblemCompiler( TipSmtParser.parse(
      StringInputFile( """
        |(declare-datatypes ()
        |  ((Nat (Z) (S (P Nat)))))
        |
        |(declare-datatypes ()
        | ((list (nil)
        |    (cons (head Nat) (tail list)))))
      """.stripMargin ) ) ).compileTipProblem().toProblem

    implicit val ctx = inputProblem.ctx

    inputProblem.datatypes.toSet must
      contain( Set(
        TipDatatype(
          TBase( "Nat", Nil ),
          Seq(
            TipConstructor( hoc"Z", Nil ),
            TipConstructor( hoc"S", Seq( hoc"P" ) ) ) ),
        TipDatatype(
          TBase( "list", Nil ),
          Seq(
            TipConstructor( hoc"nil", Nil ),
            TipConstructor( hoc"cons", Seq( hoc"head", hoc"tail" ) ) ) ) ) )
  }

  "Compiler should add inductive definition of Booleans" in {
    val inputProblem =
      new TipSmtToTipProblemCompiler(
        TipSmtParser.parse( StringInputFile( "" ) ) )
        .compileTipProblem()
        .toProblem

    implicit val ctx = inputProblem.ctx

    inputProblem.datatypes.toSet must
      contain(
        TipDatatype(
          To,
          Seq(
            TipConstructor( hoc"⊤", Nil ),
            TipConstructor( hoc"⊥", Nil ) ) ) )
  }

  "Mutually recursive function definitions should compile to formulas" in {
    val inputProblem = new TipSmtToTipProblemCompiler( TipSmtParser.parse(
      StringInputFile( """
        |(declare-datatypes ()
        |  ((Nat (Z) (S (P Nat)))))
        |
        |(declare-datatypes ()
        | ((list (nil)
        |    (cons (head Nat) (tail list)))))
        |
        |(define-funs-rec
        |  ( (f1 ((x list)) Nat) (f2 ((x list)) Nat) )
        |  (
        |    (f2 x)
        |    (f1 x)
        |  )
        |)
      """.stripMargin ) ) ).compileTipProblem().toProblem

    implicit val ctx = inputProblem.ctx

    inputProblem.functions.toSet must
      contain( Set(
        TipFun( hoc"f1", Seq( hof"!x f1(x) = f2(x)" ) ),
        TipFun( hoc"f2", Seq( hof"!x f1(x) = f2(x)" ) ) ) )
  }

  "Compiler should compile ite-expression properly" in {
    val inputProblem = new TipSmtToTipProblemCompiler( TipSmtParser.parse(
      StringInputFile( """
        |(declare-datatypes ()
        |  ((Nat (Z) (S (P Nat)))))
        |
        |(declare-datatypes ()
        | ((list (nil)
        |    (cons (head Nat) (tail list)))))
        |
        |(define-fun-rec f ((x list)) Nat
        |  ( match x
        |    (case (cons y ys) (f ys))
        |    (case default Z)
        |  )
        |)
        |(prove (ite (= Z Z) (= (f nil) Z) (= (f nil) Z) ))
      """.stripMargin ) ) ).compileTipProblem().toProblem

    implicit val ctx = inputProblem.ctx

    inputProblem.goal must_==
      hof"(Z = Z -> f(nil) = Z) &  (-(Z = Z) -> f(nil) = Z)"
  }

  "Compiler should simplify match-expression properly" in {
    val inputProblem = new TipSmtToTipProblemCompiler( TipSmtParser.parse(
      StringInputFile( """
        |(declare-datatypes ()
        |  ((Nat (Z) (S (P Nat)))))
        |
        |(declare-datatypes ()
        | ((list (nil)
        |    (cons (head Nat) (tail list)))))
        |
        |(define-fun-rec f ((x list)) Nat
        |  ( match x
        |    (case (cons y ys) (f ys))
        |    (case default Z)
        |  )
        |)
        |(prove
        |  (forall
        |    ((xs list))
        |      (match xs
        |        (case nil (= Z Z) )
        |         ( case (cons y ys) (= ys ys) ) ) ) )
      """.stripMargin ) ) ).compileTipProblem().toProblem

    implicit val ctx = inputProblem.ctx

    inputProblem.goal must_== hof"Z = Z & !(ys: list) ys = ys"
  }

  "Repeated matches on same variable should be allowed" in {
    val inputProblem = new TipSmtToTipProblemCompiler( TipSmtParser.parse(
      StringInputFile( """
        |(declare-datatypes ()
        |  ((Nat (Z) (S (P Nat)))))
        |
        |(declare-datatypes ()
        | ((list (nil)
        |    (cons (head Nat) (tail list)))))
        |
        |(define-fun-rec f ((x list)) Nat
        |  ( match x
        |    (case (cons y ys) (match x (case nil Z) (case (cons z zs) (f zs))))
        |    (case default Z)
        |  )
        |)
      """.stripMargin ) ) ).compileTipProblem().toProblem
    success
  }

  "Distinct-expression should be compiled" in {
    val inputProblem = new TipSmtToTipProblemCompiler( TipSmtParser.parse(
      StringInputFile( """
        |(declare-datatypes ()
        |  ((Nat (Z) (S (P Nat)))))
        |
        |(declare-datatypes ()
        | ((list (nil)
        |    (cons (head Nat) (tail list)))))
        |
        |(define-fun-rec f ((x list) (y list) (z list)) Bool
        |  ( distinct x y z)
        |)
      """.stripMargin ) ) ).compileTipProblem().toProblem
    success
  }

  "Equation between Boolean expressions should become equivalence" in {
    val inputProblem = new TipSmtToTipProblemCompiler( TipSmtParser.parse(
      StringInputFile( """
        | (declare-const a Bool)
        |
        | (declare-const b Bool)
        |
        | (prove (= a b))
      """.stripMargin ) ) ).compileTipProblem().toProblem
    inputProblem.goal must_== hof"a ↔ b"
  }

  "Constants should be compiled" in {
    val inputProblem = new TipSmtToTipProblemCompiler( TipSmtParser.parse(
      StringInputFile( """
        | (declare-const a Bool)
      """.stripMargin ) ) ).compileTipProblem().toProblem
    inputProblem.ctx.constants.toSet must contain( hoc"a : o" )
  }

  "Compiler should simplify constructor match-expressions" in {
    val inputProblem = new TipSmtToTipProblemCompiler( TipSmtParser.parse(
      StringInputFile( """
        |(declare-datatypes ()
        |  ((Nat (Z) (S (P Nat)))))
        |
        |(prove
        |      (match Z
        |        (case Z true)
        |         ( case (S x) false ) ) )
      """.stripMargin ) ) ).compileTipProblem().toProblem

    implicit val ctx = inputProblem.ctx

    inputProblem.goal must_== hof"⊤"
  }
}
