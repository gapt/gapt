package gapt.proofs

import gapt.expr._
import gapt.expr.ty.Ti
import gapt.formats.babel.{ Notation, Precedence }
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.{ PrimitiveRecursiveFunction => PrimRecFun }
import gapt.proofs.context.update.ProofDefinitionDeclaration
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.lk.rules.ProofLink
import gapt.proofs.lk.rules.macros.WeakeningMacroRule
import org.specs2.mutable.Specification

class ContextTest extends Specification {
  import Context._

  "inductive type" in {
    "negative occurrences" in {
      default +
        InductiveType(
          "large",
          hoc"emptyset : large",
          hoc"comprehension : (large > o) > large" ) must throwAn[IllegalArgumentException]
    }

    "polymorphism" in {
      implicit val ctx: MutableContext = MutableContext.default()
      ctx += InductiveType(
        ty"list ?a",
        hoc"nil{?a}: list ?a",
        hoc"cons{?a}: ?a > list ?a > list ?a" )
      ctx += hof"'+'{?a} xs x = cons{?a} x xs"
      ctx += Notation.Infix( "+", Precedence.plusMinus )
      ctx += Sort( "i" )
      ctx ++= Seq( hoc"0: i", hoc"1: i", hoc"2: i" )
      val e = le"nil + 3 + 2 + 1: list i"
      ctx.check( e )
      ctx.normalize( e ) must_== le"cons 1 (cons 2 (cons 3 nil))"
    }

    "nonemptiness" in {
      default + InductiveType( "conat", hoc"s: conat>conat" ) must throwAn[IllegalArgumentException]
    }
  }

  "polymorphic definitions" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += hof"const{?a ?b} (f: ?a > ?b) = (!x!y f x = f y)"

    ctx += Sort( "i" )
    ctx += hoc"0 : i"
    ctx += hof"g (x:i) = 0"

    import gapt.proofs.gaptic._
    Lemma( hols":- const g" ) {
      unfold( "const", "g" ).in( "g" )
      decompose
      refl
    }
    ok
  }

  "recursive functions" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    ctx += Notation.Infix( "+", Precedence.plusMinus )
    ctx += PrimRecFun( hoc"'+': nat>nat>nat", "0 + x = x", "s(x) + y = s(x + y)" )
    ctx += hof"1 = s(0)"; ctx += hof"2 = s(1)"; ctx += hof"3 = s(2)"; ctx += hof"4 = s(3)"
    ctx.normalize( le"2 + 2" ) must_== ctx.normalize( le"4" )
  }

  "ite" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += PrimRecFun( hoc"ite{?a}: o > ?a > ?a > ?a", "ite true a b = a", "ite false a b = b" )

    ctx += Ti; ctx += hoc"a: i"; ctx += hoc"b: i"
    ctx.whnf( le"ite true a b" ) must_== le"a"
    ctx.whnf( le"ite false a b" ) must_== le"b"

    // a version of negation that reduces definitionally
    ctx += PrimRecFun( hoc"neg : o > o", "neg true = false", "neg false = true" )
    ctx.whnf( le"ite (neg true) a b" ) must_== le"b"
    ctx.whnf( le"ite (neg false) a b" ) must_== le"a"
  }

  "propext" in {
    implicit val ctx: MutableContext = MutableContext.default()
    import gapt.proofs.gaptic._
    val propext = Lemma( Sequent() :+ ( "goal" -> hof"!p!q ((p <-> q) -> p = q)" ) ) {
      repeat( allR )
      induction( hov"p: o" ).onAll( induction( hov"q: o" ) )
      quasiprop.onAllSubGoals
    }
    ok
  }

  "proof definitions" in {
    import gapt.proofs.lk._
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += Ti; ctx += hoc"c: i"
    ctx += hoc"a: i>o"; ctx += hoc"b: i>o"
    ctx += hoc"p: i>o"; ctx += ProofNameDeclaration( le"p x", hos"a x :- b x" )

    ctx += hoc"sorry: o"; ctx += ProofNameDeclaration( le"sorry", hos":-" )
    def proofOf( sequent: HOLSequent ): LKProof = WeakeningMacroRule( ProofLink( le"sorry" ), sequent )

    ctx += ProofDefinitionDeclaration( le"p c", proofOf( hos"a c :- b c" ) )
    ctx += ProofDefinitionDeclaration( le"p c", proofOf( hos":- b c" ) )

    ( ctx += ProofDefinitionDeclaration( le"p c", proofOf( hos"a c :- b c, b c" ) ) ) must throwAn[IllegalArgumentException]
    ( ctx += ProofDefinitionDeclaration( le"p c", proofOf( hos"a c :- b c, a c" ) ) ) must throwAn[IllegalArgumentException]
    ( ctx += ProofDefinitionDeclaration( le"p c", proofOf( hos":- a c, b c" ) ) ) must throwAn[IllegalArgumentException]
    ( ctx += ProofDefinitionDeclaration( le"p x", proofOf( hos":- b c" ) ) ) must throwAn[IllegalArgumentException]
  }

}
