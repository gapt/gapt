package gapt.proofs.nd

import gapt.expr._
import gapt.formats.babel.{Notation, Precedence}
import gapt.proofs.{Ant, Checkable, ProofBuilder}
import gapt.proofs.context.Context
import gapt.proofs.context.update.{InductiveType, PrimitiveRecursiveFunction}
import org.specs2.mutable.Specification

class ClassicalExtractionTest extends Specification {

  "realizer of theory axioms" in {
    // TODO: should weakened variable match realizer from theory axiom?
    //       should realizer for theory axiom be a constant?
    var ctx = Context.default

    ctx += InductiveType( ty"nat", hoc"0 : nat", hoc"s : nat > nat")
    ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
    val Some( bFalse ) = ctx.constant( "bFalse" )
    val Some( bTrue ) = ctx.constant( "bTrue" )
    val bIsTrue = hoc"p : bool>o"
    ctx += PrimitiveRecursiveFunction(
      bIsTrue,
      List(
        ( bIsTrue( bFalse ) -> hof"false" ),
        ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )

    implicit var classicalCtx = ClassicalExtraction.systemT(ctx)

    val prf = ProofBuilder.
      c(gapt.proofs.nd.TheoryAxiom(hof"p(bTrue)")).
      u(WeakeningRule(_, hof"p(bTrue)")).
      u(ImpIntroRule(_, Ant(0))).
    qed

    val lam = ClassicalExtraction.extractCases(prf)

    val Some( i ) = classicalCtx.constant( "i" )
    normalize(lam(i)) must_== i
  }
}
