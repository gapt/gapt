package at.logic.gapt.provers.inductionProver

import at.logic.gapt.examples.{ FactorialFunctionEqualityExampleProof2, FactorialFunctionEqualityExampleProof, UniformAssociativity3ExampleProof }
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.expr.{ Eq, FOLConst, FOLFunction }
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.lk.LKToExpansionProof
import at.logic.gapt.proofs.lk.base.{ HOLSequent, LKProof, Sequent }
import at.logic.gapt.provers.inductionProver.SimpleInductionProof._
import org.apache.log4j.{ Level, Logger }

import scala.collection.immutable.HashMap

object RunOnProofSequence {
  def apply( proof: String ) = {
    new SipProver().getSimpleInductionProof( getEndSequent( proof ), getInstanceProofs( proof ) )
  }

  def getInstanceProofs( proof: String ) = ( 0 until 5 ).map { n => n -> removeEqAxioms( LKToExpansionProof( ProofMap( proof )._2( n ) ) ) }

  def getEndSequent( proof: String ) = ProofMap( proof )._1

  val assocES = HOLSequent(
    Seq( "s(x+y) = x+s(y)", "x+0 = x" )
      map ( s => univclosure( parseFormula( s ) ) ),
    Seq( Eq(
      FOLFunction( "+", FOLFunction( "+", alpha, alpha ), alpha ),
      FOLFunction( "+", alpha, FOLFunction( "+", alpha, alpha ) )
    ) )
  )
  val factorialES = HOLSequent(
    Seq(
      "f(0) = s(0)",
      "f(s(x)) = s(x)*f(x)",
      "g(x,0) = x",
      "g(x, s(y)) = g(x * s(y), y)",
      "x*s(0) = x",
      "s(0)*x = x",
      "(x*y)*z = x*(y*z)"
    )
      map ( s => univclosure( parseFormula( s ) ) ),
    Seq( Eq(
      FOLFunction( "f", alpha ),
      FOLFunction( "g", FOLFunction( "s", FOLConst( "0" ) ), alpha )
    ) )
  )

  val ProofMap = HashMap[String, ( HOLSequent, Int => LKProof )](
    "factorial" -> ( factorialES, FactorialFunctionEqualityExampleProof2.apply _ ),
    "assoc" -> ( assocES, UniformAssociativity3ExampleProof.apply _ )
  )

  def removeEqAxioms( eseq: ExpansionSequent ) = {
    val eqaxioms = Sequent(
      List(
      "x = x",
      "x = y -> y = x",
      "(x = y & y = z) -> x = z",
      "x = y -> (y = z -> x = z)",
      "x = y -> s(x) = s(y)",
      "x = y -> (u = v -> x+u = y+v)",
      "x = z -> y + x = z + x", // congruence plus left
      "(all x (all y (all z (y = z -> g(x, y) = g(x, z)))))", // congruence of g on the right
      "x = y -> z*x = z*y"
    ), // congruence of mult right
      Nil
    ) map { s => univclosure( parseFormula( s ) ) }

    removeFromExpansionSequent( eseq, eqaxioms )
  }
}