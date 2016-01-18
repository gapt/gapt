package at.logic.gapt.provers.inductionProver

import at.logic.gapt.examples._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.expr.{ Eq, FOLConst, FOLFunction }
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.{ Ant, Suc, HOLSequent, Sequent }
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.provers.inductionProver.SimpleInductionProof._
import at.logic.gapt.provers.prover9.Prover9
import org.apache.log4j.{ Level, Logger }

import scala.collection.immutable.HashMap

object RunOnProofSequence {
  def apply( proof: String ) = {
    new SipProver().getSimpleInductionProof( getEndSequent( proof ), getInstanceProofs( proof ) )
  }

  def getInstanceProofs( proof: String ) = ( 0 until 5 ).map { n => n -> removeEqAxioms( eliminateCutsET( LKToExpansionProof( ProofMap( proof )._2( n ) ) ) ) }

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

  def removeEqAxioms( eseq: ExpansionProof ): ExpansionProof =
    ExpansionProof( eseq.expansionSequent.zipWithIndex filter {
      case ( et, Ant( _ ) ) => !Prover9.isValid( toShallow( et ) )
      case ( et, Suc( _ ) ) => !Prover9.isValid( -toShallow( et ) )
    } map { _._1 } )
}