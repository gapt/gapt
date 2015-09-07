package at.logic.gapt.proofs.resolutionNew

import at.logic.gapt.provers.prover9.Prover9Importer
import org.specs2.mutable._

import scala.io.Source

class OldNewConversionTest extends Specification {

  def load( fn: String ) =
    Prover9Importer.robinsonProof(
      Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( fn ) ).mkString
    )

  if ( !Prover9Importer.isInstalled ) args( skipAll = true )

  "GEO037m4" in {
    val o = load( "GEO037-2.out" )
    val n = resOld2New( o )
    val o_ = resNew2Old( n )
    n.conclusion.isEmpty must_== true
    o_.root.isEmpty must_== true
  }

  "goat puzzle" in {
    val o = load( "PUZ047+1.out" )
    val n = resOld2New( o )
    val o_ = resNew2Old( n )
    n.conclusion.isEmpty must_== true
    o_.root.isEmpty must_== true
  }

  "cade13example.out" in {
    val o = load( "cade13example.out" )
    val n = resOld2New( o )
    val o_ = resNew2Old( n )
    n.conclusion.isEmpty must_== true
    o_.root.isEmpty must_== true
  }

  "proof with new_symbol" in {
    val o = load( "ALG138+1.out" )
    val n = resOld2New( o )
    val o_ = resNew2Old( n )
    n.conclusion.isEmpty must_== true
    o_.root.isEmpty must_== true
  }

}
