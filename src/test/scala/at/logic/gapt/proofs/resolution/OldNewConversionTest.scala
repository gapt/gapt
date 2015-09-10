package at.logic.gapt.proofs.resolution

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
    val n = load( "GEO037-2.out" )
    val o = resNew2Old( n )
    val n_ = resOld2New( o )
    n.conclusion.isEmpty must_== true
    o.root.isEmpty must_== true
    n_.conclusion.isEmpty must_== true
  }

  "goat puzzle" in {
    val n = load( "PUZ047+1.out" )
    val o = resNew2Old( n )
    val n_ = resOld2New( o )
    n.conclusion.isEmpty must_== true
    o.root.isEmpty must_== true
    n_.conclusion.isEmpty must_== true
  }

  "cade13example.out" in {
    val n = load( "cade13example.out" )
    val o = resNew2Old( n )
    val n_ = resOld2New( o )
    n.conclusion.isEmpty must_== true
    o.root.isEmpty must_== true
    n_.conclusion.isEmpty must_== true
  }

  "proof with new_symbol" in {
    val n = load( "ALG138+1.out" )
    val o = resNew2Old( n )
    val n_ = resOld2New( o )
    n.conclusion.isEmpty must_== true
    o.root.isEmpty must_== true
    n_.conclusion.isEmpty must_== true
  }

}
