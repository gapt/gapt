package at.logic.gapt.proofs.lkNew

import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.provers.prover9.Prover9Importer
import at.logic.gapt.proofs.lk.base._
import org.specs2.mutable._

import scala.io.Source

class LKNewOldConvTest extends Specification {

  def load( fn: String ) =
    Prover9Importer.lkProof(
      Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( fn ) ).mkString
    )

  if ( !Prover9Importer.isInstalled ) args( skipAll = true )

  "GEO037m4" in {

    val o = load( "GEO037-2.out" )
    val n = lkOld2New( o )
    val o_ = lkNew2Old( n )
    n.endSequent must beSyntacticFSequentEqual( o.root.toHOLSequent )
    o_.root.toHOLSequent must beSyntacticFSequentEqual( o.root.toHOLSequent )
  }

  "goat puzzle" in {

    val o = load( "PUZ047+1.out" )
    val n = lkOld2New( o )
    val o_ = lkNew2Old( n )
    n.endSequent must beSyntacticFSequentEqual( o.root.toHOLSequent )
    o_.root.toHOLSequent must beSyntacticFSequentEqual( o.root.toHOLSequent )
  }

  "cade1example.out" in {

    val o = load( "cade13example.out" )
    val n = lkOld2New( o )
    val o_ = lkNew2Old( n )
    n.endSequent must beSyntacticFSequentEqual( o.root.toHOLSequent )
    o_.root.toHOLSequent must beSyntacticFSequentEqual( o.root.toHOLSequent )
  }

  "proof with new_symbol" in {

    val o = load( "ALG138+1.out" )
    val n = lkOld2New( o )
    val o_ = lkNew2Old( n )
    n.endSequent must beSyntacticFSequentEqual( o.root.toHOLSequent )
    o_.root.toHOLSequent must beSyntacticFSequentEqual( o.root.toHOLSequent )
  }

}
