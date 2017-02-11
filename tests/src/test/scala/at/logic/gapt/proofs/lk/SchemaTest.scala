package at.logic.gapt.proofs.lk

import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{Sequent,Context}
import at.logic.gapt.expr._
import at.logic.gapt.examples.tautSchema
import at.logic.gapt.examples.niaSchema

import org.specs2.mutable.Specification

/**
  * Created by cernadavid1 on 11.02.17.
  */
class SchemaTest extends Specification {
  "Testing simple schema" in {
    val one = new LKProofSchemata()
    one.Instantiate("taut ",Seq(le"(0)"))(tautSchema.ctx) mustNotEqual None
    one.Instantiate("taut ",Seq(le"(s 0)"))(tautSchema.ctx) mustNotEqual None
    one.Instantiate("taut ",Seq(le"((s:w>w) ((s:w>w) ((s:w>w) (0:w))))"))(tautSchema.ctx) mustNotEqual None
    one.Instantiate("omega ",Seq(le"(0:w)"))(niaSchema.ctx) mustNotEqual None
    one.Instantiate("omega ",Seq(le"((s:w>w) ((s:w>w) ((s:w>w) (0:w))))"))(niaSchema.ctx) mustNotEqual None
  }

}
