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
  "Testing simple schema basecase" in {
    val one = new LKProofSchemata()
    one.Instantiate("taut",Seq(le"(0)"))(tautSchema.ctx) mustNotEqual None
  }

 "Testing simple schema stepcase" in {
    val one = new LKProofSchemata()
    one.Instantiate("taut",Seq(le"(s 0)"))(tautSchema.ctx) mustNotEqual None
  }

   "Testing simple schema Large" in {
     val one = new LKProofSchemata()
     one.Instantiate("taut",Seq(le"(s (s (s (s 0))))"))(tautSchema.ctx) mustNotEqual None
   }

     "Testing simple Nia-schema basecase" in {
      val one = new LKProofSchemata()
      one.Instantiate("omega",Seq(le"(0:w)"))(niaSchema.ctx) mustNotEqual None
    }

  "Testing simple Nia-schema stepcase" in {
    val one = new LKProofSchemata()
    one.Instantiate("omega",Seq(le"((s:w>w) (0:w))"))(niaSchema.ctx) mustNotEqual None
  }

  "Testing simple Nia-schema Large" in {
    val one = new LKProofSchemata()
    one.Instantiate("omega",Seq(le"((s:w>w) ((s:w>w) ((s:w>w) (0:w))))"))(niaSchema.ctx) mustNotEqual None
  }

}
