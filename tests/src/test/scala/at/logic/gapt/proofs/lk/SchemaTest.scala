package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.examples.tautSchema
import at.logic.gapt.examples.niaSchema
import at.logic.gapt.examples.gniaSchema

import org.specs2.mutable.Specification

/**
 * Test for schema code
 * Created by David M. Cerna on 11.02.17.
 */
class SchemaTest extends Specification {
  "Testing simple schema basecase" in {
    val proof = LKProofSchemata.Instantiate( "taut", Seq( le"(0)" ) )( tautSchema.ctx )
    tautSchema.ctx.check(proof)
    None mustEqual None
  }

  "Testing simple schema stepcase" in {
    val proof = LKProofSchemata.Instantiate( "taut", Seq( le"(s 0)" ) )( tautSchema.ctx )
    tautSchema.ctx.check(proof)  
   None mustEqual None   }

  "Testing simple schema Large" in {
    val proof = LKProofSchemata.Instantiate( "taut", Seq( le"(s (s (s (s 0))))" ) )( tautSchema.ctx )
    tautSchema.ctx.check(proof)  
   None mustEqual None   }

  "Testing Nia-schema basecase" in {
    val proof = LKProofSchemata.Instantiate( "omega", Seq( le"(0:w)" ) )( niaSchema.ctx )
    niaSchema.ctx.check(proof)  
   None mustEqual None   }

  "Testing Nia-schema stepcase" in {
    val proof = LKProofSchemata.Instantiate( "omega", Seq( le"((s:w>w) (0:w))" ) )( niaSchema.ctx )
    niaSchema.ctx.check(proof)  
   None mustEqual None   }

  "Testing  Nia-schema Large" in {
    val proof = LKProofSchemata.Instantiate( "omega", Seq( le"(s (s ((s:w>w) (0:w))))" ) )( niaSchema.ctx )
    niaSchema.ctx.check(proof)  
   None mustEqual None   }

  "Testing Nia-schema Super Large" in {
    val proof = LKProofSchemata.Instantiate( "omega", Seq( le"(s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s ((s:w>w) (0:w)))))))))))))))))))))))))))))))))" ) )( niaSchema.ctx )
    niaSchema.ctx.check(proof)  
   None mustEqual None   }
  "Testing gNia-schema both parameters zero" in {
    val proof = LKProofSchemata.Instantiate("omega",Seq(le"(0:w)",le"(0:w)"))(gniaSchema.ctx)
    gniaSchema.ctx.check(proof)  
   None mustEqual None   }
  "Testing gNia-schema first parameter zero" in {
    val proof = LKProofSchemata.Instantiate("omega",Seq(le"(0:w)",le"(s(s(s((s:w>w) (0:w)))))"))(gniaSchema.ctx)
    gniaSchema.ctx.check(proof)  

   None mustEqual None   }
  "Testing gNia-schema second parameter zero" in {
    val proof = LKProofSchemata.Instantiate("phi",Seq(le"(s(s(s((s:w>w) (0:w)))))",le"(0:w)"))(gniaSchema.ctx)
    gniaSchema.ctx.check(proof)  

   None mustEqual None   }
  "Testing gNia-schema both parameters non-zero" in {
    val proof = LKProofSchemata.Instantiate("phi", Seq(le"(s(s(s((s:w>w) (0:w)))))", le"(s(s(s((s:w>w) (0:w)))))"))(gniaSchema.ctx)
    gniaSchema.ctx.check(proof)  

   None mustEqual None   }

  "Testing gNia-schema both parameters non-zero large" in {
    val proof = LKProofSchemata.Instantiate("phi",Seq(le"((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) (0:w)))))))))))",le"( ( (((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) (0:w))))))))))))))"))(gniaSchema.ctx)
    gniaSchema.ctx.check(proof)  
   None mustEqual None   }

}


