package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.examples.tautSchema
import at.logic.gapt.examples.niaSchema

import org.specs2.mutable.Specification

/**
 * Created by David M. Cerna on 11.02.17.
 */
class SchemaTest extends Specification {
  "Testing simple schema basecase" in {
    LKProofSchemata.Instantiate( "taut", Seq( le"(0)" ) )( tautSchema.ctx ) mustNotEqual None
  }

  "Testing simple schema stepcase" in {
    LKProofSchemata.Instantiate( "taut", Seq( le"(s 0)" ) )( tautSchema.ctx ) mustNotEqual None
  }

  "Testing simple schema Large" in {
    LKProofSchemata.Instantiate( "taut", Seq( le"(s (s (s (s 0))))" ) )( tautSchema.ctx ) mustNotEqual None
  }

  "Testing Nia-schema basecase" in {
    LKProofSchemata.Instantiate( "omega", Seq( le"(0:w)" ) )( niaSchema.ctx ) mustNotEqual None
  }

  "Testing Nia-schema stepcase" in {
    LKProofSchemata.Instantiate( "omega", Seq( le"((s:w>w) (0:w))" ) )( niaSchema.ctx ) mustNotEqual None
  }

  "Testing  Nia-schema Large" in {
    LKProofSchemata.Instantiate( "omega", Seq( le"((s:w>w) ((s:w>w) ((s:w>w) (0:w))))" ) )( niaSchema.ctx ) mustNotEqual None
  }

  "Testing Nia-schema Super Large" in {
    LKProofSchemata.Instantiate( "omega", Seq( le"((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) ((s:w>w) (0:w)))))))))))))))))))))))))))))))))" ) )( niaSchema.ctx ) mustNotEqual None

  }

}
