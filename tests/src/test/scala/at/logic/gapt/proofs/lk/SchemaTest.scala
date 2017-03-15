package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.examples.tautSchema
import at.logic.gapt.examples.niaSchema
import at.logic.gapt.examples.gniaSchema
import at.logic.gapt.proofs.Context

import org.specs2.mutable.Specification

/**
 * Test for schema code
 * Created by David M. Cerna on 11.02.17.
 */
class SchemaTest extends Specification {
  def nat( i: Int )( implicit ctx: Context ): Expr = {
    val suc = ctx.get[Context.Constants].constants.getOrElse( "s", Const( "0", Ti ) )
    val base = ctx.get[Context.Constants].constants.getOrElse( "0", Const( "0", Ti ) )

    if ( i > 0 ) Apps( suc, Seq( nat( i - 1 ) ) )
    else base
  }

  "simple schema basecase" in {
    val proof = LKProofSchemata.Instantiate( "taut", Seq( nat( 0 )( tautSchema.ctx ) ) )( tautSchema.ctx )
    tautSchema.ctx.check( proof )
    ok
  }

  "simple schema stepcase" in {
    val proof = LKProofSchemata.Instantiate( "taut", Seq( nat( 1 )( tautSchema.ctx ) ) )( tautSchema.ctx )
    tautSchema.ctx.check( proof )
    ok
  }

  "simple schema Large" in {
    val proof = LKProofSchemata.Instantiate( "taut", Seq( nat( 6 )( tautSchema.ctx ) ) )( tautSchema.ctx )
    tautSchema.ctx.check( proof )
    ok
  }

  "Nia-schema basecase" in {
    val proof = LKProofSchemata.Instantiate( "omega", Seq( nat( 0 )( niaSchema.ctx ) ) )( niaSchema.ctx )
    niaSchema.ctx.check( proof )
    ok
  }

  "Nia-schema stepcase" in {
    val proof = LKProofSchemata.Instantiate( "omega", Seq( nat( 1 )( niaSchema.ctx ) ) )( niaSchema.ctx )
    niaSchema.ctx.check( proof )
    ok
  }

  " Nia-schema Large" in {
    val proof = LKProofSchemata.Instantiate( "omega", Seq( nat( 4 )( niaSchema.ctx ) ) )( niaSchema.ctx )
    niaSchema.ctx.check( proof )
    ok
  }

  "Nia-schema Super Large" in {
    val proof = LKProofSchemata.Instantiate( "omega", Seq( nat( 12 )( niaSchema.ctx ) ) )( niaSchema.ctx )
    niaSchema.ctx.check( proof )
    ok
  }
  "gNia-schema both parameters zero" in {
    val proof = LKProofSchemata.Instantiate( "omega", Seq( nat( 0 )( gniaSchema.ctx ), nat( 0 )( gniaSchema.ctx ) ) )( gniaSchema.ctx )
    gniaSchema.ctx.check( proof )
    ok
  }
  "gNia-schema first parameter zero" in {
    val proof = LKProofSchemata.Instantiate( "omega", Seq( nat( 0 )( gniaSchema.ctx ), nat( 5 )( gniaSchema.ctx ) ) )( gniaSchema.ctx )
    gniaSchema.ctx.check( proof )

    ok
  }
  "gNia-schema second parameter zero" in {
    val proof = LKProofSchemata.Instantiate( "omega", Seq( nat( 5 )( gniaSchema.ctx ), nat( 0 )( gniaSchema.ctx ) ) )( gniaSchema.ctx )
    gniaSchema.ctx.check( proof )

    ok
  }
  "gNia-schema both parameters non-zero" in {
    val proof = LKProofSchemata.Instantiate( "omega", Seq( nat( 5 )( gniaSchema.ctx ), nat( 5 )( gniaSchema.ctx ) ) )( gniaSchema.ctx )
    gniaSchema.ctx.check( proof )

    ok
  }

  "gNia-schema both parameters non-zero large" in {
    val proof = LKProofSchemata.Instantiate( "omega", Seq( nat( 12 )( gniaSchema.ctx ), nat( 12 )( gniaSchema.ctx ) ) )( gniaSchema.ctx )
    gniaSchema.ctx.check( proof )
    ok
  }

}

