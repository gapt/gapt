package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.examples.tautSchema
import at.logic.gapt.examples.niaSchema
import at.logic.gapt.examples.gniaSchema
import at.logic.gapt.proofs.Context
import at.logic.gapt.examples.NdiffSchema
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
  {

   import NdiffSchema.ctx
    "NdiffSchema Instantiate " in {
      val proof = instantiateProof( le"omega ${nat( 15 )}" )
      ctx.check( proof )
      ok
    }
  }
  {
    import tautSchema.ctx

    "simple schema basecase" in {
      val proof = instantiateProof( le"taut ${nat( 0 )}" )
      ctx.check( proof )
      ok
    }

    "simple schema stepcase" in {
      val proof = instantiateProof( le"taut ${nat( 1 )}" )
      ctx.check( proof )
      ok
    }

    "simple schema Large" in {
      val proof = instantiateProof( le"taut ${nat( 6 )}" )
      ctx.check( proof )
      ok
    }
  }

  {
    import niaSchema.ctx

    "Nia-schema basecase" in {
      val proof = instantiateProof( le"omega ${nat( 0 )}" )
      ctx.check( proof )
      ok
    }

    "Nia-schema stepcase" in {
      val proof = instantiateProof( le"omega ${nat( 1 )}" )
      ctx.check( proof )
      ok
    }

    " Nia-schema Large" in {
      val proof = instantiateProof( le"omega ${nat( 4 )}" )
      ctx.check( proof )
      ok
    }

    "Nia-schema Super Large" in {
      val proof = instantiateProof( le"omega ${nat( 12 )}" )
      ctx.check( proof )
      ok
    }
  }

  {
    import gniaSchema.ctx

    "gNia-schema both parameters zero" in {
      val proof = instantiateProof( le"omega ${nat( 0 )} ${nat( 0 )}" )
      ctx.check( proof )
      ok
    }
    "gNia-schema first parameter zero" in {
      val proof = instantiateProof( le"omega ${nat( 0 )} ${nat( 5 )}" )
      ctx.check( proof )
      ok
    }
    "gNia-schema second parameter zero" in {
      val proof = instantiateProof( le"omega ${nat( 5 )} ${nat( 0 )}" )
      ctx.check( proof )
      ok
    }
    "gNia-schema both parameters non-zero" in {
      val proof = instantiateProof( le"omega ${nat( 5 )} ${nat( 5 )}" )
      ctx.check( proof )
      ok
    }
    "gNia-schema both parameters non-zero large" in {
      val proof = instantiateProof( le"omega ${nat( 12 )} ${nat( 12 )}" )
      ctx.check( proof )
      ok
    }
  }

}

