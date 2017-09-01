package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.examples.tautSchema
import at.logic.gapt.examples.niaSchema
import at.logic.gapt.examples.gniaSchema
import at.logic.gapt.examples.induction.numbers.pluscomm
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

  {
    import tautSchema.ctx

    "simple schema basecase" in {
      val proof = LKProofSchemata.Instantiate( le"taut ${nat( 0 )}" )
      ctx.check( proof )
      ok
    }

    "simple schema stepcase" in {
      val proof = LKProofSchemata.Instantiate( le"taut ${nat( 1 )}" )
      ctx.check( proof )
      ok
    }

    "simple schema Large" in {
      val proof = LKProofSchemata.Instantiate( le"taut ${nat( 6 )}" )
      ctx.check( proof )
      ok
    }
  }

  {
    import niaSchema.ctx

    "Nia-schema basecase" in {
      val proof = LKProofSchemata.Instantiate( le"omega ${nat( 0 )}" )
      ctx.check( proof )
      ok
    }

    "Nia-schema stepcase" in {
      val proof = LKProofSchemata.Instantiate( le"omega ${nat( 1 )}" )
      ctx.check( proof )
      ok
    }

    " Nia-schema Large" in {
      val proof = LKProofSchemata.Instantiate( le"omega ${nat( 4 )}" )
      ctx.check( proof )
      ok
    }

    "Nia-schema Super Large" in {
      val proof = LKProofSchemata.Instantiate( le"omega ${nat( 12 )}" )
      ctx.check( proof )
      ok
    }
  }

  {
    import gniaSchema.ctx

    "gNia-schema both parameters zero" in {
      val proof = LKProofSchemata.Instantiate( le"omega ${nat( 0 )} ${nat( 0 )}" )
      ctx.check( proof )
      ok
    }
    "gNia-schema first parameter zero" in {
      val proof = LKProofSchemata.Instantiate( le"omega ${nat( 0 )} ${nat( 5 )}" )
      ctx.check( proof )
      ok
    }
    "gNia-schema second parameter zero" in {
      val proof = LKProofSchemata.Instantiate( le"omega ${nat( 5 )} ${nat( 0 )}" )
      ctx.check( proof )
      ok
    }
    "gNia-schema both parameters non-zero" in {
      val proof = LKProofSchemata.Instantiate( le"omega ${nat( 5 )} ${nat( 5 )}" )
      ctx.check( proof )
      ok
    }
    "gNia-schema both parameters non-zero large" in {
      val proof = LKProofSchemata.Instantiate( le"omega ${nat( 12 )} ${nat( 12 )}" )
      ctx.check( proof )
      ok
    }

    "Test if PlusComm induction proof is K-simple" in {
       IsKSimple(pluscomm) must_== false
    }

    "Test if K-simple PlusComm induction proof is K-simple" in {
      val result: LKProof = {
        val proofs = pluscomm.subProofs.toList.foldRight( List[LKProof]() )( ( a, z ) => {
          a match {
            case p: InductionRule =>
              val succ: Var = p.cases.foldRight( Var( "wrong", p.indTy ): Var )( ( a, z ) => {
                a match {
                  case InductionCase( _, Const( "s", _ ), _, e, _ ) => e.head
                  case _ => z
                }
              } )
              val ret: Expr = Substitution( freeVariables( p.formula.term ).head -> succ )( p.formula.term )
              InductionRule( p.cases, Abs( succ, ret ), succ ) :: z
            case _ => z
          }
        } )
        if ( proofs.nonEmpty ) {
          if ( proofs.tail.nonEmpty ) {
            val nonq = proofs.tail.foldRight( ( proofs.head, proofs.head.mainFormulas.head ) )(
              ( a, z ) => {
                val newp = AndRightRule( z._1, z._1.conclusion.indexOfInSuc( z._2 ), a, a.conclusion.indexOfInSuc( a.mainFormulas.head ) )
                ( newp, newp.mainFormula )
              } )._1
            val InductionRule( _, _, x: Var ) = proofs.head
            ForallRightRule( nonq, nonq.mainIndices.head, x, Var( "x", x.ty ) )
          } else proofs.head
        } else pluscomm
      }
      IsKSimple(result) must_== true
    }
  }

}

