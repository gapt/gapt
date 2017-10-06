package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.examples.tautSchema
import at.logic.gapt.examples.NiaSchema
import at.logic.gapt.examples.gniaSchema
import at.logic.gapt.examples.NdiffSchema
import at.logic.gapt.examples.induction.numbers.pluscomm
import at.logic.gapt.proofs.{ Context, HOLSequent, SetSequent }
import at.logic.gapt.proofs.ceres.{ CharacteristicClauseSet, SchematicClauseSet, StructCreators }
import at.logic.gapt.provers.escargot.Escargot
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
    "simple " in {
      val proof = instantiateProof.Instantiate(le"omega ${nat(3)}")
      ctx.check(proof)
      ok
    }
  }
  /*{
    import tautSchema.ctx
    "simple schema basecase" in {
      val proof = instantiateProof.Instantiate( le"taut ${nat( 0 )}" )
      ctx.check( proof )
      ok
    }

    "simple schema stepcase" in {
      val proof = instantiateProof.Instantiate( le"taut ${nat( 1 )}" )
      ctx.check( proof )
      ok
    }

    "simple schema Large" in {
      val proof = instantiateProof.Instantiate( le"taut ${nat( 6 )}" )
      ctx.check( proof )
      ok
    }
  }

  {
    import at.logic.gapt.examples.NiaSchema.ctx

    "Nia-schema basecase" in {
      val proof = instantiateProof.Instantiate( le"omega ${nat( 0 )}" )
      ctx.check( proof )
      ok
    }

    "Nia-schema stepcase" in {
      val proof = instantiateProof.Instantiate( le"omega ${nat( 1 )}" )
      ctx.check( proof )
      ok
    }

    " Nia-schema Large" in {
      val proof = instantiateProof.Instantiate( le"omega ${nat( 4 )}" )
      ctx.check( proof )
      ok
    }

    "Nia-schema Super Large" in {
      val proof = instantiateProof.Instantiate( le"omega ${nat( 12 )}" )
      ctx.check( proof )
      ok
    }

    " Nia-schema Clause Set Extraction  Instance 3" in {
      val proof = instantiateProof.Instantiate( le"omega ${nat( 3 )}" )
      ctx.check( proof )
      val thestruct = StructCreators.extract( proof, ctx )
      CharacteristicClauseSet( thestruct )
      ok
    }

    " Nia-schema Clause Set Refutation  Instance 1" in {
      val proof = instantiateProof.Instantiate( le"omega ${nat( 1 )}" )
      ctx.check( proof )
      val thestruct = StructCreators.extract( proof, ctx )
      val cs = CharacteristicClauseSet( thestruct )
      val refutation = Escargot.getResolutionProof( cs )
      refutation must beSome
    }

    " Nia-schema Clause set Extraction Individual Proof" in {
      val ts = StructCreators.extract( NiaSchema.phiSc, ctx )
      CharacteristicClauseSet( ts )
      ok
    }

    " Extracting the Schematic Characteristic Clause Set of the Niaschema" in {
      SchematicClauseSet( "omega", ctx ) must beSome
    }
    " Extracting the Schematic Characteristic Clause Set Checking number of symbols" in {
      val SCS = SchematicClauseSet( "omega", ctx ) match {
        case Some( x ) => x
        case None      => Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]()
      }
      SCS.keySet.size must beEqualTo( 4 )
    }
    " Extracting the Schematic Characteristic Clause Set Checking number configurations" in {
      val SCS = SchematicClauseSet( "omega", ctx ) match {
        case Some( x ) => x
        case None      => Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]()
      }

      SCS.keySet.fold( 0 )( ( vale, x ) => {
        SCS.get( x.asInstanceOf[String] ) match {
          case Some( w ) => w.size + vale.asInstanceOf[Int]
          case None      => vale
        }
      } ) must beEqualTo( 7 )
    }

    " Extracting the Schematic Characteristic Clause Set Checking number of clause sets per configuration" in {
      val SCS = SchematicClauseSet( "omega", ctx ) match {
        case Some( x ) => x
        case None      => Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]()
      }
      SCS.keySet.fold( 0 )( ( vale, x ) => {
        SCS.get( x.asInstanceOf[String] ) match {
          case Some( w ) => w.keySet.fold( 0 )( ( mail, xx ) => {
            w.get( xx.asInstanceOf[HOLSequent] ) match {
              case Some( y ) => y.size + mail.asInstanceOf[Int]
              case None      => mail
            }
          } ).asInstanceOf[Int] + vale.asInstanceOf[Int]
          case None => vale
        }
      } ) must beEqualTo( 14 )
    }
    " Extracting the Schematic Characteristic Clause Set Checking that all clauses are there" in {
      val SCS = SchematicClauseSet( "omega", ctx ) match {
        case Some( x ) => x
        case None      => Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]()
      }
      SCS.keySet.fold( 0 )( ( vale, x ) => {
        SCS.get( x.asInstanceOf[String] ) match {
          case Some( w ) => w.keySet.fold( 0 )( ( mail, xx ) => {
            w.get( xx.asInstanceOf[HOLSequent] ) match {
              case Some( y ) => y.fold( 0 )( ( whale, zz ) => {
                val ( _, two: Set[SetSequent[Atom]] ) = zz
                two.size + whale.asInstanceOf[Int]
              } ).asInstanceOf[Int] + mail.asInstanceOf[Int]
              case None => mail
            }
          } ).asInstanceOf[Int] + vale.asInstanceOf[Int]
          case None => vale
        }
      } ) must beEqualTo( 24 )
    }

    "Extraction of a Schematic Clause set, size 7 from NiaSchema" in {
      val SCS = SchematicClauseSet( "omega", ctx ) match {
        case Some( x ) => x
        case None      => Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]()
      }
      val oclauses = SCS.get( "omega" ) match {
        case Some( x ) => x
        case None      => Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]()
      }
      val oExprCl = oclauses.get( oclauses.keySet.head ) match {
        case Some( x ) => x
        case None      => Set[( Expr, Set[SetSequent[Atom]] )]()
      }
      val oExpr = oExprCl.fold( oExprCl.head._1 )( ( x, y ) => {
        val ( one, _ ) = y.asInstanceOf[( Expr, Set[SetSequent[Atom]] )]
        if ( freeVariables( x.asInstanceOf[Expr] ).nonEmpty ) x
        else one
      } ).asInstanceOf[Expr]
      SchematicClauseSet.InstantiateClauseSetSchema( "omega", oclauses.keySet.head, SCS, Substitution( freeVariables( oExpr ).head, nat( 7 ) ) )( ctx )
      ok
    }
    "Schematic Clause set equivalent to non schematic" in {
      val SCS = SchematicClauseSet( "omega", ctx ) match {
        case Some( x ) => x
        case None      => Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]()
      }
      val oclauses = SCS.get( "omega" ) match {
        case Some( x ) => x
        case None      => Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]()
      }
      val oExprCl = oclauses.get( oclauses.keySet.head ) match {
        case Some( x ) => x
        case None      => Set[( Expr, Set[SetSequent[Atom]] )]()
      }
      val oExpr = oExprCl.fold( oExprCl.head._1 )( ( x, y ) => {
        val ( one, _ ) = y.asInstanceOf[( Expr, Set[SetSequent[Atom]] )]
        if ( freeVariables( x.asInstanceOf[Expr] ).nonEmpty ) x
        else one
      } ).asInstanceOf[Expr]
      val Sclauseset = SchematicClauseSet.InstantiateClauseSetSchema( "omega", oclauses.keySet.head, SCS, Substitution( freeVariables( oExpr ).head, nat( 3 ) ) )( ctx )
      val proof = instantiateProof.Instantiate( le"omega ${nat( 3 )}" )
      val thestruct = StructCreators.extract( proof, ctx )
      val nonclauseset = CharacteristicClauseSet( thestruct )
      val fin = Sclauseset.forall( x => {
        nonclauseset.exists( y =>
          x.antecedent.toSet.equals( y.antecedent.toSet ) &&
            x.succedent.toSet.equals( y.succedent.toSet ) )
      } )
      fin must beEqualTo( true )
    }
  }
  {
    import gniaSchema.ctx

    "gNia-schema both parameters zero" in {
      val proof = instantiateProof.Instantiate( le"omega ${nat( 0 )} ${nat( 0 )}" )
      ctx.check( proof )
      ok
    }
    "gNia-schema first parameter zero" in {
      val proof = instantiateProof.Instantiate( le"omega ${nat( 0 )} ${nat( 5 )}" )
      ctx.check( proof )
      ok
    }
    "gNia-schema second parameter zero" in {
      val proof = instantiateProof.Instantiate( le"omega ${nat( 5 )} ${nat( 0 )}" )
      ctx.check( proof )
      ok
    }
    "gNia-schema both parameters non-zero" in {
      val proof = instantiateProof.Instantiate( le"omega ${nat( 5 )} ${nat( 5 )}" )
      ctx.check( proof )
      ok
    }
    "gNia-schema both parameters non-zero large" in {
      val proof = instantiateProof.Instantiate( le"omega ${nat( 12 )} ${nat( 12 )}" )
      ctx.check( proof )
      ok
    }

    "Test if PlusComm induction proof is K-simple" in {
      IsKSimple( pluscomm ) must_== false
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
      IsKSimple( result ) must_== true
    }

    "Schematic Clause set equivalent to non schematic" in {
      val SCS = SchematicClauseSet( "omega", ctx ) match {
        case Some( x ) => x
        case None      => Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]()
      }
      val oclauses = SCS.get( "omega" ) match {
        case Some( x ) => x
        case None      => Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]()
      }
      val oExprCl = oclauses.get( oclauses.keySet.head ) match {
        case Some( x ) => x
        case None      => Set[( Expr, Set[SetSequent[Atom]] )]()
      }
      val oExpr = oExprCl.fold( oExprCl.head._1 )( ( x, y ) => {
        val ( one, _ ) = y.asInstanceOf[( Expr, Set[SetSequent[Atom]] )]
        if ( freeVariables( x.asInstanceOf[Expr] ).nonEmpty ) x
        else one
      } ).asInstanceOf[Expr]
      val Sclauseset = SchematicClauseSet.InstantiateClauseSetSchema( "omega", oclauses.keySet.head, SCS,
        Substitution( freeVariables( oExpr ).head, nat( 3 ) ).compose( Substitution( freeVariables( oExpr ).tail.head, nat( 3 ) ) ) )( ctx )
      /* val proof = LKProofSchemata.Instantiate( le"omega ${nat( 3 )}" )
       val thestruct = StructCreators.extract( proof, ctx )
       val nonclauseset = CharacteristicClauseSet( thestruct )
        val fin = Sclauseset.forall( x => {
         nonclauseset.exists( y=>
           x.antecedent.toSet.equals(y.antecedent.toSet) &&
             x.succedent.toSet.equals(y.succedent.toSet) )
       } )
       fin must beEqualTo( true )
       */
      //not really ok but for later work
      ok
    }
  }
*/
}

