package at.logic.gapt.proofs.ceres_omega

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.replaceAbstractions
import at.logic.gapt.expr.hol.{ HOLOrdering, containsQuantifierOnLogicalLevel, freeHOVariables }
import at.logic.gapt.formats.llk.LLKProofParser
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.proofs.ceres.CERES
import at.logic.gapt.proofs.lk.{ AtomicExpansion, DefinitionElimination, regularize, LKToLKsk }
import at.logic.gapt.proofs.lksk.LKskProof.LabelledFormula
import at.logic.gapt.proofs.lksk._
import at.logic.gapt.proofs.ral._
import at.logic.gapt.proofs._
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.utils.logging.Logger
import org.specs2.mutable._

import scala.io.Source

//TODO: Fix the test!

class ceres_omegaTest extends Specification with Logger {

  def load( file: String, pname: String ) =
    LLKProofParser.parseString( Source fromInputStream getClass.getClassLoader.getResourceAsStream( file ) mkString ).proof( pname )

  def prepareProof( file: String, proofname: String ) = {
    val p = LLKProofParser.parseString( Source.fromInputStream( getClass.getClassLoader getResourceAsStream file ).mkString )
    val elp = AtomicExpansion( DefinitionElimination( p.Definitions )( regularize( p.proof( proofname ) ) ) )
    val selp = LKToLKsk( elp )
    val struct = extractStructFromLKsk( selp )
    val ls = StandardClauseSet( struct )
    val proj = Projections( selp )
    ( selp, ls, struct, proj )
  }

  def refutation1( cs: Set[HOLSequent] ) = {
    val Some( c1 ) = cs.find( x => ( x.antecedent.size == 1 ) && ( x.succedent.size == 1 ) )
    val Some( c2 ) = cs.find( x => ( x.antecedent.size == 1 ) && ( x.succedent.size == 0 ) )
    val Some( c3 ) = cs.find( x => ( x.antecedent.size == 0 ) && ( x.succedent.size == 1 ) )

    val y = Var( "y", Ti )
    val x0 = Var( "x0", Ti )
    val p = Const( "P", Ti -> ( Ti -> To ) )
    val y0 = Var( "Y0", Ti -> To )

    val s = c2.antecedent( 0 ) match { case HOLAtom( _, List( s, _ ) ) => s }

    val sub1 = Substitution( y0, Abs( y, HOLAtom( p, List( s, y ) ) ) )
    val sub2 = Substitution( x0, s )

    val r1 = RalInitial( c1 map { Seq[LambdaExpression]() -> _ } )
    val r2 = RalInitial( c2 map { Seq[LambdaExpression]() -> _ } )
    val r3 = RalInitial( c3 map { Seq[LambdaExpression]() -> _ } )

    val r4 = RalSub( r1, sub1 )
    val r3a = RalSub( r3, sub2 )
    val r5 = RalCut( r3a, Seq( Suc( 0 ) ), r4, Seq( Ant( 0 ) ) )
    val r6 = RalCut( r5, Seq( Suc( 0 ) ), r2, Seq( Ant( 0 ) ) )
    r6
  }

  def refutation2( cs: Set[HOLSequent] ) = {
    val Some( c1 ) = cs.find( x => ( x.antecedent.size == 1 ) && ( x.succedent.size == 1 ) )
    val Some( c2 ) = cs.find( x => ( x.antecedent.size == 1 ) && ( x.succedent.size == 0 ) )
    val Some( c3 ) = cs.find( x => ( x.antecedent.size == 0 ) && ( x.succedent.size == 1 ) )

    val r1 = RalInitial( c1 map { Seq[LambdaExpression]() -> _ } )
    val r2 = RalInitial( c2 map { Seq[LambdaExpression]() -> _ } )
    val r3 = RalInitial( c3 map { Seq[LambdaExpression]() -> _ } )

  }

  "Ceres omega Projections" should {
    "be computed for a cut-free proof" in {
      val filename = "tape3ex.llk"
      val pdb = LLKProofParser.parseString( Source.fromInputStream( getClass.getClassLoader getResourceAsStream filename ).mkString )
      val elp = AtomicExpansion( DefinitionElimination( pdb.Definitions )( regularize( pdb proof "INFTAPE" ) ) )
      val selp = LKToLKsk( elp )
      val proj = Projections( selp, CERES.skipPropositional )
      val struct = extractStructFromLKsk( selp, CERES.skipPropositional )
      val css = StandardClauseSet( struct )

      css.size must_== proj.size
      ok( "done" )
    }

    "be computed for the ntape proof" in {
      val filename = "tape3ex.llk"
      val pdb = LLKProofParser.parseString( Source.fromInputStream( getClass.getClassLoader getResourceAsStream filename ).mkString )
      val elp = AtomicExpansion( DefinitionElimination( pdb.Definitions )( regularize( pdb proof "TAPEPROOF" ) ) )
      val selp = LKToLKsk( elp )
      val proj = Projections( selp, CERES.skipPropositional )
      val struct = extractStructFromLKsk( selp, CERES.skipPropositional )
      val css = StandardClauseSet( struct, false )
      //css.map( println )

      val pcss = proj.map( x => x._1.conclusion.zipWithIndex.filter( pair => x._2( pair._2 ) ).map( _._1 ) )
      def formulas( set: Set[Sequent[LabelledFormula]] ) = set.map( x => x.map( _._2 ) ).toList
      val ( pqs, abspcss ) = replaceAbstractions( formulas( pcss ) )
      val ( cqs, abscss ) = replaceAbstractions( formulas( css ) )

      debug( "=== projection css ===" )
      abspcss.map( x => debug( x.toString ) )
      debug( "=== projection replacement terms ===" )
      pqs.map( x => debug( x._2 + " -> " + x._1 ) )
      debug( TPTPFOLExporter.tptp_problem( abspcss.asInstanceOf[List[HOLClause]] ).toString )

      debug( "=== computed css ===" )
      abscss.map( x => debug( x.toString ) )
      debug( TPTPFOLExporter.tptp_problem( abscss.asInstanceOf[List[HOLClause]] ).toString )

      debug( "=== css replacement terms ===" )
      cqs.map( x => debug( x._2 + " -> " + x._1 ) )

      /*
      pcss.forall( x => css.exists( y =>
        StillmanSubsumptionAlgorithmHOL.subsumes( y.map( _._2 ), x.map( _._2 ) ) must beTrue ) )
        */
      pqs must_== ( cqs )

      //abspcss must_== abscss
      /**/
      ok( "done" )
    }

    "be computed for the first-order permutation example" in {
      val filename = "perm.llk"
      val pdb = LLKProofParser.parseString( Source.fromInputStream( getClass.getClassLoader getResourceAsStream filename ).mkString )
      val elp = AtomicExpansion( DefinitionElimination( pdb.Definitions )( regularize( pdb proof "AxProof" ) ) )
      val selp = LKToLKsk( elp )

      val cutformulas = selp.dagLike.breadthFirst.filter( { case Cut( _, _, _, _ ) => true; case _ => false } )
      cutformulas.size must_== 5 //4 from binary equation translation, 1 from proof

      val proj = Projections( selp, x => containsQuantifierOnLogicalLevel( x ) || freeHOVariables( x ).nonEmpty )
      proj.size must_== 4

      ok( "done" )
    }
  }

  "Ceres_omega" should {
    "handle a proof with a manual refutation (1)" in {
      //skipped( "ceres omega still has problems" )
      val ( p, cs, struct, proj ) = prepareProof( "llk/simple-leibnizeq.llk", "THEPROOF" )
      //val rp = refutation1( cs.map( _.map( _._2 ) ) )

      //val ( acnf, _ ) = ceres_omega( proj, rp, p.conclusion, struct )
      //TODO: fix LKskToExpansionProof
      //val et = LKskToExpansionProof( acnf )
      ok
    }
  }

}
