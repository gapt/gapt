package at.logic.gapt.proofs.ceres_omega

import at.logic.gapt.examples._
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.replaceAbstractions
import at.logic.gapt.expr.hol.{ HOLOrdering, containsQuantifierOnLogicalLevel, freeHOVariables }
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.llk.{ ExtendedProofDatabase, LLKProofParser }
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.proofs.ceres._
import at.logic.gapt.proofs.lk.{ AtomicExpansion, CutRule, eliminateDefinitions, LKProof, LKToExpansionProof, regularize, skolemizeLK }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.resolution.{ Input, Resolution, Subst }
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.utils.logger._
import org.specs2.mutable._

//TODO: Fix the test!

class ceres_omegaTest extends Specification with SequentMatchers {

  def load( file: String, pname: String ) =
    LLKProofParser( ClasspathInputFile( file ) ).proof( pname )

  def prepareProof( file: String, proofname: String ) = {
    val p = LLKProofParser( ClasspathInputFile( file ) )
    val elp = AtomicExpansion( eliminateDefinitions( p.Definitions )( regularize( p.proof( proofname ) ) ) )
    val selp = skolemizeLK( elp )
    val struct = extractStruct( selp )
    val ls = StandardClauseSet( struct )
    val proj = Projections( selp )
    ( selp, ls, struct, proj )
  }

  def refutation1( cs: Set[HOLSequent] ) = {
    val Some( c1 ) = cs.find( x => ( x.antecedent.size == 1 ) && ( x.succedent.size == 1 ) )
    val Some( c2 ) = cs.find( x => ( x.antecedent.size == 1 ) && ( x.succedent.size == 0 ) )
    val Some( c3 ) = cs.find( x => ( x.antecedent.size == 0 ) && ( x.succedent.size == 1 ) )

    val y = Var( "y", Ti )
    val x0 = Var( "x", Ti )
    val p = Const( "P", Ti ->: Ti ->: To )
    val y0 = Var( "Y", Ti ->: To )

    val s = c2.antecedent( 0 ) match { case Atom( _, List( s, _ ) ) => s }

    val sub1 = Substitution( y0, Abs( y, Atom( p, List( s, y ) ) ) )
    val sub2 = Substitution( x0, s )

    val r1 = Input( c1 )
    val r2 = Input( c2 )
    val r3 = Input( c3 )

    val r4 = Subst( r1, sub1 )
    val r3a = Subst( r3, sub2 )
    val r5 = Resolution( r3a, Suc( 0 ), r4, Ant( 0 ) )
    val r6 = Resolution( r5, Suc( 0 ), r2, Ant( 0 ) )
    r6
  }

  def refutation2( cs: Set[HOLSequent] ) = {
    val Some( c1 ) = cs.find( x => ( x.antecedent.size == 1 ) && ( x.succedent.size == 1 ) )
    val Some( c2 ) = cs.find( x => ( x.antecedent.size == 1 ) && ( x.succedent.size == 0 ) )
    val Some( c3 ) = cs.find( x => ( x.antecedent.size == 0 ) && ( x.succedent.size == 1 ) )

    val r1 = Input( c1 )
    val r2 = Input( c2 )
    val r3 = Input( c3 )

  }

  "Ceres omega Projections" should {
    "be computed for a cut-free proof" in {
      val filename = "tape3ex.llk"
      val pdb = LLKProofParser( ClasspathInputFile( filename ) )
      val elp = AtomicExpansion( eliminateDefinitions( pdb.Definitions )( regularize( pdb proof "INFTAPE" ) ) )
      val selp = skolemizeLK( elp )
      val proj = Projections( selp, CERES.skipPropositional )
      val struct = extractStruct( selp, CERES.skipPropositional )
      val css = StandardClauseSet( struct )

      css.size must_== proj.size
      ok( "done" )
    }

    "be computed for the ntape proof" in {
      val filename = "tape3ex.llk"
      val pdb = LLKProofParser( ClasspathInputFile( filename ) )
      val elp = AtomicExpansion( eliminateDefinitions( pdb.Definitions )( regularize( pdb proof "TAPEPROOF" ) ) )
      val selp = skolemizeLK( elp )
      val proj = Projections( selp, CERES.skipPropositional )
      val struct = extractStruct( selp, CERES.skipPropositional )
      val css = StandardClauseSet( struct, false )
      //css.map( println )

      val pcss = proj.map( _.conclusion )
      val ( pqs, abspcss ) = replaceAbstractions( pcss.toList )
      val ( cqs, abscss ) = replaceAbstractions( css.toList )

      info( "=== projection css ===" )
      abspcss.map( x => info( x.toString ) )
      info( "=== projection replacement terms ===" )
      pqs.map( x => info( x._2 + " -> " + x._1 ) )
      info( TPTPFOLExporter.tptp_problem( abspcss.asInstanceOf[List[HOLClause]] ).toString )

      info( "=== computed css ===" )
      abscss.map( x => info( x.toString ) )
      info( TPTPFOLExporter.tptp_problem( abscss.asInstanceOf[List[HOLClause]] ).toString )

      info( "=== css replacement terms ===" )
      cqs.map( x => info( x._2 + " -> " + x._1 ) )

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
      val pdb = LLKProofParser( ClasspathInputFile( filename ) )
      val elp = AtomicExpansion( eliminateDefinitions( pdb.Definitions )( regularize( pdb proof "AxProof" ) ) )
      val selp = skolemizeLK( elp )

      val cutformulas = selp.dagLike.breadthFirst.filter( { case CutRule( _, _, _, _ ) => true; case _ => false } )
      cutformulas.size must_== 5 //4 from binary equation translation, 1 from proof

      val proj = Projections( selp, x => containsQuantifierOnLogicalLevel( x ) || freeHOVariables( x ).nonEmpty )
      proj.size must_== 4

      ok( "done" )
    }
  }

  "Ceres_omega" should {
    "handle a proof with a manual refutation (1)" in {
      val ( p, cs, struct, proj ) = prepareProof( "llk/simple-leibnizeq.llk", "THEPROOF" )
      val rp = refutation1( cs )

      val acnf = CERES( p.conclusion, proj, rp )
      val et = LKToExpansionProof( acnf )
      ok
    }

    "a simple intuitionistic proof" in {
      if ( !Prover9.isInstalled ) skipped( "No Prover9 installed!" )
      object CE extends AnalysisWithCeresOmega {
        override def proofdb() = ExtendedProofDatabase( Map[Formula, LKProof]( hof"THEPROOF" -> fol2.proof ), Map(), Map() )
        override def root_proof = "THEPROOF";
        override def skip_strategy() = CERES.skipNothing
      }

      CE.acnf.conclusion must beMultiSetEqual( CE.lksk_proof.conclusion )
    }

  }

}
