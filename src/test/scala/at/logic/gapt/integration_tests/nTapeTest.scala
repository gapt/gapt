package at.logic.gapt.integration_tests

import java.io.IOException

import at.logic.gapt.algorithms.hlk.HybridLatexParser
import at.logic.gapt.formats.llk.HybridLatexExporter
import at.logic.gapt.algorithms.rewriting.DefinitionElimination
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ reduceHolToFol, undoHol2Fol, replaceAbstractions }
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs.lk.{ AtomicExpansion, regularize }
import at.logic.gapt.proofs.lk.base.LKProof
import at.logic.gapt.proofs.lksk.sequentToLabelledSequent
import at.logic.gapt.proofs.resolution.RobinsonToRal

import at.logic.gapt.provers.prover9._
import at.logic.gapt.proofs.algorithms.ceres.clauseSets.AlternativeStandardClauseSet
import at.logic.gapt.proofs.algorithms.ceres.projections.Projections
import at.logic.gapt.proofs.algorithms.ceres.struct.StructCreators

import at.logic.gapt.proofs.algorithms.ceres.ceres_omega
import at.logic.gapt.proofs.lksk.LKSKToExpansionProof
import at.logic.gapt.proofs.algorithms.skolemization.lksk.LKtoLKskc
import at.logic.gapt.utils.testing.ClasspathFileCopier
import at.logic.gapt.proofs.expansionTrees.{ ETAnd, ETImp, ETWeakQuantifier, ETSkolemQuantifier, ExpansionTree, ExpansionSequent }

import org.specs2.mutable._

class nTapeTest extends Specification with ClasspathFileCopier {
  def checkForProverOrSkip = Prover9.isInstalled must beTrue.orSkip

  def show( s: String ) = println( "+++++++++ " + s + " ++++++++++" )

  def f( e: LambdaExpression ): String = toLLKString( e )

  //sequential //skolemization is not thread safe - it shouldnt't make problems here, but in case there are issues, please uncomment

  class Robinson2RalAndUndoHOL2Fol( sig_vars: Map[String, List[Var]],
                                    sig_consts: Map[String, List[Const]],
                                    cmap: replaceAbstractions.ConstantsMap ) extends RobinsonToRal {
    val absmap = Map[String, LambdaExpression]() ++ ( cmap.toList.map( x => ( x._2.toString, x._1 ) ) )
    val cache = Map[LambdaExpression, LambdaExpression]()

    override def convert_formula( e: HOLFormula ): HOLFormula = {
      //require(e.isInstanceOf[FOLFormula], "Expecting prover 9 formula "+e+" to be from the FOL layer, but it is not.")

      BetaReduction.betaNormalize(
        undoHol2Fol.backtranslate( e, sig_vars, sig_consts, absmap ) )
    }

    override def convert_substitution( s: Substitution ): Substitution = {
      val mapping = s.map.toList.map {
        case ( from, to ) =>
          (
            BetaReduction.betaNormalize( undoHol2Fol.backtranslate( from, sig_vars, sig_consts, absmap, None ) ).asInstanceOf[Var],
            BetaReduction.betaNormalize( undoHol2Fol.backtranslate( to, sig_vars, sig_consts, absmap, None ) ) )
      }

      Substitution( mapping )
    }
  }

  object Robinson2RalAndUndoHOL2Fol {
    def apply( sig_vars: Map[String, List[Var]],
               sig_consts: Map[String, List[Const]],
               cmap: replaceAbstractions.ConstantsMap ) =
      new Robinson2RalAndUndoHOL2Fol( sig_vars, sig_consts, cmap )
  }

  def decompose( et: ExpansionTree ): List[ExpansionTree] = et match {
    case ETAnd( x, y ) => decompose( x ) ++ decompose( y );
    case _             => List( et )
  }

  def printStatistics( et: ExpansionSequent ) = {
    val indet = decompose( ( et.antecedent( 1 ) ) )( 2 )
    val List( ind1, ind2 ): List[ExpansionTree] = indet match {
      case ETWeakQuantifier( _, List(
        ( inst1, et1 ),
        ( inst2, et2 )
        ) ) =>
        List( inst1, inst2 )
    }

    val ( ind1base, ind1step ) = ind1 match {
      case ETImp( ETAnd(
        ETWeakQuantifier( _, List( ( _, base ) ) ),
        ETSkolemQuantifier( _, _,
          ETImp( _, ETWeakQuantifier( f, List( ( inst, step ) ) ) )
          )
        ), _ ) =>
        ( base, step )
    }

    val ( ind2base, ind2step ) = ind2 match {
      case ETImp( ETAnd(
        ETWeakQuantifier( _, List( ( _, base ) ) ),
        ETSkolemQuantifier( _, _,
          ETImp( _, ETWeakQuantifier( f, List( ( inst, step ) ) ) )
          ) ), _ ) =>
        ( base, step )
    }

    ( ind1base, ind1step, ind2base, ind2step ) match {
      case ( Abs( xb, sb ), Abs( xs, ss ), Abs( yb, tb ), Abs( ys, ts ) ) =>
        val map = Map[LambdaExpression, StringSymbol]()
        val counter = new { private var state = 0; def nextId = { state = state + 1; state } }

        val ( map1, sb1 ) = replaceAbstractions( sb, map, counter )
        val ( map2, ss1 ) = replaceAbstractions( ss, map1, counter )
        val ( map3, tb1 ) = replaceAbstractions( tb, map2, counter )
        val ( map4, ts1 ) = replaceAbstractions( ts, map3, counter )

        println( "base 1 simplified: " + f( Abs( xb, sb1 ) ) )
        println( "base 2 simplified: " + f( Abs( yb, tb1 ) ) )
        println( "step 1 simplified: " + f( Abs( xs, ss1 ) ) )
        println( "step 2 simplified: " + f( Abs( ys, ts1 ) ) )

        println( "With shortcuts:" )
        for ( ( term, sym ) <- map4 ) {
          println( "Symbol: " + sym )
          println( "Term:   " + f( term ) )
        }
    }

  }

  sequential
  "The higher-order tape proof" should {
    "do cut-elimination on the 2 copies tape proof (tape3.llk)" in {
      //skipped("works but takes a bit time")
      checkForProverOrSkip
      show( "Loading file" )
      val tokens = HybridLatexParser.parseFile( tempCopyOfClasspathFile( "tape3.llk" ) )
      val pdb = HybridLatexParser.createLKProof( tokens )
      show( "Eliminating definitions, expanding tautological axioms" )
      val elp = AtomicExpansion( DefinitionElimination( pdb.Definitions, regularize( pdb.proof( "TAPEPROOF" ) ) ) )
      show( "Skolemizing" )
      val selp = LKtoLKskc( elp )

      show( "Extracting struct" )
      val struct = StructCreators.extract( selp, x => containsQuantifierOnLogicalLevel( x ) || freeHOVariables( x ).nonEmpty )
      show( "Computing projections" )
      val proj = Projections( selp, x => containsQuantifierOnLogicalLevel( x ) || freeHOVariables( x ).nonEmpty )

      show( "Computing clause set" )
      val cl = AlternativeStandardClauseSet( struct )
      show( "Exporting to prover 9" )
      val ( cmap, folcl_ ) = replaceAbstractions( cl.toList )
      println( "Calculated cmap: " )
      cmap.map( x => println( x._1 + " := " + x._2 ) )

      val folcl = reduceHolToFol( folcl_ )
      folcl.map( println( _ ) )

      show( "Refuting clause set" )
      Prover9.refute( folcl ) match {
        case None =>
          ko( "could not refute clause set" )
        case Some( rp ) =>
          show( "Getting formulas" )
          val proofformulas = selp.nodes.flatMap( _.asInstanceOf[LKProof].root.toFSequent.formulas ).toList.distinct

          show( "Extracting signature from " + proofformulas.size + " formulas" )
          val ( sigc, sigv ) = undoHol2Fol.getSignature( proofformulas )

          show( "Converting to Ral" )

          val myconverter = Robinson2RalAndUndoHOL2Fol( sigv.map( x => ( x._1, x._2.toList ) ), sigc.map( x => ( x._1, x._2.toList ) ), cmap )
          val ralp = myconverter( rp )
          show( "Creating acnf" )
          val ( acnf, endclause ) = ceres_omega( proj, ralp, sequentToLabelledSequent( selp.root ), struct )

          show( "Compute expansion tree" )
          val et = LKSKToExpansionProof( acnf )
          show( " HOORAY! " )

          printStatistics( et )

          ok
      }

    }

    "do cut-elimination on the 1 copy tape proof (tape3ex.llk)" in {
      checkForProverOrSkip
      show( "Loading file" )
      val tokens = HybridLatexParser.parseFile( tempCopyOfClasspathFile( "tape3ex.llk" ) )
      val pdb = HybridLatexParser.createLKProof( tokens )
      show( "Eliminating definitions, expanding tautological axioms" )
      val elp = AtomicExpansion( DefinitionElimination( pdb.Definitions, regularize( pdb.proof( "TAPEPROOF" ) ) ) )
      show( "Skolemizing" )
      val selp = LKtoLKskc( elp )

      show( "Extracting struct" )
      val struct = StructCreators.extract( selp, x => containsQuantifierOnLogicalLevel( x ) || freeHOVariables( x ).nonEmpty )
      show( "Computing projections" )
      val proj = Projections( selp, x => containsQuantifierOnLogicalLevel( x ) || freeHOVariables( x ).nonEmpty )

      show( "Computing clause set" )
      val cl = AlternativeStandardClauseSet( struct )
      show( "Exporting to prover 9" )
      val ( cmap, folcl_ ) = replaceAbstractions( cl.toList )
      println( "Calculated cmap: " )
      cmap.map( x => println( x._1 + " := " + x._2 ) )

      val folcl = reduceHolToFol( folcl_ )
      folcl.map( println( _ ) )

      show( "Refuting clause set" )
      Prover9.refute( folcl ) match {
        case None =>
          ko( "could not refute clause set" )
        case Some( rp ) =>
          show( "Getting formulas" )
          val proofformulas = selp.nodes.flatMap( _.asInstanceOf[LKProof].root.toFSequent.formulas ).toList.distinct

          show( "Extracting signature from " + proofformulas.size + " formulas" )
          val ( sigc, sigv ) = undoHol2Fol.getSignature( proofformulas )

          show( "Converting to Ral" )

          val myconverter = Robinson2RalAndUndoHOL2Fol( sigv.map( x => ( x._1, x._2.toList ) ), sigc.map( x => ( x._1, x._2.toList ) ), cmap )
          val ralp = myconverter( rp )
          show( "Creating acnf" )
          val ( acnf, endclause ) = ceres_omega( proj, ralp, sequentToLabelledSequent( selp.root ), struct )

          show( "Compute expansion tree" )
          val et = LKSKToExpansionProof( acnf )
          show( " HOORAY! " )

          printStatistics( et )

          ok
      }

    }

  }

}
