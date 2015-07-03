package at.logic.gapt.proofs.ceres

import at.logic.gapt.cli.GAPScalaInteractiveShellLibrary._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.utils.testing.ClasspathFileCopier
import org.specs2.mutable._

import at.logic.gapt.proofs.lksk._
import TypeSynonyms._
import at.logic.gapt.proofs.resolution.ral._
import at.logic.gapt.proofs.ceres.clauseSets._

/**
 * Created by marty on 6/18/15.
 */
class ceres_omegaTest extends Specification with ClasspathFileCopier {

  def prepareProof( file: String, proofname: String ) = {
    val p = loadLLK( tempCopyOfClasspathFile( file ) )
    val elp = definitionElimination( p.Definitions, regularize( p.proof( proofname ) ) )
    val selp = LKToLKsk( elp )
    val struct = extractStruct( selp )
    val ls = SimpleStandardClauseSet( struct )
    val proj = computeProjections( selp )
    ( selp, ls, struct, proj )
  }

  def refutation1( cs: Set[FSequent] ) = {
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

    val r1 = InitialSequent( c1, ( List( EmptyLabel() ), List( EmptyLabel() ) ) )
    val r2 = InitialSequent( c2, ( List( EmptyLabel() ), List() ) )
    val r3 = InitialSequent( c3, ( List(), List( EmptyLabel() ) ) )

    val r4 = Sub( r1, sub1 )
    val r3a = Sub( r3, sub2 )
    val r5 = Cut( r3a, r4, r3a.root.succedent( 0 ) :: Nil, r4.root.antecedent( 0 ) :: Nil )
    val r6 = Cut( r5, r2, r5.root.succedent( 0 ) :: Nil, r2.root.antecedent( 0 ) :: Nil )
    r6
  }

  def refutation2( cs: Set[FSequent] ) = {
    val Some( c1 ) = cs.find( x => ( x.antecedent.size == 1 ) && ( x.succedent.size == 1 ) )
    val Some( c2 ) = cs.find( x => ( x.antecedent.size == 1 ) && ( x.succedent.size == 0 ) )
    val Some( c3 ) = cs.find( x => ( x.antecedent.size == 0 ) && ( x.succedent.size == 1 ) )

    val r1 = InitialSequent( c1, ( List( EmptyLabel() ), List( EmptyLabel() ) ) )
    val r2 = InitialSequent( c2, ( List( EmptyLabel() ), List() ) )
    val r3 = InitialSequent( c3, ( List(), List( EmptyLabel() ) ) )

  }

  "Ceres_omega" should {
    "handle a proof with a manual refutation (1)" in {
      val ( p, cs, struct, proj ) = prepareProof( "llk/simple-leibnizeq.llk", "THEPROOF" )
      val rp = refutation1( cs )

      val ( acnf, _ ) = CERESomega( proj, rp, sequentToLabelledSequent( p.root ), struct )
      val et = LKskToExpansionProof( acnf )
      ok
    }
  }

}
