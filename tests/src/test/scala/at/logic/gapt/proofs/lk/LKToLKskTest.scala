package at.logic.gapt.proofs.lk

import at.logic.gapt.examples.{ Pi2Pigeonhole, lattice, tape }
import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.llk.loadLLK
import at.logic.gapt.proofs.{ Ant, Suc }
import org.specs2.mutable._

class LKToLKskTest extends Specification {
  "single strong quantifier inference" in {
    val f = FOLAtom( "p", FOLVar( "x" ) )
    val qf = All( FOLVar( "x" ), f )

    val p1 = LogicalAxiom( f )
    val p2 = ForallLeftRule( p1, qf )
    val p3 = ForallRightRule( p2, qf )

    val pSk = skolemizeInferences( p3 )
    pSk.conclusion must_== p3.endSequent
  }

  "a proof with contractions" in {
    //skipped( "bug: see https://github.com/gapt/gapt/issues/467" )
    /* This proof has 8 skolem constants, since the antecedent occurrence of the formula has 4 different strong
       Ex quantifier occurrences, their instantiation in the succedent creates 4 different paths.
     */

    val x = Var( "X", Ti -> To )
    val y = Var( "y", Ti )
    val f = Ex( y, All( x, App( x, y ) ) )
    val p0 = AtomicExpansion( f )
    val p1 = OrLeftRule( p0, Ant( 0 ), p0, Ant( 0 ) )
    val p2 = ContractionRightRule( p1, Suc( 0 ), Suc( 1 ) )
    val p3 = OrLeftRule( p2, Ant( 0 ), p2, Ant( 0 ) )
    //println( exportLLK( p3 ) )

    //println( llk.exportLLK( lkOld.LKToLKsk( lkNew2Old( p3 ) ) ) )

    skolemizeInferences( p3 )
    ok
  }

  "a proof with contractions and cut (1)" in {
    //skipped( "bug: see https://github.com/gapt/gapt/issues/467" )
    /* This proof has 2 skolem constants, since the pseudo cut on P allows us to contract both sides. Then we need to
       share both skolem constants in the two parent branches p1 and p2.
     */
    val x = Var( "X", Ti -> To )
    val y = Var( "y", Ti )
    val p = HOLAtom( Const( "P", To ), Nil )
    val f = Ex( y, All( x, App( x, y ) ) )
    val p0 = AtomicExpansion( f )
    val p1 = WeakeningRightRule( p0, p )
    val p2 = WeakeningLeftRule( p0, p )
    val p3 = CutRule( p1, p2, p )
    val p4 = ContractionLeftRule( p3, Ant( 0 ), Ant( 1 ) )
    val p5 = ContractionRightRule( p4, Suc( 0 ), Suc( 1 ) )

    skolemizeInferences( p5 )
    ok
  }

  "a proof with contractions and cut (2)" in {
    //skipped( "bug: see https://github.com/gapt/gapt/issues/467" )
    /* This proof has 3 skolem constants. Since we skip the contraction on the right hand side, we share the skolem
       constant for the All quantifier, but not for the Ex quantifier.
     */
    val x = Var( "X", Ti -> To )
    val y = Var( "y", Ti )
    val p = HOLAtom( Const( "P", To ), Nil )
    val f = Ex( y, All( x, App( x, y ) ) )
    val p0 = AtomicExpansion( f )
    val p0a = AtomicExpansion( f )
    val p1 = WeakeningRightRule( p0, p )
    val p2 = WeakeningLeftRule( p0a, p )
    val p3 = CutRule( p1, p2, p )
    val p4 = ContractionLeftRule( p3, Ant( 0 ), Ant( 1 ) )

    skolemizeInferences( p4 )
    ok
  }

  "a proof with contractions and cut (3)" in {
    /* This proof has 4 skolem constants. Since we skip the contraction on the left hand side, we have different
       skolem constants for the All quantifiers. Similar to the non-cut version, this breaks the homomorphy property and
       we also need to create fresh constants for the Ex quantifiers.
     */
    val x = Var( "X", Ti -> To )
    val y = Var( "y", Ti )
    val p = HOLAtom( Const( "P", To ), Nil )
    val f = Ex( y, All( x, App( x, y ) ) )
    val p0 = AtomicExpansion( f )
    val p0a = AtomicExpansion( f )
    val p1 = WeakeningRightRule( p0, p )
    val p2 = WeakeningLeftRule( p0a, p )
    val p3 = CutRule( p1, p2, p )
    val p4 = ContractionRightRule( p3, Suc( 0 ), Suc( 1 ) )

    skolemizeInferences( p4 )
    ok
  }

  "pigeonhole" in {
    skolemizeInferences( Pi2Pigeonhole.proof )
    ok
  }

  "lattice proof" in {
    val lk = regularize( DefinitionElimination( lattice.defs )( lattice.p ) )
    val lksk = skolemizeInferences( lk )
    lksk.conclusion must_== lk.conclusion
  }

  "tape proof" in {
    val lk = DefinitionElimination( tape.defs )( tape.p )
    val lksk = skolemizeInferences( lk )
    lksk.conclusion must_== lk.conclusion
  }

  "higher order tape proof" in {
    def load( fn: String ): LKProof = {
      val pdb = loadLLK( ClasspathInputFile( fn ) )
      AtomicExpansion( DefinitionElimination( pdb.Definitions )( pdb proof "TAPEPROOF" ) )
    }

    "2 copies tape proof" in {
      //skipped( "save time" )
      val lk = load( "tape3.llk" )
      val lksk = skolemizeInferences( lk )
      lksk.conclusion must_== lk.conclusion
    }
    "1 copy tape proof" in {
      //skipped( "save time" )
      val lk = load( "tape3ex.llk" )
      val lksk = skolemizeInferences( lk )
      lksk.conclusion must_== lk.conclusion
    }
  }
}
