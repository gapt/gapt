
package at.logic.gapt.proofs.ceres.clauseSets

import at.logic.gapt.proofs.lk.getCutAncestors
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.proofs.shlk.SchemaProofDB
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.expr.schema._
import at.logic.gapt.formats.shlk_parsing.sFOParser
import at.logic.gapt.proofs.ceres.projections.{ DeleteTautology, DeleteRedundantSequents }
import at.logic.gapt.proofs.ceres.struct._
import java.io.File.separator
import java.io.{ FileInputStream, InputStreamReader }
import org.specs2.mutable._
import scala.io._
import scala.xml._

class ClauseSetsTest extends Specification {

  sequential
  "ClauseSets" should {
    "- transform a Struct into a standard clause set" in {

      val a = HOLAtom( Var( "a", To ) )
      val b = HOLAtom( Var( "b", To ) )
      val c = HOLAtom( Var( "c", To ) )
      val d = HOLAtom( Var( "d", To ) )
      val fa = defaultFormulaOccurrenceFactory.createFormulaOccurrence( a, Nil )
      val fb = defaultFormulaOccurrenceFactory.createFormulaOccurrence( b, Nil )
      val fc = defaultFormulaOccurrenceFactory.createFormulaOccurrence( c, Nil )
      val fd = defaultFormulaOccurrenceFactory.createFormulaOccurrence( d, Nil )

      val struct = Times( Plus( A( fa ), A( fb ) ), Plus( A( fc ), A( fd ) ) )
      val cs = StandardClauseSet.transformStructToClauseSet( struct )
      val res = cs.forall( seq => seq.antecedent.isEmpty && (
        seq =^ OccSequent( Nil, List( fa, fc ) ) || seq =^ OccSequent( Nil, List( fa, fd ) ) ||
        seq =^ OccSequent( Nil, List( fb, fc ) ) || seq =^ OccSequent( Nil, List( fb, fd ) )
      ) )
      res must beTrue
    }

    "test the schematic struct in journal_example.slk" in {
      val s = new InputStreamReader( getClass.getClassLoader.getResourceAsStream( "ceres-journal_example.lks" ) )
      val map = sFOParser.parseProof( s )
      val p = map.get( "\\psi" ).get._2.get( "root" ).get
      ok
    }

    "test the schematic struct in sEXP.slk" in {
      val s = new InputStreamReader( getClass.getClassLoader.getResourceAsStream( "sEXP.lks" ) )
      SchemaProofDB.clear
      val map = sFOParser.parseProof( s )
      val p1s = map.get( "\\psi" ).get._2.get( "root" ).get
      val p2s = map.get( "\\varphi" ).get._2.get( "root" ).get
      val p1b = map.get( "\\psi" ).get._1.get( "root" ).get
      val p2b = map.get( "\\varphi" ).get._1.get( "root" ).get

      val n = IntVar( "n" )
      val struct = StructCreators.extract( p1s, getCutAncestors( p1s ) )
      val cs: List[OccSequent] = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet( struct ) ) )

      val new_map = Map.empty[Var, IntegerTerm] + Tuple2( IntVar( "k" ), Succ( IntZero() ) )
      var subst = SchemaSubstitution( new_map )
      val gr = groundStruct( struct, subst.asInstanceOf[Substitution] )
      val unfold_gr = unfoldGroundStruct( gr )

      val cs_gr = StandardClauseSet.transformStructToClauseSet( gr )
      ok
    }
  }

}
