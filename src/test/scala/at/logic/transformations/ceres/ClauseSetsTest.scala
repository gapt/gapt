
package at.logic.transformations.ceres.clauseSets

import at.logic.algorithms.lk.{getAncestors, getCutAncestors}
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.occurrences._
import at.logic.calculi.slk.SchemaProofDB
import at.logic.language.hol.{Substitution => HOLSubstitution, Atom => HOLAtom, _}
import at.logic.language.schema.{Substitution => SchemaSubstitution, _}
import at.logic.language.lambda.types._
import at.logic.parsing.shlk_parsing.sFOParser
import at.logic.transformations.ceres.projections.{DeleteTautology, DeleteRedundantSequents}
import at.logic.transformations.ceres.struct._
import java.io.File.separator
import java.io.{FileInputStream, InputStreamReader}
import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner
import scala.io._
import scala.xml._

@RunWith(classOf[JUnitRunner])
class ClauseSetsTest extends SpecificationWithJUnit {

  sequential
  "ClauseSets" should {
    "- transform a Struct into a standard clause set" in {

      val a = HOLAtom(HOLVar( "a", To ))
      val b = HOLAtom(HOLVar( "b", To ))
      val c = HOLAtom(HOLVar( "c", To ))
      val d = HOLAtom(HOLVar( "d", To ))
      val fa = defaultFormulaOccurrenceFactory.createFormulaOccurrence(a, Nil)
      val fb = defaultFormulaOccurrenceFactory.createFormulaOccurrence(b, Nil)
      val fc = defaultFormulaOccurrenceFactory.createFormulaOccurrence(c, Nil)
      val fd = defaultFormulaOccurrenceFactory.createFormulaOccurrence(d, Nil)

      val struct = Times(Plus(A(fa), A(fb)), Plus(A(fc), A(fd)))
      val cs = StandardClauseSet.transformStructToClauseSet( struct )
      val res = cs.forall( seq => seq.antecedent.isEmpty && (
        seq =^ Sequent(Nil, List(fa,fc)) || seq =^ Sequent(Nil, List(fa,fd)) ||
        seq =^ Sequent(Nil, List(fb,fc)) || seq =^ Sequent(Nil, List(fb,fd))))
      res must beTrue
    }

    "test the schematic struct in journal_example.slk" in {
      val s = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("ceres-journal_example.lks"))
      val map = sFOParser.parseProof(s)
      val p = map.get("\\psi").get._2.get("root").get
      ok
    }


    "test the schematic struct in sEXP.slk" in {
      val s = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("sEXP.lks"))
      SchemaProofDB.clear
      val map = sFOParser.parseProof(s)
      val p1s = map.get("\\psi").get._2.get("root").get
      val p2s = map.get("\\varphi").get._2.get("root").get
      val p1b = map.get("\\psi").get._1.get("root").get
      val p2b = map.get("\\varphi").get._1.get("root").get

      val n = IntVar("n")
      val struct = StructCreators.extract(p1s, getCutAncestors(p1s))
      val cs : List[Sequent] = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet(struct) ))

      val new_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(IntVar("k"), Succ(IntZero()) )
      var subst = SchemaSubstitution(new_map)
      val gr = groundStruct(struct, subst.asInstanceOf[HOLSubstitution])
      val unfold_gr = unfoldGroundStruct(gr)

      val cs_gr = StandardClauseSet.transformStructToClauseSet(gr)
      ok
    }
  }

}
