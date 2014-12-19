package at.logic.transformations.ceres

import at.logic.algorithms.lk.{getCutAncestors, getAncestors}
import at.logic.algorithms.shlk._
import at.logic.calculi.lk._
import at.logic.calculi.lk.base.{Sequent, LKProof}
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.calculi.slk.{SchemaProof, SchemaProofDB}
import at.logic.language.schema._
import at.logic.parsing.shlk_parsing.{SHLK, sFOParser}
import at.logic.utils.ds.trees.BinaryTree
import at.logic.utils.testing.ClasspathFileCopier
import clauseSchema.ParseResSchema._
import clauseSchema._
import java.io.File.separator
import java.io.{FileInputStream, InputStreamReader}
import org.junit.runner.RunWith

import org.specs2.execute.Success
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class ProjectionTermTest extends SpecificationWithJUnit with ClasspathFileCopier {
  implicit val factory = defaultFormulaOccurrenceFactory

  sequential
  "ProjectionTermTest" should {
    "create a ProjectionTerm" in {
      val k = IntVar("k")
      val real_n = IntVar("n")
      val n = k
      val n1 = Succ(k); val n2 = Succ(n1); val n3 = Succ(n2)
      val k1 = Succ(k); val k2 = Succ(n1); val k3 = Succ(n2)
      val s = Set[FormulaOccurrence]()

      val i = IntVar("i")
      val A = IndexedPredicate("A", i)
      val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
      val four = Succ(three);val five = Succ(four); val six = Succ(Succ(four));val seven = Succ(Succ(five));
      val A0 = IndexedPredicate("A", IntZero())
      val A1 = IndexedPredicate("A", one)
      val A2 = IndexedPredicate("A", two)
      val A3 = IndexedPredicate("A", three)

      val B0 = IndexedPredicate("B", IntZero())

      val Ak = IndexedPredicate("A", k)
      val Ai = IndexedPredicate("A", i)
      val Ai1 = IndexedPredicate("A", Succ(i))

      val orneg = Or(Neg(Ai), Ai1.asInstanceOf[SchemaFormula])
      val Ak1 = IndexedPredicate("A", Succ(k))
      val An = IndexedPredicate("A", k)
      val An1 = IndexedPredicate("A", n1)
      val An2 = IndexedPredicate("A", n2)
      val An3 = IndexedPredicate("A", n3)

      val ax1 = Axiom(A0 :: Nil, A0 ::Nil)
      val w1 = WeakeningRightRule(ax1, A3)
      val negl1 = NegLeftRule(w1,A0)
      val ax2 = Axiom(A1 :: Nil, A1 ::Nil)
      val orl1 = OrLeftRule(negl1, ax2, Neg(A0), A1)
      val ax3 = Axiom(A1 :: Nil, A1 ::Nil)
      val root = CutRule(orl1, ax3, A1)


      val str = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("ceres-adder.lks"))
      val proof_name = "psi"


      val map = SHLK.parseProof(str)

      val pterm = ProjectionTermCreators.extract(map.get(proof_name).get._2.get("root").get, Set.empty[FormulaOccurrence], getCutAncestors(map.get(proof_name).get._2.get("root").get))
      val t = PStructToExpressionTree.applyConsole(pterm)

      val ptermcc = ProjectionTermCreators.extract(map.get(proof_name).get._2.get("root").get, Set.empty[FormulaOccurrence] + map.get(proof_name).get._2.get("root").get.root.succedent.head, getCutAncestors(map.get(proof_name).get._2.get("root").get))
      val tcc = PStructToExpressionTree.applyConsole(ptermcc)

      Success()
    }

    "should extract proj.term for the sEXP.lks" in {
      skipped("Class cast exception")

      SchemaProofDB.clear
      val s = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("sEXP.lks"))
      val res = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("resSchema1.rs"))
      val map = sFOParser.parseProof(s)
      ParseResSchema(res)
      val proof_name = "\\psi"
      val p1 = map.get(proof_name).get._2.get("root").get
      val p2 = map.get("\\varphi").get._2.get("root").get

      val fo = p2.root.succedent.head

      val pterm = ProjectionTermCreators.extract(p1, Set.empty[FormulaOccurrence], getCutAncestors(p1))
      val new_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(IntVar("k"), Succ(Succ(IntZero())).asInstanceOf[IntegerTerm])
      var sub = Substitution(new_map)
      val t = PStructToExpressionTree.applyConsole(pterm)

      val ground = GroundingProjectionTerm(pterm, sub)
      val t_ground = PStructToExpressionTree.applyConsole(ground)

      val ground_unfold = UnfoldProjectionTerm(ground)
      val t_ground_unfold = PStructToExpressionTree.applyConsole(ground_unfold)

      val rm_arrow_ground_unfold = RemoveArrowRules(ground_unfold)
      val t_rm_arrow_ground_unfold = PStructToExpressionTree.applyConsole(rm_arrow_ground_unfold)

      val projSet = ProjectionTermToSetOfProofs(rm_arrow_ground_unfold)

      val ground_proj_set = projSet.map(set => GroundingProjections(set, fo2SubstDB.map.toMap))

      Success()
    }

    "should extract proj.term for the sINDauto.lks" in {
      skipped("Class cast exception")

      SchemaProofDB.clear
      val s = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("sINDauto.lks"))
      val map = sFOParser.parseProof(s)
      val proof_name = "\\sigma"
      val p1 = map.get(proof_name).get._2.get("root").get
      val p2 = map.get("\\varphi").get._2.get("root").get
      val fo = p2.root.succedent.head

      val pterm = ProjectionTermCreators.extract(p1, Set.empty[FormulaOccurrence], getCutAncestors(p1))
      val new_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(IntVar("k"), Succ(Succ(IntZero())).asInstanceOf[IntegerTerm])
      var sub = Substitution(new_map)

      val t = PStructToExpressionTree.applyConsole(pterm)

      val ground = GroundingProjectionTerm(pterm, sub)
      val t_ground = PStructToExpressionTree.applyConsole(ground)

      val ground_unfold = RemoveArrowRules(UnfoldProjectionTerm(ground))
      val t_ground_unfold = PStructToExpressionTree.applyConsole(ground_unfold)

      val projSet = ProjectionTermToSetOfProofs(ground_unfold)

      Success()
    }
  }
}
