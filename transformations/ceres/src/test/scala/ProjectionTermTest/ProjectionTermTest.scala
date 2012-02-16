package at.logic.transformations.ceres

import _root_.at.logic.calculi.slk.{SchemaProof, SchemaProofDB}
import at.logic.calculi.lk.propositionalRules._
import at.logic.language.hol.{HOLFormula, HOLVarFormula}
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.transformations.ceres.unfolding.{applySchemaSubstitution, SchemaSubstitution1}
import org.specs._
import projections.printSchemaProof
import scala.io.Source
import at.logic.parsing.language.simple.SHLK
import java.io.File.separator

class ProjectionTermTest extends SpecificationWithJUnit {
    implicit val factory = defaultFormulaOccurrenceFactory
    import at.logic.language.schema._
    "ProjectionTermTest" should {
        "create a ProjectionTerm" in {
          println("\n\nProjectionTerm\n\n")


          val k = IntVar(new VariableStringSymbol("k"))
          val real_n = IntVar(new VariableStringSymbol("n"))
          val n = k
          val n1 = Succ(k); val n2 = Succ(n1); val n3 = Succ(n2)
          val k1 = Succ(k); val k2 = Succ(n1); val k3 = Succ(n2)
          val s = Set[FormulaOccurrence]()

          val i = IntVar(new VariableStringSymbol("i"))
          val A = IndexedPredicate(new ConstantStringSymbol("A"), i)
          val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
          val four = Succ(three);val five = Succ(four); val six = Succ(Succ(four));val seven = Succ(Succ(five));
          val A0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero())
          val A1 = IndexedPredicate(new ConstantStringSymbol("A"), one)
          val A2 = IndexedPredicate(new ConstantStringSymbol("A"), two)
          val A3 = IndexedPredicate(new ConstantStringSymbol("A"), three)

          val B0 = IndexedPredicate(new ConstantStringSymbol("B"), IntZero())

          val Ak = IndexedPredicate(new ConstantStringSymbol("A"), k)
          val Ai = IndexedPredicate(new ConstantStringSymbol("A"), i)
          val Ai1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(i))

          val orneg = at.logic.language.schema.Or(at.logic.language.schema.Neg(Ai).asInstanceOf[SchemaFormula], Ai1.asInstanceOf[SchemaFormula]).asInstanceOf[SchemaFormula]

          val Ak1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(k))
          val An = IndexedPredicate(new ConstantStringSymbol("A"), k)
          val An1 = IndexedPredicate(new ConstantStringSymbol("A"), n1)
          val An2 = IndexedPredicate(new ConstantStringSymbol("A"), n2)
          val An3 = IndexedPredicate(new ConstantStringSymbol("A"), n3)
  //             println("\n\n START \n\n")

          val ax1 = Axiom(A0 :: Nil, A0 ::Nil)
          val w1 = WeakeningRightRule(ax1, A3)
          val negl1 = NegLeftRule(w1,A0)
                   val ax2 = Axiom(A1 :: Nil, A1 ::Nil)
              val orl1 = OrLeftRule(negl1, ax2, at.logic.language.schema.Neg(A0), A1)
                      val ax3 = Axiom(A1 :: Nil, A1 ::Nil)
              val root = CutRule(orl1, ax3, A1)


//          val str = Source.fromFile("target" + separator + "test-classes" + separator + "adder.lks").toList.foldLeft("")((ch,res) => ch + res)
//          val proof_name = "psi"
//          val proof_name = "varphi"
//          val proof_name = "phi"
//          val proof_name = "chi"



          val str = Source.fromFile("target" + separator + "test-classes" + separator + "simple.lks").toList.foldLeft("")((ch,res) => ch + res)
          val proof_name = "\\psi"

          val map = SHLK.parseProof(str)

          val pterm = ProjectionTermCreators.extract(map.get(proof_name).get._2.get("root").get, Set.empty[FormulaOccurrence], map.get(proof_name).get._2.get("root").get)
          val t = PStructToExpressionTree.applyConsole(pterm)

          val ptermcc = ProjectionTermCreators.extract(map.get(proof_name).get._2.get("root").get, Set.empty[FormulaOccurrence] + map.get(proof_name).get._2.get("root").get.root.succedent.head, map.get(proof_name).get._2.get("root").get)
          val tcc = PStructToExpressionTree.applyConsole(ptermcc)


//          val pterm = ProjectionTermCreators.extract(root, Set.empty[FormulaOccurrence], root)
//          val t = pStructToExpressionTree(pterm)
          println(printSchemaProof(map.get(proof_name).get._2.get("root").get))
          println("\n\n\n\n\n\n\n\n\n\n")
          PStructToExpressionTree.printTree(t)
          println("\n\n")
//          ProjectionTermCreators(proof_name)

          println("\n\n\n\n\n\n\n\n\n\n")
          PStructToExpressionTree.printTree(tcc)
          println("\n\n")

//          printSchemaProof.sequentToString(ax2.root)

       }
   }
}