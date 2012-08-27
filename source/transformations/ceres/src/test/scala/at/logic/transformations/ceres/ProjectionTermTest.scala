package at.logic.transformations.ceres

import at.logic.calculi.slk.{SchemaProof, SchemaProofDB}
import at.logic.algorithms.lk.{getCutAncestors, getAncestors}
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.algorithms.shlk._
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.algorithms.shlk._
import java.io.File.separator
import java.io.{FileInputStream, InputStreamReader}
import org.specs2.execute.Success
import at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.language.hol.{HOLExpression, HOLFormula, HOLVarFormula}

@RunWith(classOf[JUnitRunner])
class ProjectionTermTest extends SpecificationWithJUnit {
    implicit val factory = defaultFormulaOccurrenceFactory
    import at.logic.language.schema._
    "ProjectionTermTest" should {
        "create a ProjectionTerm" in {
          println("\n\nProjectionTerm for the Adder.lks\n\n")


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


          val str = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "adder.lks"))
          val proof_name = "psi"
//          val proof_name = "varphi"
//          val proof_name = "phi"
//          val proof_name = "chi"



//          val str = Source.fromFile("target" + separator + "test-classes" + separator + "simple.lks").toList.foldLeft("")((ch,res) => ch + res)
//          val proof_name = "\\psi"

          val map = SHLK.parseProof(str)

          val pterm = ProjectionTermCreators.extract(map.get(proof_name).get._2.get("root").get, Set.empty[FormulaOccurrence], getCutAncestors(map.get(proof_name).get._2.get("root").get))
          val t = PStructToExpressionTree.applyConsole(pterm)

          val ptermcc = ProjectionTermCreators.extract(map.get(proof_name).get._2.get("root").get, Set.empty[FormulaOccurrence] + map.get(proof_name).get._2.get("root").get.root.succedent.head, getCutAncestors(map.get(proof_name).get._2.get("root").get))
          val tcc = PStructToExpressionTree.applyConsole(ptermcc)


//          val pterm = ProjectionTermCreators.extract(root, Set.empty[FormulaOccurrence], root)
//          val t = pStructToExpressionTree(pterm)
          println(printSchemaProof(map.get(proof_name).get._2.get("root").get))
          println("\n\n\n\n\n\n\n\n\n\n")
          PStructToExpressionTree.printTree(t)
          println("\n\n")
//          ProjectionTermCreators.genCC(proof_name)

//          println("\n\n")
//          PStructToExpressionTree.printTree(tcc)
//          println("\n\n")

//          ProjectionTermCreators.relevantProj(proof_name)
//          printSchemaProof.sequentToString(ax2.root)
          
          // specs2 require a least one Result, see org.specs2.specification.Example 
          Success()
       }


    "should extract proj.term for the journal paper" in {
      println("\n\nProjectionTerm for the journal paper\n\n")
      SchemaProofDB.clear
      val s = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "journal_example.lks"))
      val map = ParseQMON.parseProof(s)
//      val p2 = map.get("\\psi").get._2.get("root").get
      val proof_name = "\\varphi"
      val p2 = map.get(proof_name).get._2.get("root").get
      val p1 = map.get("\\psi").get._2.get("root").get
      val p1b = map.get("\\psi").get._1.get("root").get

      println("\n\n")
      printSchemaProof(p2)
      println("\n\n")
      val f = p2.root.succedent.head
//      val pterm = ProjectionTermCreators.extract(p2, Set.empty[FormulaOccurrence]+f, getCutAncestors(p2))
//      val t = PStructToExpressionTree.applyConsole(pterm)
//      PStructToExpressionTree.printTree(t)
      ProjectionTermCreators.relevantProj(proof_name)
//      val cclist1 = ProjectionTermCreators.getCC(p1, List.empty[FormulaOccurrence], p1)
//      val cclist2 = ProjectionTermCreators.getCC(p2, List.empty[FormulaOccurrence], p2)
//      ProjectionTermCreators.genCCProofToolBase("\\varphi")
//      ProjectionTermCreators.genCCProofToolBase("\\psi")
//      val l = ProjectionTermCreators.getCC(p2, p2.root.succedent.head::Nil, p2)
//      println("\nl = "+l)
//      println("\ncclist2 = "+cclist2)
//      val k = IntVar(new VariableStringSymbol("k")).asInstanceOf[Var]
//      val new_map = scala.collection.immutable.Map.empty[Var, IntegerTerm] + Pair(IntVar(new VariableStringSymbol("k")).asInstanceOf[Var], IntZero().asInstanceOf[IntegerTerm] )
//      var sub = new SchemaSubstitution1[HOLExpression](new_map)
//      val fo = p1.root.succedent.head
//      val fosub = sub(StepMinusOne.minusOne(fo.formula, k.asInstanceOf[IntVar]))
//      println("\nfo = "+fo.formula)
//      println("\nfosub = "+fosub)
      Success()
    }



  }
}




