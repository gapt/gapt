package at.logic.algorithms.cutIntroduction

import at.logic.language.fol.{FOLVar, Function, FOLConst, FOLTerm}
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner


@RunWith(classOf[JUnitRunner])
class TreeGrammarDecompositionTest extends SpecificationWithJUnit {

  /**
   * Constructs a recursively called function term with
   * t as its base case
   * @param n how many iterative calls of s
   * @param t base case term (default: FOLConst("0"))
   * @return
   */
  def s(n:Int, t: FOLTerm=FOLConst("0")) : FOLTerm = n match {
    case 0 => t
    case i => Function("s", List(s(i-1, t)))
  }

  /**
   * Generating a language similar to that of a LinearExampleProof(n)
   * (i.e. w/o artificial functionsymbols)
   * with basecase t
   *
   */
  def testln(n: Int, t: FOLTerm= FOLConst("0")) : List[FOLTerm] = {
    List.range(0, n).map(x => s(x, t))
  }

  val alpha1 = FOLVar("α_1")
  val alpha2 = FOLVar("α_2")

  "TreeGrammarDecompositionPWM" should {

    "compute correctly the sufficient set of keys of testln(8) where n=1" in {
      val decomp = new TreeGrammarDecompositionPWM(testln(8), 1)
      decomp.suffKeys()

      val expected = testln(7, alpha1)

      decomp.keyList.toSet should beEqualTo(expected.toSet)
    }

    "compute correctly the sufficient set of keys of testln(8) where n=2" in {
      val decomp = new TreeGrammarDecompositionPWM(testln(8), 2)
      decomp.suffKeys()

      val expected = testln(7, alpha1) ++ testln(6, alpha2)

      decomp.keyList.toSet should beEqualTo(expected.toSet)
    }
  }
}
