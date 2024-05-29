package gapt.proofs.lk.util

import gapt.proofs.HOLSequent
import gapt.proofs.SequentIndex
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.BinaryLKProof
import gapt.proofs.lk.rules.InitialSequent
import gapt.proofs.lk.rules.UnaryLKProof

object consoleString {

  /**
   * Produces a console-readable string representation of the lowermost rule.
   *
   * @param p The rule to be printed.
   * @return
   */
  def apply(p: LKProof): String = p match {

    case InitialSequent(seq) =>
      produceString("", seq.toString, p.name)

    case UnaryLKProof(endSequent, subProof) =>
      val upperString = sequentToString(subProof.endSequent, p.auxIndices.head)
      val lowerString = sequentToString(endSequent, p.mainIndices)
      produceString(upperString, lowerString, p.name)

    case BinaryLKProof(endSequent, leftSubproof, rightSubProof) =>
      val upperString = sequentToString(leftSubproof.endSequent, p.auxIndices.head) +
        "    " +
        sequentToString(rightSubProof.endSequent, p.auxIndices.tail.head)

      val lowerString = sequentToString(endSequent, p.mainIndices)
      produceString(upperString, lowerString, p.name)
  }

  private def produceString(upperString: String, lowerString: String, ruleName: String): String = {

    val n = Math.max(upperString.length, lowerString.length) + 2
    val line = "-" * n
    val (upperDiff, lowerDiff) = (n - upperString.length, n - lowerString.length)
    val nLine = sys.props("line.separator")

    val upperNew = " " * Math.floor(upperDiff / 2).toInt + upperString + " " * Math.ceil(upperDiff / 2).toInt
    val lowerNew = " " * Math.floor(lowerDiff / 2).toInt + lowerString + " " * Math.ceil(lowerDiff / 2).toInt

    upperNew + nLine + line + ruleName + nLine + lowerNew
  }

  private def sequentToString(sequent: HOLSequent, highlightedFormulas: Seq[SequentIndex]): String = {
    val stringSequent = sequent map { _.toString() }
    highlightedFormulas.foldLeft(stringSequent) { (acc, i) =>
      val currentString = acc(i)
      val newString = "[" + currentString + "]"
      acc.updated(i, newString)
    }.toString

  }
}
