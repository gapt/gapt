package gapt.formats.tptp

import gapt.expr.formula.Formula
import gapt.expr.formula.hol.universalClosure
import gapt.proofs.{SequentProof, RichFormulaSequent}

import scala.collection.mutable
import gapt.proofs.lk.LKProof
import gapt.proofs.Ant
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import gapt.expr.formula.Bottom

class sequentProofToTptp[Proof <: SequentProof[Formula, Proof]] {

  def line(label: String, role: FormulaRole, inf: Proof, annotations: Option[Annotations]): TptpInput =
    AnnotatedFormula("fof", label, role, universalClosure(inf.conclusion.toFormula), annotations)

  private def convertInference(
      labelMap: collection.Map[Proof, String],
      inf: Proof
  ): TptpInput = {
    val label = labelMap(inf)
    inf match {
      case p =>
        val inferenceName = p.longName.flatMap {
          case c if c.isUpper => "_" + c.toLower
          case c              => c.toString
        }.dropWhile(_ == '_').stripSuffix("_rule")

        val parents = p.immediateSubProofs.map(labelMap)

        line(
          label,
          "plain",
          inf,
          Some(Annotations(Source.Inference(inferenceName, Seq.empty, parents.map(p => ParentInfo(Source.Name(p)))), Seq.empty))
        )
    }
  }

  def apply(proof: Proof): TptpFile = {
    val inputs = Seq.newBuilder[TptpInput]

    val labelMap = mutable.Map[Proof, String]()
    for ((p, i) <- proof.dagLike.postOrder.zipWithIndex) {
      labelMap(p) = s"p$i"
      inputs += convertInference(labelMap, p)
    }

    TptpFile(inputs.result())
  }

}

object sequentProofToTptp {
  def apply[Proof <: SequentProof[Formula, Proof]](p: Proof): TptpFile =
    new sequentProofToTptp().apply(p)
}

def sequentProofToProoVerTptpProblemAndProof(proof: LKProof, negationOfConjectureIndex: Ant, problemPath: String): (TptpFile, TptpFile) = {
  def line(label: String, role: FormulaRole, inf: LKProof, annotations: Option[Annotations]): TptpInput =
    AnnotatedFormula("fof", label, role, universalClosure(inf.conclusion.toFormula), annotations)

  def convertInference(
      labelMap: collection.Map[LKProof, String],
      inf: LKProof
  ): TptpInput = {
    val label = labelMap(inf)
    inf match {
      case p =>
        val inferenceName = p.longName.flatMap {
          case c if c.isUpper => "_" + c.toLower
          case c              => c.toString
        }.dropWhile(_ == '_').stripSuffix("_rule")

        val parents = p.immediateSubProofs.map(labelMap)

        line(
          label,
          "plain",
          inf,
          Some(
            Annotations(
              Source.Inference(
                inferenceName,
                Seq(TptpTerm("status", TptpTerm("thm"))),
                parents.map(p => ParentInfo(Source.Name(p)))
              ),
              Seq.empty
            )
          )
        )
    }
  }

  def toRefutation(proof: LKProof): LKProof = {
    assert(proof.conclusion.succedent.size == 1)
    WeakeningRightRule(NegLeftRule(proof, proof.conclusion.succedent.head), Bottom())
  }

  val refutation = toRefutation(proof)
  val (negationOfConjecture, rest) = refutation.conclusion.focus(negationOfConjectureIndex)
  val axioms = rest.antecedent

  import gapt.expr.formula.Neg

  val Neg(conjecture) = negationOfConjecture: @unchecked
  val conjectureProblemInput = AnnotatedFormula("fof", "c", "conjecture", conjecture, None)
  val axiomProblemInputs = axioms.zipWithIndex.map((a, i) => AnnotatedFormula("fof", s"a$i", "axiom", a, None))
  val problemFile = TptpFile(axiomProblemInputs :+ conjectureProblemInput)

  val inputs = Seq.newBuilder[TptpInput]

  val axiomDerivationInputs = axioms.zipWithIndex.map { (a, i) =>
    val axiomLabel = s"a$i"
    AnnotatedFormula("fof", axiomLabel, "axiom", a, Some(Annotations(Source.File(problemPath, Some(axiomLabel)), Seq.empty)))
  }
  inputs ++= axiomDerivationInputs
  val conjectureLabel = "c"
  val conjectureDerivationInput = AnnotatedFormula(
    "fof",
    conjectureLabel,
    "conjecture",
    conjecture,
    Some(Annotations(Source.File(problemPath, Some(conjectureLabel)), Seq.empty))
  )
  inputs += conjectureDerivationInput
  val negatedConjectureDerivationInput = AnnotatedFormula(
    "fof",
    "nc",
    "negated_conjecture",
    Neg(conjecture),
    Some(
      Annotations(
        Source.Inference("negated_conjecture", Seq(TptpTerm("status", TptpTerm("cth"))), Seq(ParentInfo(Source.Name(conjectureLabel)))),
        Seq.empty
      )
    )
  )
  inputs += negatedConjectureDerivationInput

  val labelMap = mutable.Map.empty[LKProof, String]
  for ((p, i) <- refutation.dagLike.postOrder.zipWithIndex) {
    labelMap(p) = s"p$i"
    inputs += convertInference(labelMap, p)
  }

  val lastInferenceLabel = labelMap(refutation)

  val (axiomCuts, axiomParent, sequentAfterAxiomCuts) = axioms.zipWithIndex.foldLeft(
    (Seq.empty[TptpInput], lastInferenceLabel, refutation.conclusion)
  ) {
    case ((acc, parentLabel, sequent), (axiom, index)) =>
      val axiomLabel = s"a$index"
      val axiomCutLabel = s"acut$index"
      val (formula, nextSequent) = sequent.focus(sequent.indexOfInAnt(axiom))
      val nextAcc = acc :+ AnnotatedFormula(
        "fof",
        axiomCutLabel,
        "plain",
        nextSequent.toFormula,
        Some(Annotations(
          Source.Inference(
            "cut",
            Seq(TptpTerm("status", TptpTerm("thm"))),
            Seq(
              ParentInfo(Source.Name(parentLabel)),
              ParentInfo(Source.Name(axiomLabel))
            )
          ),
          Seq.empty
        ))
      )
      val nextParent = axiomCutLabel
      (nextAcc, nextParent, nextSequent)
  }
  inputs ++= axiomCuts

  assert(sequentAfterAxiomCuts.antecedent == Vector(Neg(conjecture)))
  inputs += AnnotatedFormula(
    "fof",
    "nc_cut",
    "plain",
    Bottom(),
    Some(Annotations(
      Source.Inference(
        "cut",
        Seq(TptpTerm("status", TptpTerm("thm"))),
        Seq(
          ParentInfo(Source.Name(axiomParent)),
          ParentInfo(Source.Name("nc"))
        )
      ),
      Seq.empty
    ))
  )

  val derivationFile = TptpFile(inputs.result())

  (problemFile, derivationFile)
}

def writeLKProofToProoVerTptpFromNegationOfConjecture(
    proof: LKProof,
    negationOfConjectureIndex: Ant,
    derivationsDirectory: String,
    baseName: String
) = {
  val problemFilePath = os.Path(derivationsDirectory, os.pwd) / "Problems" / s"$baseName.p"
  val (problemFile, derivationFile) = sequentProofToProoVerTptpProblemAndProof(
    proof,
    negationOfConjectureIndex,
    problemFilePath.toString
  )
  println(s"Writing problem file to $problemFilePath")
  os.write.over(problemFilePath, problemFile.toString)
  val derivationFilePath = os.Path(derivationsDirectory, os.pwd) / s"${baseName}_proof.p"
  println(s"Writing derivation file to $derivationFilePath")
  os.write.over(derivationFilePath, derivationFile.toString)
  println("Done.")
}
