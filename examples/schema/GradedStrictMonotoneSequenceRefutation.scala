package gapt.examples

import gapt.expr._
import gapt.proofs.ceres._
import gapt.proofs.gaptic._

object GradedStrictMonotoneSequenceRefutation extends TacticsProof(GradedStrictMonotoneSequenceSchema.ctx) {
  val SCS: Map[CLS, (Struct, Set[Var])] = SchematicStruct("omega").getOrElse(Map())
  val CFPRN = CharFormPRN(SCS)
  CharFormPRN.PR(CFPRN)
  def sequentForm(input: Expr, input2: Expr, input3: Expr) = Viperize(le"omegaSFAF $input $input2 $input3 ")
}
