package gapt.examples

import gapt.expr._
import gapt.proofs.ceres._
import gapt.proofs.gaptic._

object VeryWeakLexicoPHPSchemaVariantRefutation extends TacticsProof(VeryWeakLexicoPHPSchemaVariant.ctx) {
  val SCS: Map[CLS, (Struct, Set[Var])] = SchematicStruct("omega").getOrElse(Map())
  val CFPRN = CharFormPRN(SCS)
  CharFormPRN.PR(CFPRN)
  def sequentForm(input: Expr) = Viperize(le"omegaSFAF $input")
}
