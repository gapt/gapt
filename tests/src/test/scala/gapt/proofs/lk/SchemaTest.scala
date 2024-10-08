package gapt.proofs.lk

import gapt.expr._
import gapt.examples._
import gapt.expr.formula.{All, And}
import gapt.proofs.ceres._
import gapt.expr.formula.fol.natMaker
import gapt.expr.subst.Substitution
import gapt.expr.ty.TBase
import gapt.logic.clauseSubsumption
import gapt.logic.hol.CNFp
import gapt.proofs.Sequent
import gapt.proofs.context.facet.ProofDefinitions
import gapt.proofs.context.facet.Reductions
import gapt.proofs.context.immutable.ImmutableContext
import gapt.proofs.context.mutable.MutableContext
import gapt.provers.escargot.Escargot
import org.specs2.mutable.Specification
import gapt.proofs.gaptic._
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.InductionRule
import gapt.proofs.lk.util.ArithmeticInductionToSchema
import gapt.proofs.lk.util.IsKSimple
import gapt.proofs.lk.util.instantiateProof
import gapt.proofs.lk.util.regularize

class proofes(initialContext: ImmutableContext) extends TacticsProof(initialContext) {
  def prove0(SCS: Map[CLS, (Struct, Set[Var])]): LKProof = {
    val es = Sequent(Seq("Ant_0" -> hof"omegaSFAF(0)"), Seq())
    Lemma(es) {
      unfold("omegaSFAF") atMost 1 in "Ant_0"
      unfold("chiSTAF") atMost 2 in "Ant_0"
      unfold("phiSFAT") atMost 2 in "Ant_0"
      unfold("chiSTAF") atMost 2 in "Ant_0"
      escargot
    }
  }
  def prove1(SCS: Map[CLS, (Struct, Set[Var])]): LKProof = {
    val es = Sequent(Seq("Ant_0" -> hof"omegaSFAF(s(0))"), Seq())
    Lemma(es) {
      unfold("omegaSFAF") atMost 1 in "Ant_0"
      unfold("chiSTAF") atMost 10 in "Ant_0"
      unfold("phiSFAT") atMost 10 in "Ant_0"
      unfold("chiSTAF") atMost 10 in "Ant_0"
      escargot
    }
  }

  def prove0p(SCS: Map[CLS, (Struct, Set[Var])]): LKProof = {
    val es = Sequent(Seq(), Seq("Suc_0" -> hof"omegaSFAF(0)"))
    Lemma(es) {
      unfold("omegaSFAF") atMost 1 in "Suc_0"
      unfold("chiSTAF") atMost 2 in "Suc_0"
      unfold("phiSFAT") atMost 2 in "Suc_0"
      unfold("chiSTAF") atMost 2 in "Suc_0"
      escargot
    }
  }
  def prove1p(SCS: Map[CLS, (Struct, Set[Var])]): LKProof = {
    val es = Sequent(Seq(), Seq("Suc_0" -> hof"omegaSFAF(s(0))"))
    Lemma(es) {
      unfold("omegaSFAF") atMost 1 in "Suc_0"
      unfold("chiSTAF") atMost 10 in "Suc_0"
      unfold("phiSFAT") atMost 10 in "Suc_0"
      unfold("chiSTAF") atMost 10 in "Suc_0"
      escargot
    }
  }
}

class SchemaTest extends Specification {
  {
    import NdiffSchema.ctx
    "NdiffSchema Instantiate " in {
      val proof = instantiateProof(le"omega ${natMaker(15)}")
      ctx.check(proof)
      ok
    }
  }
  {

    import tautSchema.ctx
    //    implicit val ctx: ImmutableContext = tautSchema.ctx

    "simple schema basecase" in {
      val proof = instantiateProof.Instantiate(le"taut ${natMaker(0)}")
      ctx.check(proof)
      ok
    }

    "simple schema stepcase" in {
      val proof = instantiateProof.Instantiate(le"taut ${natMaker(1)}")
      ctx.check(proof)
      ok
    }
    "simple schema Large" in {
      val proof = instantiateProof.Instantiate(le"taut ${natMaker(6)}")
      ctx.check(proof)
      ok
    }
  }
  {
    import NiaSchema.ctx

    "Nia-schema basecase" in {
      val proof = instantiateProof.Instantiate(le"omega ${natMaker(0)}")
      ctx.check(proof)
      ok
    }
    "Nia-schema stepcase" in {
      val proof = instantiateProof.Instantiate(le"omega ${natMaker(1)}")
      ctx.check(proof)
      ok
    }

    " Nia-schema Large" in {
      val proof = instantiateProof.Instantiate(le"omega ${natMaker(4)}")
      ctx.check(proof)
      ok
    }

    "Nia-schema Super Large" in {
      val proof = instantiateProof.Instantiate(le"omega ${natMaker(12)}")
      ctx.check(proof)
      ok
    }

    " Nia-schema Clause Set Extraction Instance 3" in {
      val proof = instantiateProof.Instantiate(le"omega ${natMaker(3)}")
      ctx.check(proof)
      val thestruct = StructCreators.extract(proof)(ctx)
      CharacteristicClauseSet(thestruct)

      ok
    }
    " Nia-schema Characteristic Formula Extraction Instance 1" in {
      val proof = instantiateProof.Instantiate(le"omega ${natMaker(3)}")
      ctx.check(proof)
      val thestruct = StructCreators.extract(proof)(ctx)
      val Form = CharFormN(thestruct)
      subsumedClausesRemoval(CNFp(Form).toList)
      ok
    }

    " Nia-schema Clause Set Refutation  Instance 1" in {
      val proof = instantiateProof.Instantiate(le"omega ${natMaker(1)}")
      ctx.check(proof)
      val thestruct = StructCreators.extract(proof)(ctx)
      val cs = CharacteristicClauseSet(thestruct)
      val refutation = Escargot.getResolutionProof(cs)
      refutation must beSome
    }
    " Proof Nia-schema Characteristic Formula Instance 0" in {
      val SCS = SchematicStruct("omega")(ctx).getOrElse(Map())
      val ctx2 = ctx.newMutable
      CharFormPRN.PR(CharFormPRN(SCS))(ctx2)
      val proof = new proofes(ctx2.toImmutable).prove0(SCS)
      ctx2.check(proof)
      ok
    }
    " Proof Nia-schema Characteristic Formula Instance 1" in {
      val SCS = SchematicStruct("omega")(ctx).getOrElse(Map())
      val ctx2 = ctx.newMutable
      CharFormPRN.PR(CharFormPRN(SCS))(ctx2)
      val proof = new proofes(ctx2.toImmutable).prove1(SCS)
      ctx2.check(proof)
      ok
    }
    " Proof Nia-schema Positive Characteristic Formula Instance 0" in {
      val SCS = SchematicStruct("omega")(ctx).getOrElse(Map())
      val ctx2 = ctx.newMutable
      CharFormPRP.PR(CharFormPRP(SCS))(ctx2)
      val proof = new proofes(ctx2.toImmutable).prove0p(SCS)
      ctx2.check(proof)
      ok
    }
    " Proof Nia-schema Positive Characteristic Formula Instance 1" in {
      val SCS = SchematicStruct("omega")(ctx).getOrElse(Map())
      val ctx2 = ctx.newMutable
      CharFormPRP.PR(CharFormPRP(SCS))(ctx2)
      val proof = new proofes(ctx2.toImmutable).prove1p(SCS)
      ctx2.check(proof)
      ok
    }
    " Extracting the Schematic Characteristic Clause Set of the Niaschema" in {
      SchematicStruct("omega")(ctx) must beSome
      ok
    }
    " Extracting the Schematic Characteristic Clause Set Checking number of symbols" in {
      val SCS = SchematicStruct("omega")(ctx).getOrElse(Map())
      SCS.keySet.size must beEqualTo(6)
    }

    "Extraction of a Schematic Clause set, size 7 from NiaSchema" in {
      val SCS = SchematicStruct("omega")(ctx).getOrElse(Map())
      val top = CLS(le"omega ${natMaker(7)}", SCS.keySet.find(x => x.proof.toString.contains("omega")).get.config)
      InstanceOfSchematicStruct(top, SCS)(ctx)
      ok
    }
    "Schematic Clause set equivalent to non schematic" in {
      val SCS = SchematicStruct("omega")(ctx).getOrElse(Map())
      val top = CLS(le"omega ${natMaker(3)}", SCS.keySet.find(x => x.proof.toString.contains("omega")).get.config)
      val st = InstanceOfSchematicStruct(top, SCS)(ctx)
      val Sclauseset = subsumedClausesRemoval(CharacteristicClauseSet(st).toList)
      val proof = instantiateProof.Instantiate(le"omega ${natMaker(3)}")
      val thestruct = StructCreators.extract(proof)(ctx)
      val nonclauseset = subsumedClausesRemoval(CharacteristicClauseSet(thestruct).toList)
      val fin =
        (Sclauseset.forall(s => nonclauseset.exists(clauseSubsumption(_, s).isDefined)) ||
          nonclauseset.forall(s => Sclauseset.exists(clauseSubsumption(_, s).isDefined))) && nonclauseset.size == Sclauseset.size
      fin must beEqualTo(true)
    }
    "Schematic Clause set equivalent to Characteristic formula Clause Set" in {
      val SCS = SchematicStruct("omega")(ctx).getOrElse(Map())
      val top = CLS(le"omega ${natMaker(3)}", SCS.keySet.find(x => x.proof.toString.contains("omega")).get.config)
      val st = InstanceOfSchematicStruct(top, SCS)(ctx)
      val Sclauseset = subsumedClausesRemoval(CharacteristicClauseSet(st).toList)
      val proof = instantiateProof.Instantiate(le"omega ${natMaker(3)}")
      val thestruct = StructCreators.extract(proof)(ctx)
      val nonclauseset = subsumedClausesRemoval(CNFp(CharFormN(thestruct)).toList)
      val fin =
        (Sclauseset.forall(s => nonclauseset.exists(clauseSubsumption(_, s).isDefined)) ||
          nonclauseset.forall(s => Sclauseset.exists(clauseSubsumption(_, s).isDefined))) && nonclauseset.size == Sclauseset.size
      fin must beEqualTo(true)
    }
    "Schematic Formula Construction" in {
      val SCS = SchematicStruct("omega")(ctx).getOrElse(Map())
      val SchemForm = CharFormPRN(SCS)
      SCS.size must beEqualTo(SchemForm.size)
    }
    "Schematic Formula Construction PR Form" in {
      val SCS = SchematicStruct("omega")(ctx).getOrElse(Map())
      val SchemForm = CharFormPRN(SCS)
      val muCtx = ctx.newMutable
      CharFormPRN.PR(SchemForm)(muCtx)
      muCtx.get[Reductions].normalizer.rules.size must beEqualTo(8)
    }
  }
  {
    import gniaSchema.ctx
    "gNia-schema both parameters zero" in {
      val proof = instantiateProof.Instantiate(le"omega ${natMaker(0)} ${natMaker(0)}")
      ctx.check(proof)
      ok
    }
    "gNia-schema first parameter zero" in {
      val proof = instantiateProof.Instantiate(le"omega ${natMaker(0)} ${natMaker(5)}")
      ctx.check(proof)
      ok
    }
    "gNia-schema second parameter zero" in {
      val proof = instantiateProof.Instantiate(le"omega ${natMaker(5)} ${natMaker(0)}")
      ctx.check(proof)
      ok
    }
    "gNia-schema both parameters non-zero" in {
      val proof = instantiateProof.Instantiate(le"omega ${natMaker(5)} ${natMaker(5)}")
      ctx.check(proof)
      ok
    }
    "gNia-schema both parameters non-zero large" in {
      val proof = instantiateProof.Instantiate(le"omega ${natMaker(12)} ${natMaker(12)}")
      ctx.check(proof)
      ok
    }

    "Test if PlusComm induction proof is K-simple" in {
      import gapt.examples.theories.nat._
      IsKSimple(addcomm.proof) must_== false
    }

    "Test if K-simple PlusComm induction proof is K-simple" in {
      import gapt.examples.theories.nat._

      /**
       * Builds the conjunction of the main formulas of the given inference
       * by repeated application of the and:r rule.
       * @param p The default proof for the conjunction.
       * @param ps The proofs whose main formulas are to be connected by conjunction.
       */
      def inductionAndRightMacro(p: InductionRule, ps: Seq[InductionRule]): LKProof = {
        ps.foldRight[LKProof](p) {
          case (l, r) => AndRightRule(l, r, And(l.mainFormula, r.mainFormulas.head))
        }
      }

      val proofs: List[InductionRule] = addcomm.proof.subProofs.collect {
        case p: InductionRule =>
          val v: Var = p.cases.flatMap { _.eigenVars }.head
          val f: Expr = Substitution(p.formula.variable -> v)(p.formula.term)
          InductionRule(p.cases, Abs(v, f), v)
      }.toList

      val result: LKProof = proofs match {
        case p :: ps =>
          val x @ Var(_, _) = p.term: @unchecked
          val r = inductionAndRightMacro(p, ps)
          ForallRightRule(r, All(x, r.mainFormulas.head), x)
        case _ => addcomm.proof
      }
      IsKSimple(result) must_== true
    }
    "Schematic Clause set equivalent to non schematic" in {
      val SCS = SchematicStruct("omega")(ctx).getOrElse(Map())
      val top = CLS(le"omega ${natMaker(3)} ${natMaker(3)}", SCS.keySet.find(x => x.proof.toString.contains("omega")).get.config)
      val theStructWeNeed = InstanceOfSchematicStruct(top, SCS)(ctx)
      val SClauseSet = subsumedClausesRemoval(CharacteristicClauseSet(theStructWeNeed).toList)
      val proof = instantiateProof.Instantiate(le"omega ${natMaker(3)}  ${natMaker(3)}")
      val theStruct = StructCreators.extract(proof)(ctx)
      val nonClauseSet = subsumedClausesRemoval(CharacteristicClauseSet(theStruct).toList)
      val fin =
        (SClauseSet.forall(s => nonClauseSet.exists(clauseSubsumption(_, s).isDefined)) ||
          nonClauseSet.forall(s => SClauseSet.exists(clauseSubsumption(_, s).isDefined))) && nonClauseSet.size == SClauseSet.size
      fin must beEqualTo(true)
    }

    "Schematic Clause set equivalent to Characteristic formula Clause Set" in {
      val SCS = SchematicStruct("omega")(ctx).getOrElse(Map())
      val top = CLS(le"omega ${natMaker(3)} ${natMaker(3)}", SCS.keySet.find(x => x.proof.toString.contains("omega")).get.config)
      val theStructWeNeed = InstanceOfSchematicStruct(top, SCS)(ctx)
      val SClauseSet = subsumedClausesRemoval(CharacteristicClauseSet(theStructWeNeed).toList)
      val proof = instantiateProof.Instantiate(le"omega ${natMaker(3)}  ${natMaker(3)}")
      val theStruct = StructCreators.extract(proof)(ctx)
      val nonClauseSet = subsumedClausesRemoval(CNFp(CharFormN(theStruct)).toList)
      val fin =
        (SClauseSet.forall(s => nonClauseSet.exists(clauseSubsumption(_, s).isDefined)) ||
          nonClauseSet.forall(s => SClauseSet.exists(clauseSubsumption(_, s).isDefined))) && nonClauseSet.size == SClauseSet.size
      fin must beEqualTo(true)
    }
    "Schematic Formula Construction" in {
      val SCS = SchematicStruct("omega")(ctx).getOrElse(Map())
      val SchemForm = CharFormPRN(SCS)
      SCS.size must beEqualTo(SchemForm.size)
    }
    "Schematic Formula Construction PR Form" in {
      val SCS = SchematicStruct("omega")(ctx).getOrElse(Map())
      val SchemForm = CharFormPRN(SCS)
      val muCtx = ctx.newMutable
      CharFormPRN.PR(SchemForm)(muCtx)
      muCtx.get[Reductions].normalizer.rules.size must beEqualTo(18)
    }
  }
  {
    import FunctionIterationSchema.ctx
    "Instantiation of function interation schema" in {
      val proof = instantiateProof.Instantiate(le"phi (s (s (s (s (s (s 0)))))) ")
      ctx.check(proof)
      ok
    }
  }
  {
    import FunctionIterationRefutation.ctx
    "Instantiation of the negative characteristic formula of the function interation schema" in {
      val proof = instantiateProof.Instantiate(le"Top (s (s (s (s (s (s 0)))))) ")
      ctx.check(proof)
      ok
    }
  }
  {
    import FunctionIterationRefutationPos.ctx
    "Instantiation of the positive characteristic formula proof of the function interation schema" in {
      val proof = instantiateProof.Instantiate(le"Top (s (s (s (s (s (s 0)))))) ")
      ctx.check(proof)
      ok
    }
  }

  {
    import gapt.examples.theories.nat._
    "Constructing schematic pluscomm proof" in {
      implicit val ccon: MutableContext = ctx.newMutable
      ArithmeticInductionToSchema(addcomm.combined(), Const("Commutativity", TBase("nat")))
      val res = ccon.get[ProofDefinitions].components.keySet.map(x => ccon.get[ProofDefinitions].components.getOrElse(x, Set())).foldLeft(0)((x, y) => x + y.size)
      res must_== 7
    }

    "Instantiating schematic pluscomm proof" in {
      implicit val ccon: MutableContext = ctx.newMutable
      ArithmeticInductionToSchema(addcomm.combined(), Const("Commutativity", TBase("nat")))
      val P = hoc"Proof: nat>nat"
      val proof = regularize(instantiateProof(le"$P ${natMaker(10)}"))
      ctx.check(proof)
      ok
    }
  }

}
