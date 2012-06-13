package at.logic.transformations.ceres

import at.logic.algorithms.lk.getCutAncestors
import at.logic.calculi.lk.base.{FSequent, Sequent}
import at.logic.calculi.occurrences.{defaultFormulaOccurrenceFactory, FormulaOccurrence}
import at.logic.transformations.ceres.projections.printSchemaProof
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.slk._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.schema._
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.execute.Success

@RunWith(classOf[JUnitRunner])
class projTerm3recTest extends SpecificationWithJUnit {
    implicit val factory = defaultFormulaOccurrenceFactory
    import at.logic.language.schema._
    "projTerm3recTest" should {
        "create a ProjectionTerm for the 3rec example" in {
          println("\n\nProjectionTerm 3rec\n\n")

          val i = IntVar(new VariableStringSymbol("i"))
          val k = IntVar(new VariableStringSymbol("k"))
          val n1 = Succ(k)
          val n2 = Succ(n1)
          val n3 = Succ(n2)
          val zero = IntZero()
          val one = Succ(IntZero())
          val two = Succ(Succ(IntZero()))
          val A0 = IndexedPredicate(new ConstantStringSymbol("A"), zero)
          val A1 = IndexedPredicate(new ConstantStringSymbol("A"), one)
          val A2 = IndexedPredicate(new ConstantStringSymbol("A"), two)
          val Ai = IndexedPredicate(new ConstantStringSymbol("A"), i)
          val Ai1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(i))
          val orneg = Or(Neg(Ai), Ai1)
          val An1 = IndexedPredicate(new ConstantStringSymbol("A"), n1)
          val An2 = IndexedPredicate(new ConstantStringSymbol("A"), n2)
          val An3 = IndexedPredicate(new ConstantStringSymbol("A"), n3)

          //-------- Definition of \psi_base

          val ax1 = Axiom(A0::Nil, A0::Nil)
          val negl1 = NegLeftRule(ax1,A0)
          val ax2 = Axiom(A1::Nil, A1::Nil)
          val orl1 = OrLeftRule(negl1, ax2, Neg(A0), A1)
          val negl2 = NegLeftRule(orl1,A1)
          val ax3 = Axiom(A2::Nil, A2::Nil)
          val orl2 = OrLeftRule(negl2, ax3, Neg(A1), A2)
          val ax4 = Axiom(A0::Nil, A0::Nil)
          val negl3 = NegLeftRule(ax4,A0)
          val ax5 = Axiom(A1::Nil, A1::Nil)
          val orl3 = OrLeftRule(negl3, ax5, Neg(A0), A1)
          val ax6 = Axiom(A0::Nil, A0::Nil)
          val andEqR1 = AndRightEquivalenceRule3(ax6,A0, BigAnd(i,Ai,zero,zero))
          val orl22 = AndRightRule(andEqR1, orl3, BigAnd(i,Ai,zero,zero), A1)
          val contrl1 = ContractionLeftRule(orl22, A0)
          val andEqR2 = AndRightEquivalenceRule1(contrl1, And(BigAnd(i,Ai,zero,zero), A1), BigAnd(i,Ai,zero,one))
          val andr2 = AndRightRule(orl2, andEqR2, A2, BigAnd(i,Ai,zero,one))
          val andr3 = AndRightEquivalenceRule1(andr2, And(A2, BigAnd(i,Ai,zero,one)), BigAnd(i,Ai,zero,two))
          val contrl2 = ContractionLeftRule(andr3, A0)
          val contrl3 = ContractionLeftRule(contrl2, Or(Neg(A0),A1))
          val andleq3 = AndLeftEquivalenceRule3(contrl3, Or(Neg(A0),A1), BigAnd(i, Or(Neg(Ai),Ai1), zero, zero))
          val andlb = AndLeftRule(andleq3, Or(Neg(A1),A2), BigAnd(i, Or(Neg(Ai),Ai1), zero, zero))
          val base = AndLeftEquivalenceRule1(andlb, And(Or(Neg(A1),A2), BigAnd(i, Or(Neg(Ai),Ai1), zero, zero)), BigAnd(i, Or(Neg(Ai),Ai1), zero, one))

          //----------- end of definition of \psi_base

          //-------- Definition of \psi_step

          val pl2 = SchemaProofLinkRule(FSequent(A0::BigAnd(i,orneg,zero,n1)::Nil, BigAnd(i,Ai,zero,n2)::Nil), "\\psi", k)
          val wl2 = WeakeningLeftRule(pl2, Neg(An2))
          val pl3 = SchemaProofLinkRule(FSequent(A0::BigAnd(i,orneg,zero,n1)::Nil, BigAnd(i,Ai,zero,n2)::Nil), "\\psi", k)
          val wl3 = WeakeningLeftRule(pl3, An3)
          val orl5 = OrLeftRule(wl2, wl3, Neg(An2), An3)
          val cont1l = ContractionLeftRule(orl5, A0)
          val cont2l = ContractionLeftRule(cont1l, BigAnd(i,orneg,zero,n1))
          val pr2 = ContractionRightRule(cont2l, BigAnd(i,Ai,zero,n2))

          val pl1 = SchemaProofLinkRule(FSequent(A0::BigAnd(i,orneg,zero,n1)::Nil, BigAnd(i,Ai,zero,n2)::Nil), "\\psi", k)
          val ax66 = Axiom(An2::Nil, An2::Nil)
          val andl222 = AndLeft2Rule(ax66, BigAnd(i,Ai,zero,n1), An2)
          val eq4 = AndLeftEquivalenceRule1(andl222, And(BigAnd(i,Ai,zero,n1), An2), BigAnd(i,Ai,zero,n2))
          val cut1 = CutRule(pl1, eq4, BigAnd(i,Ai,zero,n2))
          val neg4l = NegLeftRule(cut1, An2)
          val ax7 = Axiom(An3::Nil, An3::Nil)
          val pr3 = OrLeftRule(neg4l, ax7, Neg(An2), An3)

          val andr5 = AndRightRule(pr2, pr3, BigAnd(i,Ai,zero,n2), An3)
          val equiv = AndRightEquivalenceRule1(andr5, And(BigAnd(i,Ai,zero,n2), An3), BigAnd(i,Ai,zero,n3))
          val contr5 = ContractionLeftRule(equiv, A0)
          val contr55 = ContractionLeftRule(contr5, BigAnd(i,orneg,zero,n1))
          val contr555 = ContractionLeftRule(contr55, Or(Neg(An2), An3))
          val andl555 = AndLeftRule(contr555, BigAnd(i,orneg,zero,n1), Or(Neg(An2), An3))
          val eq33 = AndLeftEquivalenceRule1(andl555, And(BigAnd(i,orneg,zero,n1), Or(Neg(An2), An3)), BigAnd(i,orneg,zero,n2))
          val negr33 = NegRightRule(eq33, A0)
          val pl13 = OrRightRule(negr33, Neg(A0), BigAnd(i,Ai,zero,n3))

          val ax10 = Axiom(A0::Nil, A0::Nil)
          val nl6 = NegLeftRule(ax10, A0)
          val khin3 = SchemaProofLinkRule(FSequent(BigAnd(i,Ai,zero,n3)::Nil, BigAnd(i,Ai,zero,n3)::Nil), "\\chi", n3)
          val orl10 = OrLeftRule(nl6, khin3, Neg(A0), BigAnd(i,Ai,zero,n3))
          val step = CutRule(pl13, orl10, Or(Neg(A0), BigAnd(i,Ai,zero,n3)))

          //----------- end of definition of \psi_step

          //----------- Definition of \chi_0

          val chi0a = Axiom(A0::Nil, A0::Nil)
          val eqq1 = AndLeftEquivalenceRule3(chi0a, A0, BigAnd(i,Ai,zero,zero))
          val chi0 = AndRightEquivalenceRule3(eqq1, A0, BigAnd(i,Ai,zero,zero))

          //----------- end of definition of \chi_0

          //----------- Definition of \chi_k+1

          val prh = SchemaProofLinkRule(FSequent(BigAnd(i,Ai,zero,k)::Nil, BigAnd(i,Ai,zero,k)::Nil), "\\chi", k)
          val ax8 = Axiom(An1::Nil, An1::Nil)
          val andr6 = AndRightRule(prh, ax8, BigAnd(i,Ai,zero,k), An1)
          val eq44 = AndRightEquivalenceRule1(andr6, And(BigAnd(i,Ai,zero,k), An1), BigAnd(i,Ai,zero,n1))
          val andlc = AndLeftRule(eq44, BigAnd(i,Ai,zero,k), An1)
          val chin = AndLeftEquivalenceRule1(andlc, And(BigAnd(i,Ai,zero,k), An1), BigAnd(i,Ai,zero,n1))

          //----------- end of definition of \chi_k+1

          SchemaProofDB.clear
          SchemaProofDB.put(new SchemaProof("\\chi", k::Nil, FSequent(BigAnd(i,Ai,zero,k)::Nil, BigAnd(i,Ai,zero,k)::Nil), chi0, chin))
          SchemaProofDB.put(new SchemaProof("\\psi", k::Nil, FSequent(A0::BigAnd(i, orneg, zero, n1)::Nil, BigAnd(i,Ai,zero,n2)::Nil), base, step))

          def proof_name = "\\psi"
//          printSchemaProof(SchemaProofDB.get(proof_name).rec)
//          val p = SchemaProofDB.get(proof_name).rec
//          val pterm = ProjectionTermCreators.extract(p, Set.empty[FormulaOccurrence], getCutAncestors(p))
//          val t = PStructToExpressionTree.applyConsole(pterm)
          println("\n\n\n")
//          PStructToExpressionTree.printTree(t)
          ProjectionTermCreators.relevantProj(proof_name)
          println("\n\n\n")

          // specs2 require a least one Result, see org.specs2.specification.Example 
          Success()
        }
    }
}