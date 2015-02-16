package at.logic.proofs.lk.algorithms

import at.logic.language.hol._
import at.logic.language.lambda.symbols.StringSymbol
import at.logic.language.lambda.types.{Ti, To}
import at.logic.language.schema.{BigAnd, BigOr, IndexedPredicate, IntVar, IntZero, SchemaFormula, Succ, Or => OrS}
import at.logic.proofs.expansionTrees.{ExpansionSequent, toFSequent, ETAtom => AtomET, ETNeg => NegET, ETOr => OrET, ETStrongQuantifier => StrongQuantifierET, ETWeakQuantifier => WeakQuantifierET}
import at.logic.proofs.lk.base.{FSequent, beSyntacticFSequentEqual}
import at.logic.proofs.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class SolveTest extends SpecificationWithJUnit {
  implicit val factory = defaultFormulaOccurrenceFactory
  "SolveTest" should {
    "solve the sequents" in {
      val k = IntVar("k")
      val real_n = IntVar("n")
      val n = k
      val n1 = Succ(k); val n2 = Succ(n1); val n3 = Succ(n2)
      val k1 = Succ(k); val k2 = Succ(n1); val k3 = Succ(n2)
      val s = Set[FormulaOccurrence]()

      val i = IntVar("i")
      val A = IndexedPredicate("A", i)
      val B = IndexedPredicate("B", i)
      val C = IndexedPredicate("C", i)
      val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
      val four = Succ(three);val five = Succ(four); val six = Succ(Succ(four));val seven = Succ(Succ(five))
      val A0 = IndexedPredicate("A", IntZero())
      val A1 = IndexedPredicate("A", one)
      val A2 = IndexedPredicate("A", two)
      val A3 = IndexedPredicate("A", three)

      val B0 = IndexedPredicate("B", IntZero())

      val Ak = IndexedPredicate("A", k)
      val Ai = IndexedPredicate("A", i)
      val Ai1 = IndexedPredicate("A", Succ(i))
      val orneg = OrS(at.logic.language.schema.Neg(Ai).asInstanceOf[SchemaFormula], Ai1.asInstanceOf[SchemaFormula]).asInstanceOf[SchemaFormula]

      val Ak1 = IndexedPredicate("A", Succ(k))
      val An = IndexedPredicate("A", k)
      val An1 = IndexedPredicate("A", n1)
      val An2 = IndexedPredicate("A", n2)
      val An3 = IndexedPredicate("A", n3)

      val biga = BigAnd(i, A, zero, one)
      val bigo = BigOr(i, A, zero, one)
      val biga2 = BigAnd(i, A, zero, two)
      val bigo2 = BigOr(i, A, zero, two)

      val fseq = FSequent(A0 :: A1 :: Nil, bigo :: Nil)

      val p = solve.solvePropositional(fseq)

      // TODO: something with these...
      solve.solvePropositional(FSequent(HOLNeg(HOLAnd(HOLNeg(A), HOLNeg(B))) :: Nil, HOLOr(A , B) :: Nil))
      solve.solvePropositional(FSequent(HOLOr(HOLOr(A, B), C) :: Nil, A :: B :: C :: Nil))
      solve.solvePropositional(FSequent(HOLAnd(A , B) :: Nil, HOLNeg(HOLOr(HOLNeg(A), HOLNeg(B))) :: Nil))
      solve.solvePropositional(FSequent(A0 :: A1 :: A2 :: Nil, biga2 :: Nil))
      solve.solvePropositional(FSequent(A :: B :: C :: Nil, HOLAnd(HOLAnd(A, B), C) :: Nil))
      solve.solvePropositional(FSequent(bigo2 :: Nil, A0 :: A1 :: A2 :: Nil))
      
      val c2 = HOLConst(new StringSymbol("c"), Ti)
      val d2 = HOLConst(new StringSymbol("d"), Ti)
      val e2 = HOLConst(new StringSymbol("e"), Ti)
        
      val P = HOLConst(new StringSymbol("P"), Ti -> To)      

      val Pc2 = HOLAtom(P, c2::Nil)
      val Pd2 = HOLAtom(P, d2::Nil)
      val Pe2 = HOLAtom(P, e2::Nil)
      val andPc2Pd2 = HOLAnd(Pc2, Pd2)
      val impPc2Pd2 = HOLImp(Pc2, Pd2)
      val imp_andPc2Pd2_Pe2 = HOLImp(andPc2Pd2, Pe2)
      val orPc2Pd2 = HOLOr(Pc2, Pd2)
      val seq11 = FSequent(Pc2::Nil, Pc2::Nil)
      val seq12 = FSequent(andPc2Pd2::Nil, Pc2::Nil)
      val seq13 = FSequent(Pc2::Nil, orPc2Pd2::Nil)
      val seq14 = FSequent(andPc2Pd2::Nil, orPc2Pd2::Nil)
      val seq15 = FSequent(Pc2::impPc2Pd2::imp_andPc2Pd2_Pe2::Nil, Pe2::Nil)
      val seq16 = FSequent(Pc2::Nil, Pd2::Nil)

      solve.solvePropositional(seq16) must beEqualTo (None)
    }

    "prove non-atomic axioms (1)" in {
      import at.logic.language.hol._
      val List(x,y,z)    = List("x","y","z") map (x => HOLVar(StringSymbol(x), Ti))
      val List(u,v,w) = List("u","v","w") map (x => HOLVar(StringSymbol(x), Ti -> Ti))
      val List(a,b,c, zero)    = List("a","b","c","0") map (x => HOLConst(StringSymbol(x), Ti))
      val List(f,g,h,s)    = List("f","g","h","s") map (x => HOLConst(StringSymbol(x), Ti -> Ti))
      val List(p,q)      = List("P","Q") map (x => HOLConst(StringSymbol(x), Ti -> Ti))
      val List(_Xsym,_Ysym)    = List("X","Y") map (x => StringSymbol(x))
      val List(_X,_Y)    = List(_Xsym,_Ysym) map (x => HOLVar(x, Ti -> To))

      val xzero = HOLAtom(_X,List(zero))
      val xx = HOLAtom(_X,List(x))
      val xsx = HOLAtom(_X,List(HOLFunction(s,List(x))))

      val ind = HOLAllVar(_X, HOLImp(HOLAnd(xzero, HOLAllVar(x, HOLImp(xx,xsx) )), HOLAllVar(x, xx) ))
      val fs = FSequent(ind::Nil,ind::Nil)
      val proof = AtomicExpansion(fs)
      //check if the derived end-sequent is correct
      proof.root.toFSequent must beSyntacticFSequentEqual (fs)

      //check if three different eigenvariables were introduced and nothing more
      /* FIXME: replace toFormula.symbols call with call to getVars from utils
      val psymbols = proof.nodes.flatMap(x => x.asInstanceOf[LKProof].root.toFormula.symbols).filterNot(_.isInstanceOf[LogicalSymbolsA]).toSet
      val fssymbols = fs.formulas.flatMap(_.symbols).filterNot(_.isInstanceOf[LogicalSymbolsA]).toSet
      //println(psymbols)
      (psymbols diff fssymbols).size must_== 3
      (fssymbols diff psymbols) must beEmpty
      */
    }

    "prove non-atomic axioms (2)" in {
      import at.logic.language.hol._
      val List(x,y,z)    = List("x","y","z") map (x => HOLVar(StringSymbol(x), Ti))
      val List(u,v,w) = List("u","v","w") map (x => HOLVar(StringSymbol(x), Ti -> Ti))
      val List(a,b,c, zero)    = List("a","b","c","0") map (x => HOLConst(StringSymbol(x), Ti))
      val List(f,g,h,s)    = List("f","g","h","s") map (x => HOLConst(StringSymbol(x), Ti -> Ti))
      val List(psym,qsym)      = List("P","Q") map (x => StringSymbol(x))
      val List(_Xsym,_Ysym)    = List("X","Y") map (x => StringSymbol(x))
      val List(_X,_Y)    = List(_Xsym,_Ysym) map (x => HOLVar(x, Ti -> To))

      val Q = HOLConst(qsym, Ti -> (Ti -> To) )
      val P = HOLConst(qsym, Ti -> To)
      val xzero = HOLAtom(Q,List(y, HOLFunction(s,List(x))))

      val formula = HOLAllVar(x, HOLNeg(HOLExVar(y, xzero)))
      val fs = FSequent(List(HOLAtom(P,x::Nil), formula),List(formula, HOLAtom(P,y::Nil)))
      val proof = AtomicExpansion(fs)
      //check if the derived end-sequent is correct
      proof.root.toFSequent must beSyntacticFSequentEqual (fs)

      //check if two different eigenvariables were introduced and nothing more
      /* FIXME: replace toFormula.symbols call with call to getVars from utils
      val psymbols = proof.nodes.flatMap(x => x.asInstanceOf[LKProof].root.toFormula.symbols).filterNot(_.isInstanceOf[LogicalSymbolsA]).toSet
      val fssymbols = fs.formulas.flatMap(_.symbols).filterNot(_.isInstanceOf[LogicalSymbolsA]).toSet
      (psymbols diff fssymbols).size must_== 2
      (fssymbols diff psymbols) must beEmpty */
    }

    // tests of expansionProofToLKProof also in MiscTest, such that it can be used in combination with extractExpansionSequent

    "prove sequent where quantifier order matters" in {
      // example from Chaudhuri et.al.: A multi-focused proof system ...
      val List(x,y,u,v)    = List("x","y","u","v") map (x => HOLVar(StringSymbol(x), Ti))
      val c = HOLConst(StringSymbol("c"), Ti)
      val d = HOLConst(StringSymbol("d"), Ti -> To)


      val formula = HOLExVar(x, HOLOr( HOLNeg( HOLAtom(d, x::Nil) ), HOLAllVar(y, HOLAtom(d, y::Nil)))) // exists x (-d(x) or forall y d(y))

      val inst1 = OrET(
        NegET( AtomET( HOLAtom(d, u::Nil))), // -d(u)
        StrongQuantifierET( HOLAllVar(y, HOLAtom(d, y::Nil)), v, AtomET(HOLAtom(d, v::Nil))) // forall y d(y) +^v d(v)
      )

      val inst2 = OrET(
        NegET( AtomET( HOLAtom(d, c::Nil))), // -d(c)
        StrongQuantifierET( HOLAllVar(y, HOLAtom(d, y::Nil)), u, AtomET(HOLAtom(d, u::Nil))) // forall y d(y) +^u d(u)
      )

      // here, the second tree, containing c, must be expanded before u, as u is used as eigenvar in the c branch
      val et = WeakQuantifierET.applyWithoutMerge(formula, List( (inst1, u), (inst2, c)))
      val etSeq = new ExpansionSequent(Nil, et::Nil)

      val lkProof = solve.expansionProofToLKProof(toFSequent(etSeq), etSeq)
      lkProof.isDefined must beTrue
    }

  }
}

