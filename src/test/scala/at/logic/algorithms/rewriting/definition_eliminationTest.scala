package at.logic.algorithms.rewriting

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.language.fol._
import at.logic.language.lambda.symbols.{StringSymbol}
import at.logic.calculi.lk._
import at.logic.language.hol.HOLExpression
import at.logic.calculi.lk.base.{beSyntacticFSequentEqual, FSequent, Sequent, LKProof}
import at.logic.calculi.proofs.NullaryProof

@RunWith(classOf[JUnitRunner])
class definition_eliminationTest extends SpecificationWithJUnit {
  object proof1 {
    val List(alphasym, betasym, xsym, ysym) = List("\\alpha","\\beta","x","y")
    val List(p,q,a,b,tsym) = List("P","Q","A","B","t")
    val List(t) = List(tsym) map (FOLConst.apply)
    val List(alpha,beta,x,y) = List(alphasym, betasym, xsym, ysym).map(FOLVar.apply)
    val qa = Atom(q, alpha::Nil)
    val qx = Atom(q, x::Nil)
    val pab = Atom(p, List(alpha,beta))
    val pay = Atom(p, List(alpha,y))
    val pty = Atom(p, List(t,y))
    val pxy = Atom(p, List(x,y))
    val ax =  Atom(a,x::Nil)
    val at =  Atom(a,t::Nil)
    val aa =  Atom(a,alpha::Nil)
    val bx = Atom(b,x::Nil)
    val eqxt = Equation(x,t)
    val allypay = AllVar(y,pay)
    val allypty = AllVar(y,pty)
    val allypxy = AllVar(y, pxy)
    val allxypxy = AllVar(x, allypxy )
    val allxax = AllVar(x, ax)
    val exformula = ExVar(x, And(qx, ax))

    val i1 = Axiom(List(qa), List(qa))
    val i2 = ForallLeftRule(i1, i1.root.antecedent(0), AllVar(x,qx), alpha)

    val i3 = Axiom(List(pab),List(pab))
    val i4 = ForallLeftRule(i3, i3.root.antecedent(0), allypay, beta)
    val i5 = ForallRightRule(i4, i4.root.succedent(0), allypay, beta)
    val i6 = DefinitionRightRule(i5, i5.root.succedent(0), aa)
    val i7 = ForallLeftRule(i6, i6.root.antecedent(0), allxypxy , alpha)
    val i8 = DefinitionLeftRule(i7, i7.root.antecedent(0), allxax )
    val i9 = AndRightRule(i2, i8, i2.root.succedent(0), i8.root.succedent(0))
    val i10 = ExistsRightRule(i9, i9.root.succedent(0), exformula , alpha)
    val i11 = DefinitionRightRule(i10, i10.root.succedent(0), ExVar(x, bx))
    val i12 = AndLeft2Rule(i11, ax, i11.root.antecedent(0))

    val i13 = Axiom(eqxt::Nil, eqxt::Nil)
    val i14 = EquationLeft1Rule(i13,i12,i13.root.succedent(0), i12.root.antecedent(1), And(at, AllVar(x, qx)) )
    getoccids(i14, Nil) map println

    val def1 = (ax, AllVar(y, pxy))
    val def2 = (bx, And(qx,ax))
    val dmap = Map[HOLExpression, HOLExpression]() + def1 +def2

    def getoccids(p:LKProof, l : List[String]) : List[String] = p match {
      case r:NullaryProof[Sequent] =>
        val line = r.rule +": "+  r.root.antecedent.map(_.id).mkString(",") + " :- " + (r.root.succedent.map(_.id).mkString(","))
        line::Nil
      case r@UnaryLKProof(_, p1, root, _, _) =>
        val line = r.rule +": "+ root.antecedent.map(_.id).mkString(",") + " :- " + (root.succedent.map(_.id).mkString(","))
        getoccids(p1, line::l) :+ line
      case r@BinaryLKProof(_, p1, p2, root, _, _,  _) =>
        val line = r.rule +": "+ root.antecedent.map(_.id).mkString(",") + " :- " + (root.succedent.map(_.id).mkString(","))
        val rec1 = getoccids(p1, line::l)
        val rec2 = getoccids(p2, rec1)
        (rec1 ++ rec2) :+ line

    }

  }

  /**
    * The following tests are all commented out for the same reason. One of the
    * definitions used for them is the following:
    * 
    * A(x) -> \forall x. P(x, y)
    *
    * Which seems ok in principle. The problem happens when the
    * NaiveIncompleteMatchingAlgorithm is run. It sees that these are two
    * applications (of A to x and of forall to P(x,y)) and recursively calls
    * itself. When it gets to the variable x, it tries to create a substitution 
    * x <- P(x, y)
    *
    * But the substitution cannot be created, since the requirement that both
    * things need to have the same type fails. In this case, x has type i and
    * P(x,y) has type (i -> o).
    *
    */

  "Definition elimination" should {
    "work on formulas" in {
      skipped("Failing on HOL matching")
      val f = And(proof1.ax,Or(Atom(proof1.a,proof1.t::Nil), proof1.bx))
      val f_ = DefinitionElimination(proof1.dmap,f)
      println(f_)
      val correct_f = And(proof1.allypxy,Or(proof1.allypty, And(proof1.qx, proof1.allypxy)))
      f_ mustEqual(correct_f)
    }

    "work on a simple proof" in {
      skipped("Failing on HOL matching")
      import proof1._
      val elp = DefinitionElimination( dmap, i12 )
      println(elp)
      val expected = FSequent(List(AllVar(x,AllVar(y, pxy)), And(AllVar(y,pxy), AllVar(x,qx))), List(ExVar(x, And(qx, AllVar(y,pxy)))))
      expected must beSyntacticFSequentEqual(elp.root.toFSequent)
    }

    "work on a simple proof with equality" in {
      skipped("Failing on HOL matching")
      val elp = DefinitionElimination( proof1.dmap, proof1.i14 )
      println(elp)
      ok
    }

  }

}
