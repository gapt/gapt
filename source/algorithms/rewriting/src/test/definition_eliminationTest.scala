package at.logic.algorithms.rewriting

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.language.fol._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.lk.propositionalRules.{AndRightRule, Axiom}
import at.logic.calculi.lk.quantificationRules.{ExistsRightRule, ForallRightRule, ForallLeftRule}
import at.logic.calculi.lk.definitionRules.{DefinitionLeftRule, DefinitionRightRule}

@RunWith(classOf[JUnitRunner])
class definition_eliminationTest extends SpecificationWithJUnit {
  object proof1 {
    val List(alphasym, betasym, xsym, ysym) = List("\\alpha","\\beta","x","y") map VariableStringSymbol
    val List(p,q,a,b) = List("P","Q","A","B") map ConstantStringSymbol
    val List(alpha,beta,x,y) = List(alphasym, betasym, xsym, ysym).map( (x : VariableStringSymbol) => FOLVar(x))
    val qa = Atom(q, alpha::Nil)
    val qx = Atom(q, x::Nil)
    val pab = Atom(p, List(alpha,beta))
    val pay = Atom(p, List(alpha,y))
    val pxy = Atom(p, List(x,y))
    val ax =  Atom(a,x::Nil)
    val bx = Atom(b,x::Nil)

    val i1 = Axiom(List(qa), List(qa))
    val i2 = ForallLeftRule(i1, i1.root.antecedent(0), qx, alpha)

    val i3 = Axiom(List(pab),List(pab))
    val i4 = ForallLeftRule(i3, i3.root.antecedent(0), AllVar(y,pay), beta)
    val i5 = ForallRightRule(i4, i4.root.succedent(0), AllVar(y,pay), beta)
    val i6 = DefinitionRightRule(i5, i5.root.succedent(0), ax)
    val i7 = ForallLeftRule(i6, i6.root.antecedent(0), AllVar(x, AllVar(y, pxy)), alpha)
    val i8 = DefinitionLeftRule(i7, i7.root.antecedent(0), AllVar(x, ax))
    val i9 = AndRightRule(i2, i8, i2.root.succedent(0), i8.root.succedent(0))
    val i10 = ExistsRightRule(i9, i9.root.succedent(0), ExVar(x, And(qx, ax)), alpha)
    val i11 = DefinitionRightRule(i10, i10.root.succedent(0), ExVar(x, bx))

    val def1 = (ax, AllVar(y, pxy))
    val def2 = (bx, And(qx,ax))
  }

  "Definition elmination" should {
    "work on a simple proof" in {
      skipped("not done yet")
      ok
    }
  }

}
