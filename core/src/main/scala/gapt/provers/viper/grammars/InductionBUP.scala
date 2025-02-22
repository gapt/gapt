package gapt.provers.viper.grammars

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.ty.FunctionType
import gapt.expr.ty.To
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.grammars.InductionGrammar
import gapt.grammars.InductionGrammar.Production
import gapt.proofs.HOLSequent
import gapt.proofs.RichFormulaSequent
import gapt.proofs.expansion.InstanceTermEncoding
import gapt.logic.hol.PredicateEliminationProblem

case class InductionBUP(grammar: InductionGrammar, enc: InstanceTermEncoding, goal: Formula) {
  val X = rename(Var("X", FunctionType(To, Seq(grammar.alpha.ty, grammar.indTy) ++ grammar.gamma.map(_.ty))), containedNames(grammar))

  trait BupSequent {
    def theoryFormulas: HOLSequent
    def gammas: Vector[List[Expr]]
    def sequent: HOLSequent
    def formula: Formula
  }

  case class IndCase(constructor: Const, theoryFormulas: HOLSequent, gammas: Vector[List[Expr]]) extends BupSequent {
    val nu = grammar.nus(constructor)

    val indHyps: Vector[Formula] =
      for (gam <- gammas; nui <- nu if nui.ty == grammar.indTy)
        yield X(grammar.alpha, nui)(gam: _*).asInstanceOf[Formula]

    val indConcl: Formula = X(grammar.alpha, constructor(nu))(grammar.gamma: _*).asInstanceOf[Formula]

    val sequent: HOLSequent = indHyps ++: theoryFormulas :+ indConcl

    val formula: Formula = All.Block(grammar.alpha +: nu ++: grammar.gamma, sequent.toImplication)
  }

  case class EndCut(theoryFormulas: HOLSequent, gammas: Vector[List[Expr]]) extends BupSequent {
    val indFormulaInstances: Vector[Formula] =
      for (gam <- gammas)
        yield X(grammar.alpha, grammar.alpha)(gam: _*).asInstanceOf[Formula]

    val sequent: HOLSequent = indFormulaInstances ++: theoryFormulas :+ goal

    val formula: Formula = All.Block(grammar.alpha +: grammar.gamma, sequent.toImplication)
  }

  val indCases: Vector[IndCase] =
    grammar.nus.keys.toVector.map { c =>
      val prods = grammar.productions.filter(p => grammar.correspondingCase(p).forall(_ == c))
      val tauProds = prods.collect { case Production(List(tau), List(rhs)) if tau == grammar.tau => rhs }
      val gammaProds0 = prods.collect { case Production(gamma, rhs) if gamma == grammar.gamma => rhs }
      val gammaProds = if (gammaProds0.isEmpty) Vector(grammar.gamma) else gammaProds0
      IndCase(c, enc.decodeToInstanceSequent(tauProds), gammaProds)
    }

  val endCut: EndCut = {
    val prods = grammar.productions.filter(p => freeVariables(p.rhs).subsetOf(Set(grammar.alpha)))
    val tauProds = prods.collect { case Production(List(tau), List(rhs)) if tau == grammar.tau => rhs }
    val gammaProds0 = prods.collect { case Production(gamma, rhs) if gamma == grammar.gamma => rhs }
    val gammaProds = if (gammaProds0.isEmpty) Vector(grammar.gamma) else gammaProds0
    EndCut(enc.decodeToInstanceSequent(tauProds), gammaProds)
  }

  val bupSequents: Vector[BupSequent] = indCases :+ endCut

  val sequents: Vector[HOLSequent] = bupSequents.map(_.sequent)

  val formula: Formula = Ex(X, And(bupSequents.map(_.formula)))
  val predicateEliminationProblem: PredicateEliminationProblem = PredicateEliminationProblem(Seq(X), And(bupSequents.map(_.formula)))
}
