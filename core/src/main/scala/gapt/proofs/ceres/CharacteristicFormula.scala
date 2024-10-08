package gapt.proofs.ceres

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Eq
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Iff
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.expr.formula.constants.ExistsC
import gapt.expr.formula.constants.ForallC
import gapt.expr.formula.constants.QuantifierC
import gapt.expr.util.freeVariables
import gapt.logic.hol.toNNF
import gapt.proofs.Sequent
import gapt.proofs.context.mutable.MutableContext

import scala.util.matching.Regex

object Viperize {
  def apply(top: Expr)(implicit ctx: MutableContext): Sequent[Formula] = {
    val newAnte = ctx.normalizer.rules.map(x => {
      val pattern = new Regex("\\S+S[TF]*A[TF]*")
      if ((pattern findAllIn x.lhs.toString).nonEmpty) {
        val matrix = Iff(x.lhs, x.rhs)
        All.Block(freeVariables(matrix).toSeq, matrix)
      } else if (!(x.lhs.ty.toString.matches("o"))) {
        val matrix = Eq(x.lhs, x.rhs)
        val App(name, args) = x.lhs: @unchecked
        println(name)
        All.Block(freeVariables(matrix).toSeq, matrix)
      } else Bottom()
    })
    val newSuc = All.Block(freeVariables(top).toSeq, Imp(top, Bottom()))
    Sequent(newAnte.toSeq filterNot (x => x.alphaEquals(Bottom())), Seq(newSuc))
  }
}
object CharFormN extends StructVisitor[Formula, Unit] {
  def apply(struct: Struct): Formula = {
    val csf = recurse(
      struct,
      StructTransformer[Formula, Unit](
        { (x, _) => x },
        { (x, y, _) =>
          {
            if (x.equals(Top())) y
            else if (y.equals(Top())) x
            else And(x, y)
          }
        },
        Top(),
        { (x, y, _) =>
          {
            if (x.equals(Bottom())) y
            else if (y.equals(Bottom())) x
            else Or(x, y)
          }
        },
        Bottom(),
        { (x, _) => Neg(x) },
        { (_, _, _) => throw new Exception("Should not contain CLS terms") }
      ),
      ()
    )
    All.Block(freeVariables(csf).toSeq, csf)
  }
}
object CharFormPRN {
  def apply(scs: Map[CLS, (Struct, Set[Var])]): Map[Formula, (Formula, Set[Var])] = Support(
    scs,
    stTN
  )
  private val stTN = StructTransformer[Formula, Map[(String, Sequent[Boolean]), String]](
    { (x, _) => x },
    { (x, y, _) => And(x, y) },
    Top(),
    { (x, y, _) => Or(x, y) },
    Bottom(),
    { (x, _) => Neg(x) },
    Support.cF
  )
  def PR(chF: Map[Formula, (Formula, Set[Var])])(implicit ctx: MutableContext): Unit =
    Support.add(chF, ForallC)
}
object CharFormP extends StructVisitor[Formula, Unit] {
  def apply(struct: Struct): Formula = {
    val csf = recurse(
      struct,
      StructTransformer[Formula, Unit](
        { (x, _) => toNNF(Neg(x)) },
        { (x, y, _) =>
          {
            if (x.equals(Bottom())) y
            else if (y.equals(Bottom())) x
            else Or(x, y)
          }
        },
        Bottom(),
        { (x, y, _) =>
          {
            if (x.equals(Top())) y
            else if (y.equals(Top())) x
            else And(x, y)
          }
        },
        Top(),
        { (x, _) => Neg(x) },
        { (_, _, _) => throw new Exception("Should not contain CLS terms") }
      ),
      ()
    )
    Ex.Block(freeVariables(csf).toSeq, csf)
  }
}
object CharFormPRP {
  def apply(scs: Map[CLS, (Struct, Set[Var])]): Map[Formula, (Formula, Set[Var])] = Support(scs, stTP)
  private val stTP = StructTransformer[Formula, Map[(String, Sequent[Boolean]), String]](
    { (x, _) => Neg(x) },
    { (x, y, _) => Or(x, y) },
    Bottom(),
    { (x, y, _) => And(x, y) },
    Top(),
    { (x, _) => Neg(x) },
    Support.cF
  )
  def PR(chF: Map[Formula, (Formula, Set[Var])])(implicit ctx: MutableContext): Unit =
    Support.add(chF, ExistsC)
}

private object Support {
  def apply(
      scs: Map[CLS, (Struct, Set[Var])],
      stT: StructTransformer[Formula, Map[(String, Sequent[Boolean]), String]]
  ): Map[Formula, (Formula, Set[Var])] = {
    val names = structNames(scs)
    scs.map {
      s =>
        (s: @unchecked) match {
          case (CLS(Apps(Const(name, _, _), vs), cc), (st, vars)) =>
            (Atom(names((name, cc)), vs), (constructingForm(st, names, stT), vars))
        }
    }
  }

  def cF(pn: Expr, cc: Sequent[Boolean], mn: Map[(String, Sequent[Boolean]), String]): Formula = {
    val Apps(Const(name, _, _), vs) = pn: @unchecked
    Atom(mn.getOrElse((name, cc), { throw new Exception("Should be in map") }), vs)
  }
  // assuming NNFCNF
  private def QuantIntroForAll(f: Formula, evar: Set[Var]): Formula = f match {
    case And(x, And(Top(), Top()))     => QuantIntroForAll(x, evar)
    case And(And(Top(), Top()), x)     => QuantIntroForAll(x, evar)
    case And(Top(), x)                 => QuantIntroForAll(x, evar)
    case And(x, Top())                 => QuantIntroForAll(x, evar)
    case And(x, y)                     => And(QuantIntroForAll(x, evar), QuantIntroForAll(y, evar))
    case Or(x, Or(Bottom(), Bottom())) => QuantIntroForAll(x, evar)
    case Or(Or(Bottom(), Bottom()), x) => QuantIntroForAll(x, evar)
    case Or(Bottom(), x)               => QuantIntroForAll(x, evar)
    case Or(x, Bottom())               => QuantIntroForAll(x, evar)
    case Or(Neg(Neg(x)), Neg(Neg(y))) =>
      All.Block(evar.intersect(freeVariables(Or(x, y))).toSeq, Or(x, y))
    case Or(x, Neg(Neg(y))) =>
      All.Block(evar.intersect(freeVariables(Or(x, y))).toSeq, Or(x, y))
    case Or(Neg(Neg(x)), y) =>
      All.Block(evar.intersect(freeVariables(Or(x, y))).toSeq, Or(x, y))
    case Or(x, y) =>
      All.Block(evar.intersect(freeVariables(Or(x, y))).toSeq, Or(x, y))
    case Atom(_, _) =>
      All.Block(evar.intersect(freeVariables(f)).toSeq, f)
    case Top()           => Top()
    case Bottom()        => Bottom()
    case Neg(Neg(x))     => QuantIntroForAll(x, evar)
    case Neg(Atom(_, _)) => All.Block(evar.intersect(freeVariables(f)).toSeq, f)
    case Neg(x)          => Neg(QuantIntroForAll(x, evar))
  }
  private def QuantIntroExists(f: Formula, evar: Set[Var]): Formula = f match {
    case Or(x, Or(Bottom(), Bottom())) => QuantIntroExists(x, evar)
    case Or(Or(Bottom(), Bottom()), x) => QuantIntroExists(x, evar)
    case Or(Bottom(), x)               => QuantIntroExists(x, evar)
    case Or(x, Bottom())               => QuantIntroExists(x, evar)
    case Or(x, y)                      => Or(QuantIntroExists(x, evar), QuantIntroExists(y, evar))
    case And(x, And(Top(), Top()))     => QuantIntroExists(x, evar)
    case And(And(Top(), Top()), x)     => QuantIntroExists(x, evar)
    case And(Top(), x)                 => QuantIntroExists(x, evar)
    case And(x, Top())                 => QuantIntroExists(x, evar)
    case And(Neg(Neg(x)), Neg(Neg(y))) =>
      Ex.Block(evar.intersect(freeVariables(And(x, y))).toSeq, And(x, y))
    case And(x, Neg(Neg(y))) =>
      Ex.Block(evar.intersect(freeVariables(And(x, y))).toSeq, And(x, y))
    case And(Neg(Neg(x)), y) =>
      Ex.Block(evar.intersect(freeVariables(And(x, y))).toSeq, And(x, y))
    case And(x, y) =>
      Ex.Block(evar.intersect(freeVariables(And(x, y))).toSeq, And(x, y))
    case Atom(_, _) =>
      Ex.Block(evar.intersect(freeVariables(f)).toSeq, f)
    case Top()           => Top()
    case Bottom()        => Bottom()
    case Neg(Neg(x))     => QuantIntroExists(x, evar)
    case Neg(Atom(_, _)) => Ex.Block(evar.intersect(freeVariables(f)).toSeq, f)
    case Neg(x)          => Neg(QuantIntroExists(x, evar))
  }
  def add(chF: Map[Formula, (Formula, Set[Var])], qType: QuantifierC)(implicit ctx: MutableContext): Unit = {

    import gapt.proofs.context.update.ReductionRuleUpdate.reductionRulesAsReductionRuleUpdate

    val definitions: Map[Const, List[(Atom, Formula)]] = {
      for (case (f @ Atom(newEx, _), (form, vars)) <- chF.toList)
        yield (
          newEx.asInstanceOf[Const],
          (
            f,
            if (qType.equals(ForallC)) QuantIntroForAll(form, vars)
            else QuantIntroExists(form, vars)
          )
        )
    }.groupBy(_._1).map { case (pred, eqns) => (pred, eqns.map(_._2)) }

    definitions.keys.foreach { ctx += _ }
    ctx += definitions.values.flatten.map {
      case (lhs, rhs) => ReductionRule(lhs, rhs)
    }.toSeq
  }
  private def structNames(sss: Map[CLS, (Struct, Set[Var])]): Map[(String, Sequent[Boolean]), String] =
    sss.keySet.map { cls =>
      {
        val CLS(Apps(Const(name, _, _), _), cc) = cls: @unchecked
        val cutConfigChars = cc.map(b => if (b) 'T' else 'F')
        ((name, cc), name + "S" + cutConfigChars.succedent.mkString + "A" + cutConfigChars.antecedent.mkString)
      }
    }.toMap
  private object constructingForm extends StructVisitor[Formula, Map[(String, Sequent[Boolean]), String]] {
    def apply(struct: Struct, names: Map[(String, Sequent[Boolean]), String], stT: StructTransformer[Formula, Map[(String, Sequent[Boolean]), String]]): Formula =
      recurse(struct, stT, names)
  }
}
