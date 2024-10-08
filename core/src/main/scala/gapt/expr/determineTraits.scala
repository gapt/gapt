package gapt.expr

import gapt.expr.formula.Atom
import gapt.expr.formula.Formula
import gapt.expr.formula.constants.AndC
import gapt.expr.formula.constants.BottomC
import gapt.expr.formula.constants.EqC
import gapt.expr.formula.constants.ExistsC
import gapt.expr.formula.constants.ForallC
import gapt.expr.formula.constants.ImpC
import gapt.expr.formula.constants.LogicalConstant
import gapt.expr.formula.constants.NegC
import gapt.expr.formula.constants.OrC
import gapt.expr.formula.constants.TopC
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLAtomConst
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLFormulaWithBoundVar
import gapt.expr.formula.fol.FOLFunctionConst
import gapt.expr.formula.fol.FOLHeadType
import gapt.expr.formula.fol.FOLPartialAtom
import gapt.expr.formula.fol.FOLPartialFormula
import gapt.expr.formula.fol.FOLPartialTerm
import gapt.expr.formula.fol.FOLQuantifier
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.hol.HOLAtomConst
import gapt.expr.formula.hol.HOLPartialAtom
import gapt.expr.formula.prop.PropAtom
import gapt.expr.formula.prop.PropConnective
import gapt.expr.formula.prop.PropFormula
import gapt.expr.formula.prop.PropPartialFormula
import gapt.expr.ty.->:
import gapt.expr.ty.FunctionType
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.expr.ty.Ty

/**
 * Determine the correct traits for a given lambda expression.
 *
 * We assign to each lambda expression a set of traits it is supposed to have.  These traits are generated by a
 * (non-deterministic) tree automaton with rules such as App(NegC(), FOLFormula) -> FOLFormula.
 *
 * This object contains private classes for each of the resulting determinized states.  We could use anonymous types as
 * well, i.e. Var with FOLVar instead of Var_with_FOLVar, but these would show up in the debugger as
 * determineTraits$$anon$27, which is not particularly readable.
 */
private[expr] object determineTraits {
  private class Var_with_FOLVar(s: String, t: Ty) extends Var(s, t) with FOLVar
  private class Var_with_Formula(s: String, t: Ty) extends Var(s, t) with Formula
  private class Var_with_Atom(s: String, t: Ty) extends Var(s, t) with Atom
  private class Var_with_HOLPartialAtom(s: String, t: Ty, override val numberOfArguments: Int) extends Var(s, t) with HOLPartialAtom

  def forVar(sym: String, exptype: Ty): Var = exptype match {
    case Ti                   => new Var_with_FOLVar(sym, exptype)
    case To                   => new Var_with_Atom(sym, exptype)
    case FunctionType(To, ts) => new Var_with_HOLPartialAtom(sym, exptype, ts.length)
    case _                    => new Var(sym, exptype)
  }

  private class Const_with_FOLQuantifier(s: String, t: Ty, ps: List[Ty]) extends Const(s, t, ps) with FOLQuantifier
  private class Const_with_LogicalConstant(s: String, t: Ty, ps: List[Ty]) extends Const(s, t, ps) with LogicalConstant
  private class Const_with_PropConnective_with_PropFormula(s: String, t: Ty, ps: List[Ty]) extends Const(s, t, ps) with PropConnective with PropFormula
  private class Const_with_FOLConst(s: String, t: Ty, ps: List[Ty]) extends Const(s, t, ps) with FOLConst
  private class Const_with_PropAtom(s: String, t: Ty, ps: List[Ty]) extends Const(s, t, ps) with PropAtom
  private class Const_with_PropConnective(s: String, t: Ty, ps: List[Ty], override val numberOfArguments: Int) extends Const(s, t, ps) with PropConnective
  private class Const_with_PropPartialFormula(s: String, t: Ty, ps: List[Ty], override val numberOfArguments: Int) extends Const(s, t, ps) with PropPartialFormula
  private class Const_with_FOLFunctionConst(s: String, t: Ty, ps: List[Ty], override val numberOfArguments: Int) extends Const(s, t, ps) with FOLFunctionConst
  private class Const_with_FOLAtomConst(s: String, t: Ty, ps: List[Ty], override val numberOfArguments: Int) extends Const(s, t, ps) with FOLAtomConst
  private class Const_with_HOLAtomConst(s: String, t: Ty, ps: List[Ty], override val numberOfArguments: Int) extends Const(s, t, ps) with HOLAtomConst

  private class Const_with_FOLAtomConst_with_LogicalConstant(
      s: String,
      t: Ty,
      ps: List[Ty],
      override val numberOfArguments: Int
  ) extends Const(s, t, ps) with FOLAtomConst with LogicalConstant

  private class Const_with_HOLAtomConst_with_LogicalConstant(
      s: String,
      t: Ty,
      ps: List[Ty],
      override val numberOfArguments: Int
  ) extends Const(s, t, ps) with HOLAtomConst with LogicalConstant

  def forConst(sym: String, exptype: Ty, ps: List[Ty]): Const = (sym, exptype, ps) match {
    case ForallC(Ti) | ExistsC(Ti)    => new Const_with_FOLQuantifier(sym, exptype, ps)
    case ForallC(_) | ExistsC(_)      => new Const_with_LogicalConstant(sym, exptype, ps)
    case AndC() | OrC() | ImpC()      => new Const_with_PropConnective(sym, exptype, ps, 2)
    case NegC()                       => new Const_with_PropConnective(sym, exptype, ps, 1)
    case TopC() | BottomC()           => new Const_with_PropConnective_with_PropFormula(sym, exptype, ps)
    case EqC(Ti)                      => new Const_with_FOLAtomConst_with_LogicalConstant(sym, exptype, ps, 2)
    case EqC(_)                       => new Const_with_HOLAtomConst_with_LogicalConstant(sym, exptype, ps, 2)
    case (_, Ti, _)                   => new Const_with_FOLConst(sym, exptype, ps)
    case (_, To, _)                   => new Const_with_PropAtom(sym, exptype, ps)
    case (_, FOLHeadType(To, n), _)   => new Const_with_FOLAtomConst(sym, exptype, ps, n)
    case (_, FOLHeadType(Ti, n), _)   => new Const_with_FOLFunctionConst(sym, exptype, ps, n)
    case (_, FunctionType(To, ts), _) => new Const_with_HOLAtomConst(sym, exptype, ps, ts.length)
    case _                            => new Const(sym, exptype, ps)
  }

  private class App_with_PropFormula(f: Expr, a: Expr) extends App(f, a) with PropFormula
  private class App_with_FOLTerm(f: Expr, a: Expr) extends App(f, a) with FOLTerm
  private class App_with_FOLAtom(f: Expr, a: Expr) extends App(f, a) with FOLAtom
  private class App_with_FOLFormula(f: Expr, a: Expr) extends App(f, a) with FOLFormula
  private class App_with_Atom(f: Expr, a: Expr) extends App(f, a) with Atom
  private class App_with_Formula(f: Expr, a: Expr) extends App(f, a) with Formula
  private class App_with_FOLPartialTerm(f: Expr, a: Expr, override val numberOfArguments: Int) extends App(f, a) with FOLPartialTerm
  private class App_with_FOLPartialAtom(f: Expr, a: Expr, override val numberOfArguments: Int) extends App(f, a) with FOLPartialAtom
  private class App_with_FOLPartialFormula(f: Expr, a: Expr, override val numberOfArguments: Int) extends App(f, a) with FOLPartialFormula
  private class App_with_PropPartialFormula(f: Expr, a: Expr, override val numberOfArguments: Int) extends App(f, a) with PropPartialFormula
  private class App_with_HOLPartialAtom(f: Expr, a: Expr, override val numberOfArguments: Int) extends App(f, a) with HOLPartialAtom
  def forApp(f: Expr, a: Expr): App = (f, a) match {
    case (f: PropPartialFormula, a: PropFormula) => f.numberOfArguments match {
        case 1 => new App_with_PropFormula(f, a)
        case n => new App_with_PropPartialFormula(f, a, n - 1)
      }

    case (f: FOLPartialTerm, a: FOLTerm) => f.numberOfArguments match {
        case 1 => new App_with_FOLTerm(f, a)
        case n => new App_with_FOLPartialTerm(f, a, n - 1)
      }

    case (f: FOLPartialAtom, a: FOLTerm) => f.numberOfArguments match {
        case 1 => new App_with_FOLAtom(f, a)
        case n => new App_with_FOLPartialAtom(f, a, n - 1)
      }

    case (f: FOLPartialFormula, a: FOLFormula) => f.numberOfArguments match {
        case 1 => new App_with_FOLFormula(f, a)
        case n => new App_with_FOLPartialFormula(f, a, n - 1)
      }

    case (f: FOLQuantifier, _) => a match {
        case a: FOLFormulaWithBoundVar => new App_with_FOLFormula(f, a)
        case _                         => new App_with_Formula(f, a)
      }

    case (f: HOLPartialAtom, _) => f.numberOfArguments match {
        case 1 => new App_with_Atom(f, a)
        case n => new App_with_HOLPartialAtom(f, a, n - 1)
      }

    case _ => f.ty match {
        case _ ->: To => new App_with_Formula(f, a)
        case _        => new App(f, a)
      }
  }

  private class Abs_with_FOLFormulaWithBoundVar(v: Var, t: Expr) extends Abs(v, t) with FOLFormulaWithBoundVar
  def forAbs(v: Var, t: Expr): Abs = (v.ty, t) match {
    case (Ti, t: FOLFormula) => new Abs_with_FOLFormulaWithBoundVar(v, t)
    case _                   => new Abs(v, t)
  }
}
