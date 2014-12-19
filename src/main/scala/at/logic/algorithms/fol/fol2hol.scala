package at.logic.algorithms.fol

import at.logic.language.fol.{FOLVar, FOLFormula, FOLExpression, Substitution => FOLSubstitution}
import at.logic.language.hol.{Substitution => HOLSubstitution, _}
import at.logic.language.lambda._
import at.logic.calculi.lk.base.FSequent

/**
 * Converts objects from the FOL layer to the HOL layer.
 *
 * (Sometimes it is necessary to convert terms to an upper layer: e.g. applying a FOL substitution to a HOL term does not
 * work if the result is not in FOL.)
 */
object fol2hol {
  def apply(e:FOLExpression) : HOLExpression = recreateWithFactory(e, HOLFactory).asInstanceOf[HOLExpression]

  def apply(f:FOLFormula) : HOLFormula = fol2hol(f.asInstanceOf[FOLExpression]).asInstanceOf[HOLFormula]

  def apply(f:FSequent) : FSequent =
    FSequent(f.antecedent.map(_ match {
      case folf: FOLFormula => fol2hol(folf)
      case holf: HOLFormula => holf
    }), f.succedent.map(_ match {
      case folf: FOLFormula => fol2hol(folf)
      case holf: HOLFormula => holf
    }))

  def apply(sub: FOLSubstitution) : HOLSubstitution = HOLSubstitution(sub.folmap.map(x=>
      (fol2hol(x._1).asInstanceOf[HOLVar], fol2hol(x._2)) ))
}

/**
 * Converts an object to another layer.  For example, a FOLFormula to the HOL layer, i.e. returning a HOLFormula.
 */
// This code is more generic but needs casting, since the factory can't do that
object recreateWithFactory {
  def apply(e:LambdaExpression, factory : FactoryA) : LambdaExpression = e match {
    case Var(name,t) => factory.createVar(e.asInstanceOf[Var].sym,t)
    case Const(name,t) => factory.createConst(e.asInstanceOf[Const].sym,t)
    case App(s,t) => factory.createApp(recreateWithFactory(s,factory), recreateWithFactory(t,factory))
    case Abs(x,t) => factory.createAbs(recreateWithFactory(x,factory).asInstanceOf[Var], recreateWithFactory(t,factory))
  }

  def apply(f:FSequent, factory : FactoryA) : FSequent = FSequent(
    f.antecedent.map(x => toHOLF(recreateWithFactory(x,factory))),
    f.succedent.map(x  => toHOLF(recreateWithFactory(x,factory))) )

  def apply[T <: LambdaExpression](sub : Substitution, factory : FactoryA, substitution_constructor : Map[Var,LambdaExpression] => Substitution) : Substitution =
    substitution_constructor(
      sub.map.map( x =>
      (toT[Var](recreateWithFactory(x._1,factory)), toT[T](recreateWithFactory(x._2,factory) ))
    ))

  private def toHOLF(exp:LambdaExpression) : HOLFormula = toT[HOLFormula](exp)
  private def toT[T](exp:LambdaExpression) : T = try {
    exp.asInstanceOf[T]
  } catch {
    case e:Exception =>
      throw new Exception("Could not convert "+exp+": "+e.getMessage, e)
  }
}

