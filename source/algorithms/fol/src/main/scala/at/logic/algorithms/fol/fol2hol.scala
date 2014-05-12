package at.logic.algorithms.fol

import at.logic.language.fol.{FOLVar, FOLFormula, FOLExpression, Substitution => FOLSubstitution}
import at.logic.language.hol.{Substitution => HOLSubstitution, _}
import at.logic.language.lambda._
import at.logic.calculi.lk.base.FSequent
import at.logic.language.lambda.symbols.StringSymbol

/**
 * Sometimes it is necessary to convert terms to an upper layer: e.g. applying a fol subtitution to a hol term does not
 * work if the result is not first order.
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
 * This code is more generic but needs casting, since the factory can't do that */
object recreateWithFactory {
  def apply(e:LambdaExpression, factory : FactoryA) : LambdaExpression = e match {
    case Var(name,t) => factory.createVar(StringSymbol(name),t)
    case App(s,t) => factory.createApp(s,t)
    case Abs(x,t) => factory.createAbs(x,t)
  }

  def apply(f:FSequent, factory : FactoryA) : FSequent = FSequent(
    f.antecedent.map(x => toHOLF(recreateWithFactory(x,factory))),
    f.succedent.map(x  => toHOLF(recreateWithFactory(x,factory))) )

  //TODO: Fix this!
  /*
  def apply[T <: LambdaExpression, U <: LambdaExpression](sub : Substitution[U], factory : FactoryA) : Substitution[T] =
    Substitution[T](
      sub.map.map( x =>
      (toT[Var](recreateWithFactory(x._1,factory)), toT[T](recreateWithFactory(x._2,factory) ))
    ))
*/

  private def toHOLF(exp:LambdaExpression) : HOLFormula = toT[HOLFormula](exp)
  private def toT[T](exp:LambdaExpression) : T = try {
    exp.asInstanceOf[T]
  } catch {
    case e:Exception =>
      throw new Exception("Could not convert "+exp+": "+e.getMessage, e)
  }
}

