package gapt.expr.util

import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.formula.Atom
import gapt.expr.formula.Formula
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLExpression
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.expr.preExpr
import gapt.expr.ty.Ty
import gapt.expr.util.ExpressionParseHelper.Splice
import gapt.formats.babel._
import gapt.proofs.FOLClause
import gapt.proofs.FOLSequent
import gapt.proofs.HOLClause
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.logic.hol.PredicateEliminationProblem
import gapt.expr.formula.Ex
import gapt.expr.formula.hol.containsHOQuantifier
import gapt.expr.formula.hol.freeHOVariables.isHOVar

object ExpressionParseHelper {
  abstract class Splice[+ForType] {
    def spliceIn: preExpr.Expr
  }
  implicit class IdentifierSplice[+T](val ident: String) extends Splice[T] {
    def spliceIn = preExpr.Ident(ident, preExpr.freshMetaType(), None)
  }
  implicit class ExpressionSplice[+ExprType <: Expr](val expr: ExprType) extends Splice[ExprType] {
    def spliceIn = preExpr.QuoteWhitebox(expr)
  }
}

/**
 * Extension class that provides string interpolation functions for various expression types.
 *
 * @param sc A StringContext
 */
class ExpressionParseHelper(sc: StringContext, file: sourcecode.File, line: sourcecode.Line, sig: BabelSignature) {
  private implicit def _sig: BabelSignature = sig

  private def interpolateHelper(expressions: Seq[Splice[Expr]]): (String, preExpr.Expr => preExpr.Expr) = {
    def repls(name: String): preExpr.Expr =
      expressions(name.drop(placeholder.length).toInt).spliceIn
    def repl(expr: preExpr.Expr): preExpr.Expr = expr match {
      case preExpr.LocAnnotation(e, loc)                            => preExpr.LocAnnotation(repl(e), loc)
      case preExpr.TypeAnnotation(e, ty)                            => preExpr.TypeAnnotation(repl(e), ty)
      case preExpr.Ident(name, _, _) if name startsWith placeholder => repls(name)
      case expr: preExpr.Ident                                      => expr
      case preExpr.Abs(v, sub) =>
        repl(v) match {
          case vNew @ preExpr.Ident(_, _, _) => // If repl(v) = v.
            preExpr.Abs(vNew, repl(sub))
          case preExpr.Quoted(Var(vNew, _), ty, _) => // If repl(v) = v'.
            preExpr.Abs(preExpr.Ident(vNew, ty, None), repl(sub))
          case _ => // Otherwise
            throw new IllegalArgumentException("Trying to substitute non-variable term in binding.")
        }
      case preExpr.App(a, b)    => preExpr.App(repl(a), repl(b))
      case expr: preExpr.Quoted => expr
      case preExpr.FlatOps(children) => preExpr.FlatOps(children.map {
          case Left((n, loc)) if n.startsWith(placeholder) => Right(preExpr.LocAnnotation(repls(n), loc))
          case tok @ Left(_)                               => tok
          case Right(e)                                    => Right(repl(e))
        })
    }

    (sc.parts.init.zipWithIndex.map { case (s, i) => s + " " + placeholder + i + " " }.mkString ++ sc.parts.last, repl)
  }

  private def interpolate(args: Seq[Splice[Expr]], baseAstTransformer: preExpr.Expr => preExpr.Expr): Expr = {
    val (combined, repl) = interpolateHelper(args)

    def astTransformer(expr: preExpr.Expr): preExpr.Expr = baseAstTransformer(repl(expr))

    BabelParser.tryParse(combined, astTransformer) match {
      case Left(error) => throw new IllegalArgumentException(
          s"Parse error at ${file.value}:${line.value}:\n${error.getMessage}"
        )
      case Right(expr) => expr
    }
  }

  def ty(args: Nothing*): Ty =
    BabelParser.tryParseType(sc.parts.mkString) match {
      case Left(error) => throw new IllegalArgumentException(
          s"Parse error at ${file.value}:${line.value}:\n${error.getMessage}"
        )
      case Right(ty) => ty
    }

  // Higher order parsers

  /**
   * Parses a string as a [[Expr]].
   *
   */
  def le(args: Splice[Expr]*): Expr = interpolate(args, identity)

  /**
   * Parses a string as a [[gapt.expr.formula.Formula]].
   *
   * @param args
   * @return
   */
  def hof(args: Splice[Expr]*): Formula = interpolate(args, preExpr.TypeAnnotation(_, preExpr.Bool)).asInstanceOf[Formula]

  /**
   * Parses a string as a [[gapt.expr.formula.Atom]].
   *
   * @param args
   * @return
   */
  def hoa(args: Splice[Expr]*): Atom = hof(args: _*) match {
    case atom: Atom => atom
    case expr =>
      throw new IllegalArgumentException(s"Expression $expr appears not to be a HOL atom. Parse it with hof.")
  }

  /**
   * Parses a string as a [[Var]].
   *
   * @param args
   * @return
   */
  def hov(args: Splice[Expr]*): Var = le(args: _*) match {
    case v: Var => v
    case expr =>
      throw new IllegalArgumentException(s"Expression $expr cannot be read as a variable. Parse it with le.")
  }

  /**
   * Parses a string as a [[Const]].
   *
   * @param args
   * @return
   */
  def hoc(args: Splice[Expr]*): Const = le(args: _*) match {
    case c: Const  => c
    case Var(n, t) => Const(n, t)
    case expr =>
      throw new IllegalArgumentException(s"Expression $expr cannot be read as a constant. Parse it with le.")
  }

  // First order parsers

  /**
   * Parses a string as a [[gapt.expr.formula.fol.FOLExpression]].
   *
   * @param args
   * @return
   */
  def foe(args: Splice[FOLExpression]*): FOLExpression = le(args: _*) match {
    case folExpression: FOLExpression => folExpression
    case expr =>
      throw new IllegalArgumentException(s"Expression $expr appears not to be a FOL expression. Parse it with le.")
  }

  /**
   * Parses a string as a [[gapt.expr.formula.fol.FOLFormula]].
   *
   * @param args
   * @return
   */
  def fof(args: Splice[FOLExpression]*): FOLFormula = hof(args: _*) match {
    case formula: FOLFormula => formula
    case expr =>
      throw new IllegalArgumentException(s"Formula $expr appears not to be a FOL formula. Parse it with hof.")
  }

  /**
   * Parses a string as a [[gapt.expr.formula.fol.FOLAtom]].
   *
   * @param args
   * @return
   */
  def foa(args: Splice[FOLExpression]*): FOLAtom = fof(args: _*) match {
    case atom: FOLAtom => atom
    case expr =>
      throw new IllegalArgumentException(s"Formula $expr appears not to be an atom. Parse it with fof.")
  }

  /**
   * Parses a string as a [[gapt.expr.formula.fol.FOLTerm]].
   *
   * @param args
   * @return
   */
  def fot(args: Splice[FOLTerm]*): FOLTerm = le(args: _*) match {
    case term: FOLTerm => term
    case expr =>
      throw new IllegalArgumentException(s"Expression $expr appears not to be FOL term. Parse it with le.")
  }

  /**
   * Parses a string as a [[gapt.expr.formula.fol.FOLVar]].
   *
   * @param args
   * @return
   */
  def fov(args: Splice[FOLTerm]*): FOLVar = le(args: _*) match {
    case Var(n, _) => FOLVar(n)
    case expr =>
      throw new IllegalArgumentException(s"Term $expr cannot be read as a FOL variable. Parse it with fot.")
  }

  /**
   * Parses a string as a [[gapt.expr.formula.fol.FOLConst]].
   *
   * @param args
   * @return
   */
  def foc(args: Splice[FOLTerm]*): FOLConst = fot(args: _*) match {
    case c: FOLConst => c
    case expr =>
      throw new IllegalArgumentException(s"Term $expr cannot be read as a FOL constant. Parse it with fot.")
  }

  /** Parses a string as a [[gapt.proofs.HOLSequent]]. */
  def hos(args: Splice[Expr]*): HOLSequent = {
    val (combined, repl) = interpolateHelper(args)

    BabelParser.tryParseSequent(combined, e => preExpr.TypeAnnotation(repl(e), preExpr.Bool)) match {
      case Left(error) => throw new IllegalArgumentException(
          s"Parse error at ${file.value}:${line.value}:\n${error.getMessage}"
        )
      case Right(sequent) => sequent.map(_.asInstanceOf[Formula])
    }
  }

  /** Parses a string as a labelled sequent. */
  def hols(args: Splice[Expr]*): Sequent[(String, Formula)] = {
    val (combined, repl) = interpolateHelper(args)

    BabelParser.tryParseLabelledSequent(combined, repl) match {
      case Left(error) => throw new IllegalArgumentException(
          s"Parse error at ${file.value}:${line.value}:\n${error.getMessage}"
        )
      case Right(sequent) => sequent
    }
  }

  /** Parses a string as a [[gapt.proofs.HOLClause]]. */
  def hcl(args: Splice[Expr]*): HOLClause = hos(args: _*).map(_.asInstanceOf[Atom])

  /** Parses a string as a [[gapt.proofs.FOLSequent]]. */
  def fos(args: Splice[Expr]*): FOLSequent = hos(args: _*).map(_.asInstanceOf[FOLFormula])

  /** Parses a string as a [[gapt.proofs.FOLClause]]. */
  def fcl(args: Splice[Expr]*): FOLClause = hos(args: _*).map(_.asInstanceOf[FOLAtom])

  /** Parses a string as a [[gapt.logic.hol.PredicateEliminationProblem]] */
  def pep(args: Splice[Expr]*): PredicateEliminationProblem = hof(args: _*) match
    case expr @ Ex.Block(vars, foPart) => {
      val (hoVarsPrefix, varSuffix) = vars.span(isHOVar)
      val remainder = Ex.Block(varSuffix, foPart)
      if (containsHOQuantifier(remainder)) {
        throw new IllegalArgumentException(s"Expression $expr is not of the form ∃X_1...∃X_n F where F is a first-order formula and X_1,...,X_n are second-order variables")
      }
      PredicateEliminationProblem(hoVarsPrefix, remainder)
    }

  private def placeholder = "__qq_"
}
