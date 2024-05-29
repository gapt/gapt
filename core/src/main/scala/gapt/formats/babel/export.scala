package gapt.formats.babel

import gapt.expr._
import gapt.proofs.HOLSequent
import gapt.utils.Doc
import Doc._
import gapt.expr.VarOrConst
import gapt.expr.formula.Eq
import gapt.expr.formula.Iff
import gapt.expr.formula.Neg
import gapt.expr.formula.fol.FOLConst
import gapt.expr.subst.Substitution
import gapt.expr.ty.->:
import gapt.expr.ty.FunctionType
import gapt.expr.ty.TBase
import gapt.expr.ty.TVar
import gapt.expr.ty.Ti
import gapt.expr.ty.Ty
import gapt.expr.util.syntacticMatching
import gapt.expr.util.typeVariables
import gapt.formats.babel.Notation.RealConst

/**
 * Exports lambda expressions in the Babel format.
 * You probably do not want to use this class, use one of [[gapt.expr.Expr#toString expression.toString]],
 * [[gapt.expr.Expr#toSigRelativeString .toSigRelativeString]], or
 * [[gapt.expr.Expr#toAsciiString .toAsciiString]] instead.
 * These are all implemented using this class.
 *
 * @param unicode  Whether to output logical connectives using Unicode symbols.
 * @param sig  The Babel signature, to decide whether we need to escape constants because they
 *             do not fit the naming convention.
 */
class BabelExporter(unicode: Boolean, sig: BabelSignature, omitTypes: Boolean = false) {

  val defaultIndent = 2
  val lineWidth = 80

  def nest(doc: Doc, j: Int = defaultIndent): Doc =
    doc.group.nest(j)

  protected def group(doc: Doc): Doc = doc.group

  protected def parens(doc: Doc): Doc = "(" <> doc <> ")"

  def `export`(expr: Expr): String =
    group(show(expr, false, Map(), Map())._1.inPrec(0)).render(lineWidth)
  def exportRaw(expr: Expr): String =
    group(showRaw(expr).inPrec(0)).render(lineWidth)
  def `export`(sequent: HOLSequent): String =
    group(show(sequent, Map(), Map())._1).render(lineWidth)
  def `export`(ty: Ty): String = show(ty, needParens = false).group.render(lineWidth)

  def show(sequent: HOLSequent, bound: Map[String, Var], t0: Map[String, VarOrConst]): (Doc, Map[String, VarOrConst]) = {
    var t1 = t0
    val docSequent = sequent map { formula =>
      val (formulaDoc, t1_) = show(formula, true, bound, t1)
      t1 = t1_
      formulaDoc.inPrec(0)
    }
    (
      sep(docSequent.antecedent.toList, "," <> line) </>
        (if (unicode) "⊢" else ":-") </>
        sep(docSequent.succedent.toList, "," <> line),
      t1
    )
  }

  case class Parenable(prec: Int, doc: Doc) {
    def inPrec(outerPrec: Int) =
      if (outerPrec > prec) {
        parens(group(nest(doc)))
      } else if (outerPrec + 1 < prec) {
        group(nest(doc))
      } else {
        doc
      }
  }

  def showRaw(expr: Expr): Parenable = expr match {
    case Abs(Var(vn, vt), e) =>
      val v_ = parens(showName(vn) <> ":" <> show(vt, false))
      val e_ = showRaw(e)
      Parenable(Precedence.lam, (if (unicode) "λ" else "^") <> v_ </> e_.inPrec(Precedence.lam + 1))
    case ident @ VarOrConst(_, _, _) =>
      show(ident, Safe)
    case Apps(f, as) =>
      Parenable(Precedence.app, wordwrap2((f :: as).map(showRaw).map(_.inPrec(Precedence.app + 1))))
  }

  /**
   * Converts a lambda expression into a document.
   *
   * At every point in the conversion, we keep track of:
   *
   *  1. Whether the parser will already know the type of this expression (by inference)
   *  1. What type the free identifiers have.
   *  1. What priority the enclosing operator has.
   *
   * @param expr  The lambda expression to convert.
   * @param knownType  Whether we already know the type of this expression.
   * @param bound  Names bound by enclosing binders.
   * @param t0  Already known free identifiers, together with the variable or constant they represent.
   * @return  Pretty-printed document and the free identifiers.
   */
  def show(
      expr: Expr,
      knownType: Boolean,
      bound: Map[String, Var],
      t0: Map[String, VarOrConst]
  ): (Parenable, Map[String, VarOrConst]) =
    expr match {
      case Iff(a, b) =>
        showFakeBin(expr, Notation.fakeIffConst, a, b, knownType, bound, t0)
      case Neg(Eq(a, b)) =>
        showFakeBin(expr, Notation.fakeNeqConst, a, b, false, bound, t0)

      case Abs(v @ Var(vn, vt), e) =>
        val (e_, t1) = show(e, knownType, bound + (vn -> v), t0 - vn)
        val v_ =
          if (vt == Ti || t1.get(vn).contains(v) || omitTypes)
            showName(vn)
          else
            parens(showName(vn) <> ":" <> show(vt, false))
        (Parenable(Precedence.lam, (if (unicode) "λ" else "^") <> v_ </> e_.inPrec(Precedence.lam)), t1 - vn ++ t0.get(vn).map { vn -> _ })

      case Apps(_, args) if args.nonEmpty => showApps(expr, knownType, bound, t0)

      case expr @ VarOrConst(name, _, _) =>
        val isNotation = sig.notationsForToken(name).exists {
          case Notation.Alias(_, _) => false
          case _                    => true
        }
        val (mode, t1) = getIdentShowMode(expr, knownType, bound, t0)
        val doc = show(expr, mode)
        (if (isNotation) Parenable(0, doc.inPrec(0)) else doc, t1)
    }

  sealed trait IdentShowMode
  case object Bare extends IdentShowMode
  case object Safe extends IdentShowMode
  case object WithParams extends IdentShowMode
  case object WithType extends IdentShowMode

  def show(ident: VarOrConst, mode: IdentShowMode): Parenable =
    mode match {
      case Bare =>
        Parenable(Precedence.max, showName(ident.name))
      case Safe =>
        ident match {
          case Var(name, ty) =>
            Parenable(Precedence.max, "#v(" <> showNameFollowableByOp(name) <> ":" </> show(ty, false) <> ")")
          case Const(name, ty, params) =>
            Parenable(Precedence.max, "#c(" <> showNameWithParams(name, params) <> ":" </> show(ty, false) <> ")")
        }
      case WithParams =>
        Parenable(Precedence.max, showNameWithParams(ident.name, ident.asInstanceOf[Const].params))
      case WithType =>
        val withParams = ident match {
          case Const(n, _, ps) => showNameFollowableByOp(n) <> showTyParams(ps)
          case Var(n, _)       => showNameFollowableByOp(n)
        }
        Parenable(Precedence.typeAnnot, withParams <> ":" <> show(ident.ty, false))
    }

  def showNameWithParams(name: String, params: List[Ty]): Doc =
    (if (params.isEmpty) showName(name) else showNameFollowableByOp(name)) <> showTyParams(params)

  def getIdentShowMode(
      expr: VarOrConst,
      knownType: Boolean,
      bound: Map[String, Var],
      t0: Map[String, VarOrConst]
  ): (IdentShowMode, Map[String, VarOrConst]) = {
    val name = expr.name
    val ty = expr.ty
    val isAliased = sig.notationsForToken(expr.name).exists(not => not.const != RealConst(expr.name))
    sig.signatureLookup(name) match {
      case _ if omitTypes                         => Bare -> t0
      case _ if isAliased                         => Safe -> t0
      case _ if t0.get(name).exists(_ != expr)    => Safe -> t0
      case _ if bound.get(name).exists(_ != expr) => Safe -> t0
      // Now: t0.get(name).forall(_ == expr)
      case BabelSignature.IsConst(c) if !bound.contains(name) =>
        safeMatching(c, expr) match {
          case Some(_) if knownType && !paramsNecessary(c) =>
            Bare -> t0
          case Some(_) => WithParams -> t0
          case None    => Safe -> t0
        }
      case res if bound.contains(name) || res.isVar =>
        if (expr.isInstanceOf[Const]) Safe -> t0
        else if (knownType || t0.get(name).contains(expr) || ty == Ti) Bare -> (t0 + (name -> expr))
        else WithType -> (t0 + (name -> expr))
      // Now: !bound(name) && !.isVar
      case _ if !expr.isInstanceOf[Const] => Safe -> t0
      // Now: expr.isInstanceOf[Const]
      case BabelSignature.IsUnknownConst if knownType || t0.get(name).contains(expr) || expr == FOLConst(name) =>
        val hasParams = expr.asInstanceOf[Const].params.nonEmpty
        if (hasParams)
          WithParams -> t0
        else
          Bare -> (t0 + (name -> expr))
      case BabelSignature.IsUnknownConst =>
        expr match {
          case Const(_, _, ps) if ps.nonEmpty =>
            WithType -> t0
          case _ =>
            WithType -> (t0 + (name -> expr))
        }
      case _ => Safe -> t0
    }
  }

  def paramsNecessary(sigC: Const): Boolean =
    !typeVariables(sigC.params).subsetOf(typeVariables(sigC.ty))

  def safeMatching(c1: Const, c2: Expr): Option[Substitution] =
    c2 match {
      case c2: Const => safeMatching(c1, c2)
      case _         => None
    }

  def safeMatching(c1: Const, c2: Const): Option[Substitution] =
    if (c1.name != c2.name) None
    else if (c1.params.size != c2.params.size) None
    else syntacticMatching((c1.ty -> c2.ty) :: (c1.params zip c2.params))

  def unicodeSafe(n: Notation.Token): Boolean =
    unicode || n.token.forall(_ < 127)

  def notationForConst(const: Notation.ConstName): Option[Notation] =
    sig.notationsForConst(const).find(not => unicodeSafe(not.token))

  def showTyParams(params: List[Ty], always: Boolean = false): Doc =
    params match {
      case List()      => ""
      case List(param) => "{" <> show(param, needParens = false) <> "}"
      case _ =>
        "{" <> wordwrap(params.map {
          case param @ TVar(_) => show(param, needParens = false)
          case param           => parens(show(param, needParens = false))
        }) <> "}"
    }

  def showFakeBin(
      expr: Expr,
      fakeConst: Notation.ConstName,
      a: Expr,
      b: Expr,
      knownType: Boolean,
      bound: Map[String, Var],
      t0: Map[String, VarOrConst]
  ): (Parenable, Map[String, VarOrConst]) = {
    notationForConst(fakeConst) match {
      case Some(Notation.Infix(Notation.Token(tok), _, prec, _)) =>
        val (a_, t1) = show(a, knownType, bound, t0)
        val (b_, t2) = show(b, knownType, bound, t1)
        (Parenable(prec, a_.inPrec(prec + 1) <+> tok </> b_.inPrec(prec + 1)), t2)
      case _ =>
        showApps(expr, knownType, bound, t0)
    }
  }

  def sepByComma(args: List[Doc]): Doc =
    args match {
      case Nil     => ""
      case List(a) => a
      case _       => wordwrap(args, ",")
    }

  def shows(
      exprs: List[Expr],
      knownType: Boolean,
      bound: Map[String, Var],
      t0: Map[String, VarOrConst]
  ): (List[Parenable], Map[String, VarOrConst]) = {
    var t1 = t0
    val exprs_ = for (expr <- exprs) yield {
      val (expr_, t1_) = show(expr, knownType, bound, t1)
      t1 = t1_
      expr_
    }
    (exprs_, t1)
  }

  def showApps(
      expr: Expr,
      knownType: Boolean,
      bound: Map[String, Var],
      t0: Map[String, VarOrConst]
  ): (Parenable, Map[String, VarOrConst]) = {
    val Apps(hd, args) = expr
    val hdSym = hd match {
      case Const(n, _, _) => Some(n)
      case Var(n, _)      => Some(n)
      case _              => None
    }
    val notation = hdSym.flatMap(h => notationForConst(RealConst(h)))
    (notation, args) match {
      case (Some(Notation.Quantifier(tok, _, prec)), Seq(Abs(v, e))) =>
        // FIXME
        val Var(vn, vt) = v
        val (e_, t1) = show(e, true, bound + (vn -> v), t0 - vn)
        val v_ =
          if (vt == Ti || t1.get(vn).contains(v) || omitTypes)
            showName(vn)
          else
            parens(showName(vn) <> ":" <> show(vt, false))
        return (
          Parenable(
            prec,
            tok.token <>
              (if (vn.startsWith("_")) " " else "") <> v_ </>
              e_.inPrec(prec)
          ),
          t1 - vn ++ t0.get(vn).map { vn -> _ }
        )
      case _ =>
    }

    val argTysKnown = hdSym.exists { n =>
      t0.get(n).contains(hd) || (sig.signatureLookup(n) match {
        case _ if t0.get(n).exists(_ != hd) => false
        case BabelSignature.IsConst(c)      => typeVariables(c).isEmpty
        case _                              => false
      })
    }
    val (args_, t1) = shows(args, argTysKnown, bound, t0)

    def showFunCall(hd: Parenable, args: List[Parenable]) =
      Parenable(Precedence.app, hd.inPrec(Precedence.app) <> nest(group(parens(sepByComma(args.map(_.inPrec(0)))))))

    val retTyKnown = knownType || hdSym.exists { n =>
      t1.get(n).contains(hd) || (sig.signatureLookup(n) match {
        case _ if t0.get(n).exists(_ != hd) => false
        case BabelSignature.IsConst(c) =>
          val FunctionType(retTy, argTys) = c.ty: @unchecked
          typeVariables(retTy :: argTys.drop(args.size)).subsetOf(typeVariables(argTys.take(args.size)))
        case BabelSignature.IsUnknownConst =>
          expr.ty == Ti
        case _ => false
      })
    }

    val (call, t3) = hd match {
      case hd: VarOrConst =>
        val (hdMode, t2) = getIdentShowMode(hd, knownType = true, bound, t1)
        (notation, args_) match {
          case (Some(Notation.Prefix(Notation.Token(tok), _, prec)), Seq(arg)) if hdMode == Bare =>
            val argDoc = arg.inPrec(prec)
            val needSpace = argDoc.firstChar.forall { c =>
              tok match {
                case _ if c == '_' => true
                case _ if fastparse.parse(tok, BabelLexical.OperatorAndNothingElse(_)).isSuccess =>
                  def argIsRestOp = fastparse.parse(c.toString, BabelLexical.RestOpChar(_)).isSuccess
                  def argIsOp = fastparse.parse(c.toString, BabelLexical.OpChar(_)).isSuccess
                  argIsOp || argIsRestOp && tok.contains("_")
                case _ if tok.forall(BabelLexical.isUnquotNameChar) =>
                  BabelLexical.isUnquotNameChar(c)
                case _ => false
              }
            }
            (Parenable(prec, showName(tok) <> (if (needSpace) " " <> argDoc else argDoc)), t2)
          case (Some(Notation.Infix(tok, _, prec, leftAssociative)), Seq(lhs, rhs)) if hdMode == Bare =>
            val (biasLeft, biasRight) = if (leftAssociative) (0, +1) else (+1, 0)
            (Parenable(prec, lhs.inPrec(prec + biasLeft) <+> showName(tok) </> rhs.inPrec(prec + biasRight)), t2)
          case (Some(Notation.Postfix(tok, _, prec)), Seq(arg)) if hdMode == Bare =>
            (Parenable(prec, arg.inPrec(prec) <+> showName(tok)), t2)
          case _ =>
            val hd_ = show(hd, hdMode)
            val isNotation = sig.notationsForToken(hd.name).exists {
              case Notation.Alias(_, _) => false
              case _                    => true
            }
            (showFunCall(if (isNotation) Parenable(0, hd_.inPrec(0)) else hd_, args_), t2)
        }
      case _ =>
        val (hd_, t2) = show(hd, knownType = true, bound, t1)
        (showFunCall(hd_, args_), t2)
    }

    if (retTyKnown || omitTypes) (call, t3)
    else
      (
        Parenable(
          Precedence.typeAnnot,
          call.inPrec(Precedence.typeAnnot) <> ":" </>
            show(expr.ty, false)
        ),
        t3
      )
  }

  val safeChars = """[A-Za-z0-9 ~!@#$%^&*()_=+{}|;:,./<>?-]|\[|\]""".r
  val asciiUnquotName = """[A-Za-z0-9_]+""".r
  def showName(token: Notation.Token)(implicit dummyImplicit: DummyImplicit): Doc = showName(token.token)
  def showName(name: String): Doc =
    if (fastparse.parse(name, BabelLexical.OperatorAndNothingElse(_)).isSuccess && unicodeSafe(name))
      name
    else
      showNonOpName(name)
  def showNameFollowableByOp(name: String): Doc =
    if (fastparse.parse(name, BabelLexical.OperatorAndNothingElse(_)).isSuccess && unicodeSafe(name))
      name <> " "
    else
      showNonOpName(name)
  def showNonOpName(name: String): Doc = name match {
    case _ if unicode && name.nonEmpty && name.forall { BabelLexical.isUnquotNameChar } => name
    case asciiUnquotName()                                                              => name
    case _ => "'" + name.map {
        case c @ safeChars() =>
          c
        case '\''         => "\\'"
        case '\\'         => "\\\\"
        case c if unicode => c
        case c            => "\\u%04x".format(c.toChar.toInt)
      }.mkString + "'"
  }

  def show(ty: Ty, needParens: Boolean): Doc = ty match {
    case TBase(name, params) => wordwrap(showName(name) :: params.map(show(_, needParens = true)))
    case TVar(name)          => "?" <> showName(name)
    case a ->: b if !needParens =>
      group(show(a, true) <> ">" <> zeroWidthLine <> show(b, false))
    case _ => parens(nest(show(ty, false)))
  }
}
