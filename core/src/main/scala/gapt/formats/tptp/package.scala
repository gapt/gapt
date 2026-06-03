package gapt.formats

import gapt.expr._
import gapt.expr.formula.Atom
import gapt.expr.formula.Eq
import gapt.expr.formula.Formula
import gapt.expr.formula.hol.existentialClosure
import gapt.expr.ty.FunctionType
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.proofs._

package object tptp {

  type GeneralTerm = Expr
  // type GeneralList = Seq[GeneralTerm]
  type FormulaRole = String
  type InfoItem = GeneralTerm

  case class TptpFile(inputs: Seq[TptpInput]) {
    override def toString = inputs.mkString

    def toSequent = existentialClosure(inputs.flatMapS {
      case AnnotatedFormula(_, _, "conjecture", formula, _) =>
        Sequent() :+ formula
      case AnnotatedFormula(_, _, _, formula, _) =>
        formula +: Sequent()
      case in => throw new IllegalArgumentException(in.toString)
    })

    def toSequentWithIncludes = {
      val sequent = existentialClosure(inputs.flatMapS {
        case AnnotatedFormula(_, _, "conjecture", formula, _) =>
          Sequent() :+ formula
        case AnnotatedFormula(_, _, _, formula, _) =>
          formula +: Sequent()
        case IncludeDirective(_, _) =>
          Sequent()
      })
      val names = inputs.collect({
        case IncludeDirective(name, _) => name
      })

      (names, sequent)

    }
  }
  sealed trait TptpInput {
    override def toString = TptpToString.tptpInput(this)
  }
  type TptpName = String
  type ParentDetails = Option[GeneralTerm]
  type GeneralListNew = Seq[GeneralTerm]
  type UsefulInfo = GeneralListNew

  case class ParentInfo(source: Source, details: Option[GeneralTerm] = None)

  enum Source {
    case Name(name: TptpName)
    case Inference(rule: String, usefulInfo: Seq[GeneralTerm], parents: Seq[ParentInfo])
    case Internal(introType: String, usefulInfo: Seq[GeneralTerm], parents: Seq[ParentInfo])
    case File(fileName: String, fileInfo: Option[TptpName])
    case Theory(name: String, usefulInfo: Seq[GeneralTerm])
    case Creator(name: String, usefulInfo: Seq[GeneralTerm], parents: Seq[ParentInfo])
    // the General case is a catch-all used during the parser refactoring
    // afterwards this case should not exist anymore
    // every source should be accounted for by one of the other enum cases
    case General(term: GeneralTerm)
  }
  case class Annotations(source: Source, optionalInfo: Seq[GeneralTerm])
  case class AtomicWord(inner: String)

  case class AnnotatedFormula(language: String, name: String, role: FormulaRole, formula: Formula, annotations: Option[Annotations]) extends TptpInput

  case class IncludeDirective(fileName: String, formulaSelection: Option[Seq[String]]) extends TptpInput

  object TptpTerm {
    def apply(sym: String, args: Seq[Expr]): Expr =
      Apps(Const(sym, FunctionType(Ti, args.map(_.ty))), args)
    def apply(sym: String, args: Expr*)(implicit dummyImplicit: DummyImplicit): Expr =
      TptpTerm(sym, args)
    def unapplySeq(expr: Expr): Option[(String, Seq[Expr])] = expr match {
      case Apps(Const(sym, _, _), args) => Some((sym, args))
      case _                            => None
    }
  }
  def TptpAtom(sym: String, args: Seq[Expr]): Atom =
    (sym, args) match {
      case ("equal", Seq(a, b)) => Eq(a, b) // old tptp syntax
      case _                    => Apps(Const(sym, FunctionType(To, args.map(_.ty))), args).asInstanceOf[Atom]
    }

  object GeneralList {
    val name = "$general_list"
    def apply(elems: Seq[GeneralTerm]): Expr = TptpTerm(name, elems)
    def apply(elems: GeneralTerm*)(implicit dummyImplicit: DummyImplicit): Expr = TptpTerm(name, elems)
    def unapplySeq(expr: Expr): Option[Seq[Expr]] = expr match {
      case Apps(Const(`name`, _, _), elems) => Some(elems)
      case _                                => None
    }
  }
  object GeneralColon {
    val name = "$general_colon"
    def apply(a: GeneralTerm, b: GeneralTerm): Expr = TptpTerm(name, a, b)
    def unapplySeq(expr: Expr): Option[Seq[Expr]] = expr match {
      case Apps(Const(`name`, _, _), elems) => Some(elems)
      case _                                => None
    }
  }

  /**
   * The roles of valid formula assertions in a TPTP file.
   * @see http://tptp.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html#formula_role
   */
  object TptpFormulaRoles {
    val roles: Set[FormulaRole] = Set("axiom", "hypothesis", "definition", "assumption", "lemma", "theorem", "corollary", "conjecture", "negated_conjecture", "plain")

    def apply() = roles
  }

}
