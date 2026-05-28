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
  type GeneralList = Seq[GeneralTerm]
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
  case object Unknown
  type Source = DagSource | Unknown.type
  type DagSource = TptpName | InferenceRecord
  type TptpName = AtomicWord | Int
  type ParentDetails = Option[GeneralTerm]
  case class ParentInfo(source: Source, details: ParentDetails)
  case class InferenceRecord(inference_rule: AtomicWord, usefulInfo: GeneralList, parents: Seq[ParentInfo])
  sealed trait Annotations {
    def source: Source
    def optionalInfo: GeneralList
  }

  case class AtomicWord(inner: String)
  given Conversion[String, AtomicWord] = (s: String) => AtomicWord(s)

  object AtomicWord {
    def unapply(term: GeneralTerm): Option[String] = term match {
      case TptpTerm(name, _, _) => Some(name)
      case _                    => None
    }
  }

  def termToParentInfo(term: GeneralTerm): ParentInfo = term match {
    case GeneralColon(source, parentDetails) => ParentInfo(termToSource(source), Some(parentDetails))
    case t                                   => ParentInfo(termToSource(t), None)
  }

  def termToSource(term: GeneralTerm): Source = term match {
    case TptpTerm("inference", TptpTerm(rule), GeneralList(usefulInfo*), GeneralList(parents*)) =>
      InferenceRecord(rule, usefulInfo, parents.map(termToParentInfo))
    case TptpTerm(t) => AtomicWord(t)
    case _           => Unknown
  }
  given Conversion[GeneralTerm, Source] = termToSource

  // these conversion will be removed once the parser refactor has finished
  given Conversion[GeneralList, Annotations] = (generalList: GeneralList) => {
    generalList match {
      case Seq() => new Annotations {
          def source: Source = Unknown
          def optionalInfo: GeneralList = generalList
        }
      case Seq(s, optInfo*) => new Annotations {
          def source: Source = termToSource(s)
          def optionalInfo: GeneralList = optInfo
        }
    }

  }
  given Conversion[Annotations, GeneralList] = (annotations: Annotations) => annotations.optionalInfo
  case class AnnotatedFormula(language: String, name: String, role: FormulaRole, formula: Formula, annotations: Annotations) extends TptpInput

  object AnnotatedFormula {
    def unapply(annotatedFormula: AnnotatedFormula): Option[(String, String, FormulaRole, Formula, GeneralList)] =
      Some((annotatedFormula.language, annotatedFormula.name, annotatedFormula.role, annotatedFormula.formula, annotatedFormula.annotations.optionalInfo))
  }

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
