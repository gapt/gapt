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
  type DagSource = TptpName | InferenceRecord
  type TptpName = String
  type ParentDetails = Option[GeneralTerm]
  type GeneralListNew = Seq[GeneralTerm]
  type UsefulInfo = GeneralListNew
  case class Introduced(introType: AtomicWord, usefulInfo: GeneralListNew, parents: Seq[ParentInfo])
  case class ParentInfo(source: TptpName, details: ParentDetails)
  case class InferenceRecord(inference_rule: AtomicWord, usefulInfo: GeneralListNew, parents: Seq[ParentInfo])
  case class File(fileName: AtomicWord, fileInfo: Option[TptpName])

  enum Source {
    case Name(name: TptpName)
    case Inference(rule: String)
    case General(term: GeneralTerm)
  }
  case class Annotations(source: Source, optionalInfo: Seq[GeneralTerm])
  case class AtomicWord(inner: String)

  case class AnnotatedFormula(language: String, name: String, role: FormulaRole, formula: Formula, annotations: Option[Annotations]) extends TptpInput
  // case class AnnotatedFormula2(language: String, name: String, role: FormulaRole, formula: Formula, annotations: Option[Annotations])

  // given Conversion[Seq[GeneralTerm], Option[Annotations]] = s =>
  //   s match {
  //     case Seq()            => None
  //     case Seq(s, optInfo*) => Some(Annotations(s, optInfo))
  //   }

  // given Conversion[Option[Annotations], Seq[GeneralTerm]] = s =>
  //   s match {
  //     case None      => Seq()
  //     case Some(ann) => ann.source +: ann.optionalInfo
  //   }

  // for backwards compatibility
  // these will be removed once the parser refactor is finished
  // object AnnotatedFormula {
  //   def unapply(annotatedFormula: AnnotatedFormula): Option[(String, String, FormulaRole, Formula, GeneralListNew)] =
  //     Some((annotatedFormula.language, annotatedFormula.name, annotatedFormula.role, annotatedFormula.formula, optionalAnnotationsToGeneralList(annotatedFormula.annotations)))
  // }
  // def tptpNameToTerm(name: TptpName): GeneralTerm = {
  //   name match {
  //     case AtomicWord(inner) => TptpTerm(inner)
  //     case _                 => throw new NotImplementedError("cannot handle integer names yet")
  //   }
  // }
  // def annotationsToGeneralList(a: Annotations): GeneralListNew = {
  //   val sourceExpr = a.source match {
  //     case Unknown => TptpTerm("unknown")
  //     case InferenceRecord(name, usefulInfo, parents) => TptpTerm(
  //         "inference",
  //         tptpNameToTerm(name),
  //         GeneralList(usefulInfo*),
  //         GeneralList(parents.map(p => tptpNameToTerm(p.source))*)
  //       )
  //     case File(fileName, fileInfo) => fileInfo match {
  //         case None    => TptpTerm("file", tptpNameToTerm(fileName))
  //         case Some(f) => TptpTerm("file", tptpNameToTerm(fileName), tptpNameToTerm(f))
  //       }
  //     case Introduced(introType, usefulInfo, parents) => TptpTerm(
  //         "introduced",
  //         tptpNameToTerm(introType),
  //         GeneralList(usefulInfo*),
  //         GeneralList(parents.map(p => tptpNameToTerm(p.source))*)
  //       )
  //     case s => throw new NotImplementedError(s"cannot handle this yet. got $s")
  //   }
  //   sourceExpr +: a.optionalInfo
  // }

  // def optionalAnnotationsToGeneralList = (annotations: Option[Annotations]) => annotations.map(annotationsToGeneralList).getOrElse(Seq.empty)
  // def generalListToOptionalAnnotations(list: GeneralListNew) = list match {
  //   case Seq()            => None
  //   case Seq(s, optInfo*) => Some(Annotations(termToSource(s), optInfo))
  // }

  // def termToParentInfo(term: GeneralTerm): ParentInfo = term match {
  //   case GeneralColon(TptpTerm(source), parentDetails) => ParentInfo(source, Some(parentDetails))
  //   case TptpTerm(source)                              => ParentInfo(source, None)
  //   case GeneralColon(_, _)                            => throw new IllegalArgumentException(s"cannot handle parents that are not names. got: $term")
  // }
  // def termToSource(term: GeneralTerm): Source = term match {
  //   case TptpTerm("inference", TptpTerm(rule), GeneralList(usefulInfo*), GeneralList(parents*)) =>
  //     InferenceRecord(rule, usefulInfo, parents.map(termToParentInfo))

  //   case TptpTerm("file", TptpTerm(fileName)) =>
  //     File(fileName, None)

  //   case TptpTerm("file", TptpTerm(fileName), TptpTerm(label)) =>
  //     File(fileName, Some(label))

  //   case TptpTerm("introduced", TptpTerm(introType), GeneralList(usefulInfo*)) =>
  //     Introduced(introType, usefulInfo, Seq.empty)

  //   case TptpTerm("introduced", TptpTerm(introType), GeneralList(usefulInfo*), GeneralList(parents*)) =>
  //     Introduced(introType, usefulInfo, parents.map(termToParentInfo))

  //   case TptpTerm("unknown") =>
  //     Unknown

  //   case TptpTerm(t) =>
  //     AtomicWord(t)

  //   case _ =>
  //     throw new UnsupportedOperationException(s"cannot handle term: $term")
  // }
  // object AtomicWord {
  //   def unapply(term: GeneralTerm): Option[String] = term match {
  //     case TptpTerm(name, _, _) => Some(name)
  //     case _                    => None
  //   }
  // }
  given Conversion[String, AtomicWord] = (s: String) => AtomicWord(s)
  // end of backwards compatibility

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
