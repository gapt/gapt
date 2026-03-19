package gapt.proofs.expansion
import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.Atom
import gapt.expr.formula.Formula
import gapt.expr.formula.Iff
import gapt.expr.formula.hol.HOLAtomConst
import gapt.expr.formula.hol.HOLPosition
import gapt.expr.subst.Substitution
import gapt.logic.Polarity
import gapt.proofs.context.Context

object eliminateDefsET {
  object DefinitionFormula {
    def unapply(f: Formula): Option[(List[Var], HOLAtomConst, Formula)] = f match {
      case All.Block(vs, Iff(Apps(d: HOLAtomConst, vs_), r)) if vs == vs_ =>
        Some((vs, d, r))
      case _ => None
    }
  }
  private val negReplPos = HOLPosition(1, 2)
  private val posReplPos = HOLPosition(2, 1)

  def apply(ep: ExpansionProof, pureFolWithoutEq: Boolean)(implicit ctx: Context): ExpansionProof =
    apply(ep, pureFolWithoutEq, atomicExpansionET.getDefinedAtoms(ep))

  def apply(ep: ExpansionProof, pureFolWithoutEq: Boolean, definitions: Set[Const])(implicit ctx: Context): ExpansionProof =
    atomicExpansionET(definitions.foldLeft(ep)(apply(_, _, pureFolWithoutEq)), definitions, pureFolWithoutEq)

  private def apply(ep: ExpansionProof, definitionConst: Const, pureFolWithoutEq: Boolean)(implicit ctx: Context): ExpansionProof = scala.util.boundary {
    val definitionFormula @ DefinitionFormula(vs, _, definedFormula) =
      ep.expansionSequent.antecedent.map(_.shallow).find {
        case DefinitionFormula(_, `definitionConst`, _) => true
        case _                                          => false
      }.getOrElse(scala.util.boundary.break(ep)): @unchecked

    def mkDefAtom(as: Seq[Expr], pol: Polarity) =
      ETDefinition(
        Substitution(vs zip as)(definedFormula),
        ETAtom(definitionConst(as).asInstanceOf[Atom], pol)
      )

    val insts0 = for {
      case ETWeakQuantifierBlock(`definitionFormula`, n, insts) <- ep.expansionSequent.antecedent
      (as, inst) <- insts
      // DO NOT INLINE THIS!  (otherwise the value of repls changes?!?!?)
      negRepls = inst(negReplPos)
      posRepls = inst(posReplPos)
      repls = negRepls ++ posRepls
      repl <- repls
    } yield as -> repl

    var insts = Map() ++ insts0.groupBy(_._1).view.mapValues(_.map(_._2)).toMap

    val rest = ep.expansionSequent.filterNot { et => et.polarity.inAnt && et.shallow == definitionFormula }
    val usesites: Set[(Seq[Expr], Polarity)] = rest.elements.flatMap { _.subProofs }.collect { case ETAtom(Apps(`definitionConst`, args), pol) => (args, pol) }.toSet
    insts = Map() ++ (for (as <- usesites.map(_._1) ++ insts.keys) yield as -> insts.getOrElse(as, Vector()))

    if (!pureFolWithoutEq) {
      val newRepl = Vector() ++ (for ((_, is) <- insts; i <- is) yield generalizeET(i, definedFormula))
      insts = for ((as, _) <- insts) yield as -> Substitution(vs zip as)(newRepl).toVector
    }

    insts =
      for ((as, is) <- insts)
        yield as -> (is ++ (for {
          pol <- Polarity.values
          if usesites(as -> pol)
          if !is.exists(_.polarity == pol)
        } yield mkDefAtom(as, pol)))

    def repl(et: ExpansionTree): ExpansionTree =
      atomicExpansionET.mapDefinedAtom(et) {
        case (sh, Apps(`definitionConst`, as), pol) =>
          ETMerge(sh, pol, insts(as).filter(_.polarity == pol))
      }

    val newCuts = ETCut {
      for {
        (_, is) <- insts
        pos = is.filter(_.polarity.positive)
        neg = is.filter(_.polarity.negative)
        if pos.nonEmpty && neg.nonEmpty
      } yield ETMerge(pos) -> ETMerge(neg)
    }

    val newES = ETMerge(newCuts +: rest.map(repl))

    eliminateMerges(ExpansionProof(newES))
  }
}
