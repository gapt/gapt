package gapt.proofs.expansion

import gapt.expr.VarOrConst
import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.BinaryPropConnectiveHelper
import gapt.expr.formula.Bottom
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Quant
import gapt.expr.formula.Top
import gapt.expr.formula.hol.{HOLPosition, instantiate}
import gapt.expr.subst.Substitution
import gapt.formats.babel.BabelSignature
import gapt.logic.Polarity
import gapt.logic.hol.SkolemFunctions
import gapt.proofs.{Checkable, DagProof, HOLSequent, Sequent}
import gapt.proofs.context.Context
import gapt.utils.{Doc, Maybe}

import scala.collection.mutable

/**
 * Expansion tree.
 *
 * A tree collecting instances of a formula. See, e.g., M. Baaz, S. Hetzl,
 * D. Weller: On the complexity of proof deskolemization, Journal of Symbolic
 * Logic, 77(2), 2012 for a formulation close to the one implemented here.
 *
 * [[ExpansionTree]] wraps an expansion tree term together with the intended
 * shallow formula and polarity.  The term may not be necessarily correct
 * for this shallow formula (i.e., calling [[deep]] may produce an exception).
 * Calling [[ExpansionTree.check]] validates the correctness of the expansion tree (also
 * with respect to the given [[gapt.proofs.context.Context]]).
 *
 * The constructors [[ETAtom]], [[ETAnd]], etc. ensure that the produced
 * expansion trees are correct.
 */
case class ExpansionTree(term: ETt, polarity: Polarity, shallow: Formula) extends DagProof[ExpansionTree] {
  def deep: Formula = term.deep(shallow, polarity)

  override def equals(that: Any): Boolean = that match {
    case that: AnyRef if this eq that          => true
    case _ if this.hashCode != that.hashCode() => false
    case ExpansionTree(term2, polarity2, shallow2) =>
      polarity == polarity2 && term == term2 && shallow == shallow2
    case _ => false
  }

  def immediateSubProofs: Seq[ExpansionTree] = {
    def seq[T](as: T*): Seq[T] = as
    (this: @unchecked) match {
      case ETAtom(_, _) | ETWeakening(_, _) | ETTop(_) | ETBottom(_) => Seq.empty
      case ETMerge(a, b)                                             => seq(a, b)
      case ETNeg(a)                                                  => seq(a)
      case ETAnd(a, b)                                               => seq(a, b)
      case ETOr(a, b)                                                => seq(a, b)
      case ETImp(a, b)                                               => seq(a, b)
      case ETWeakQuantifier(_, insts)                                => insts.values.toSeq
      case ETStrongQuantifier(_, _, ch)                              => seq(ch)
      case ETSkolemQuantifier(_, _, ch)                              => seq(ch)
      case ETDefinition(_, ch)                                       => seq(ch)
    }
  }

  def isAtom: Boolean = this match {
    case ETAtom(_, _) => true
    case _            => false
  }

  def apply(pos: HOLPosition): Set[ExpansionTree] =
    if (pos.isEmpty) Set(this)
    else ((pos.head, this): @unchecked) match {
      case (_, ETMerge(a, b)) => a.apply(pos) union b.apply(pos)

      case (1, ETNeg(ch)) => ch.apply(pos.tail)

      case (1, ETAnd(l, _)) => l.apply(pos.tail)
      case (2, ETAnd(_, r)) => r.apply(pos.tail)

      case (1, ETOr(l, _)) => l.apply(pos.tail)
      case (2, ETOr(_, r)) => r.apply(pos.tail)

      case (1, ETImp(l, _)) => l.apply(pos.tail)
      case (2, ETImp(_, r)) => r.apply(pos.tail)

      case (1, ETStrongQuantifier(_, _, ch)) => ch.apply(pos.tail)
      case (1, ETSkolemQuantifier(_, _, ch)) => ch.apply(pos.tail)
      case (1, ETWeakQuantifier(_, insts))   => insts.values.flatMap(_.apply(pos.tail)).toSet

      case (_, ETWeakening(_, _)) => Set.empty
    }

  /** Checks whether this expansion tree is correct (in the given Context). */
  def check()(implicit ctx: Maybe[Context]): Unit = {
    def go: ExpansionTree => Unit = {
      t =>
        (t: @unchecked) match {
          // assumes that the shallow formula is already checked
          case ETAtom(_, _) | ETTop(_) | ETBottom(_) | ETWeakening(_, _) =>
          case ETMerge(a, b) =>
            go(a); go(b)
          case ETNeg(child) => go(child)
          case ETAnd(a, b) =>
            go(a); go(b)
          case ETOr(a, b) =>
            go(a); go(b)
          case ETImp(a, b) =>
            go(a); go(b)
          case ETWeakQuantifier(_, instances) =>
            for ((inst, child) <- instances) {
              ctx.foreach(_.check(inst))
              go(child)
            }
          case ETStrongQuantifier(_, eigenVar, child) =>
            ctx.foreach(_.check(eigenVar))
            go(child)
          case ETSkolemQuantifier(sh, skT, child) =>
            val Apps(skConst: Const, skArgs) = skT: @unchecked
            ctx.foreach { ctx =>
              val Some(skD) = ctx.skolemDef(skConst): @unchecked
              Checkable.requireDefEq(skD(skArgs), sh)(ctx)
            }
            go(child)
          case ETDefinition(sh, child) =>
            ctx.foreach(Checkable.requireDefEq(sh, child.shallow)(_))
            go(child)
        }
        ctx.foreach(_.check(shallow))
        go(this)
    }
  }

  def toDoc(implicit sig: BabelSignature): Doc = new ExpansionTreePrettyPrinter(sig).`export`(this)
  def toSigRelativeString(implicit sig: BabelSignature): String = toDoc.render(80)
  override def toString: String = toSigRelativeString
}

object ExpansionTree {
  def apply(formula: Formula, polarity: Polarity, term: ETt): ExpansionTree =
    ExpansionTree(term, polarity, formula)

  implicit val closedUnderSubst: ClosedUnderSub[ExpansionTree] =
    (sub, et) => ExpansionTree(sub(et.term), et.polarity, sub(et.shallow))

  implicit object closedUnderReplacement extends ClosedUnderReplacement[ExpansionTree] {
    def replace(et: ExpansionTree, p: PartialFunction[Expr, Expr]): ExpansionTree =
      ExpansionTree(TermReplacement(et.term, p), et.polarity, TermReplacement(et.shallow, p))

    def names(et: ExpansionTree): Set[VarOrConst] =
      containedNames(et.term) union containedNames(et.shallow)
  }

  implicit object checkable extends Checkable[ExpansionTree] {
    def check(et: ExpansionTree)(implicit ctx: Context): Unit = et.check()(ctx)
  }
}

/** Expansion tree for an atom. */
object ETAtom {
  def apply(shallow: Formula, polarity: Polarity): ExpansionTree =
    ExpansionTree(ETtAtom, polarity, shallow)
  def unapply(et: ExpansionTree): Option[(Formula, Polarity)] = et match {
    case ExpansionTree(ETtAtom, polarity, shallow) =>
      Some((shallow, polarity))
    case _ => None
  }
}

/** Expansion tree representing a weakening inference. */
object ETWeakening {
  def apply(shallow: Formula, polarity: Polarity): ExpansionTree =
    ExpansionTree(ETtWeakening, polarity, shallow)
  def unapply(et: ExpansionTree): Option[(Formula, Polarity)] = et match {
    case ExpansionTree(ETtWeakening, polarity, shallow) => Some((shallow, polarity))
    case _                                              => None
  }

  def apply(proof: ExpansionProof, newShallow: HOLSequent): ExpansionProof =
    ExpansionProof(apply(proof.expansionSequent, newShallow))
  def apply(sequent: ExpansionSequent, newShallow: HOLSequent): ExpansionSequent =
    sequent ++ (for ((t, i) <- newShallow.diff(sequent.shallow).zipWithIndex)
      yield ETWeakening(t, i.polarity))
}

/** Expansion tree merge node, representing a contraction inference. */
object ETMerge {
  def apply(nonEmptyChildren: Iterable[ExpansionTree]): ExpansionTree =
    nonEmptyChildren.reduce(ETMerge(_, _))

  def apply(shallow: Formula, polarity: Polarity, children: Iterable[ExpansionTree]): ExpansionTree = {
    for (ch <- children) {
      require(ch.polarity == polarity)
      require(ch.shallow == shallow)
    }
    if (children.nonEmpty) apply(children) else ETWeakening(shallow, polarity)
  }

  def byShallowFormula(trees: Iterable[ExpansionTree]): Vector[ExpansionTree] =
    trees.groupBy(t => t.shallow -> t.polarity).valuesIterator.map(ETMerge(_)).toVector

  def apply(expansionSequent: ExpansionSequent): ExpansionSequent =
    Sequent(byShallowFormula(expansionSequent.antecedent), byShallowFormula(expansionSequent.succedent))

  def apply(expansionProof: ExpansionProof): ExpansionProof =
    ExpansionProof(apply(expansionProof.expansionSequent))

  def apply(child1: ExpansionTree, child2: ExpansionTree): ExpansionTree = {
    require(child1.polarity == child2.polarity)
    require(child1.shallow == child2.shallow)
    ExpansionTree(ETtMerge(child1.term, child2.term), child1.polarity, child1.shallow)
  }
  def unapply(et: ExpansionTree): Option[(ExpansionTree, ExpansionTree)] = et match {
    case ExpansionTree(ETtMerge(term1, term2), polarity, shallow) =>
      Some((ExpansionTree(term1, polarity, shallow), ExpansionTree(term2, polarity, shallow)))
    case _ => None
  }
}

object ETMerges {
  def unapply(tree: ExpansionTree): Some[Vector[ExpansionTree]] =
    tree match {
      case ETMerge(ETMerges(t), ETMerges(s)) => Some(t ++ s)
      case _                                 => Some(Vector(tree))
    }
}

private[expansion] class ETNullaryCompanion(conn: Formula) {
  def apply(polarity: Polarity): ExpansionTree = ExpansionTree(ETtNullary, polarity, conn)
  def unapply(et: ExpansionTree): Option[Polarity] = et match {
    case ExpansionTree(ETtNullary, polarity, `conn`) => Some(polarity)
    case _                                           => None
  }
}

/** Expansion tree for ⊤. */
object ETTop extends ETNullaryCompanion(Top())

/** Expansion tree for ⊥. */
object ETBottom extends ETNullaryCompanion(Bottom())

/** Expansion tree for ¬. */
object ETNeg {
  def apply(child: ExpansionTree): ExpansionTree =
    ExpansionTree(ETtUnary(child.term), !child.polarity, -child.shallow)
  def unapply(et: ExpansionTree): Option[ExpansionTree] = et match {
    case ExpansionTree(ETtUnary(term), polarity, Neg(shallow)) =>
      Some(ExpansionTree(term, !polarity, shallow))
    case _ => None
  }
}

private[expansion] class ETBinaryCompanion(conn: BinaryPropConnectiveHelper, isImp: Boolean) {
  def apply(child1: ExpansionTree, child2: ExpansionTree): ExpansionTree = {
    if (isImp)
      require(!child1.polarity == child2.polarity)
    else
      require(child1.polarity == child2.polarity)
    ExpansionTree(ETtBinary(child1.term, child2.term), child2.polarity, conn(child1.shallow, child2.shallow))
  }
  def unapply(et: ExpansionTree): Option[(ExpansionTree, ExpansionTree)] =
    et match {
      case ExpansionTree(ETtBinary(ch1, ch2), pol, conn(sh1, sh2)) =>
        Some((
          ExpansionTree(ch1, if (isImp) !pol else pol, sh1),
          ExpansionTree(ch2, pol, sh2)
        ))
      case _ => None
    }
}

/** Expansion tree for ∧. */
object ETAnd extends ETBinaryCompanion(And, isImp = false) {
  object Flat {
    def apply(expansionTree: ExpansionTree): Seq[ExpansionTree] =
      expansionTree match {
        case ETAnd(Flat(ls), Flat(rs)) => ls ++ rs
        case _                         => Seq(expansionTree)
      }
    def unapply(expansionTree: ExpansionTree): Option[Seq[ExpansionTree]] =
      Some(Flat(expansionTree))
  }
}

/** Expansion tree for ∨. */
object ETOr extends ETBinaryCompanion(Or, isImp = false)

/** Expansion tree for →. */
object ETImp extends ETBinaryCompanion(Imp, isImp = true)

/**
 * Expansion tree collecting the instances for a weak quantifier.
 *
 * It has the form Qx.A +^t,,1,,^ E,,1,, + … +^t,,n,,^ E,,n,,, where t,,1,,,…,t,,n,, are lambda terms of the same type
 * as x and E,,i,, is an expansion tree of A[x\t,,i,,].
 *
 * Its deep formula is E,,1,,.deep ∨ … ∨ E,,n,,.deep (in the case of an existential) or E,,1,,.deep ∧ … ∧ E,,n,,.deep
 * (in the case of a universal).
 *
 */
object ETWeakQuantifier {
  import gapt.expr.subst.ExprSubstWithβ._
  def apply(shallow: Formula, instances: Map[Expr, ExpansionTree]): ExpansionTree = {
    val (polarity, boundVar, qfFormula) = shallow match {
      case Ex(x, t)  => (Polarity.InSuccedent, x, t)
      case All(x, t) => (Polarity.InAntecedent, x, t)
    }
    for ((inst, child) <- instances) {
      require(child.polarity == polarity)
      val correctShallow = Substitution(boundVar -> inst)(qfFormula)
      require(child.shallow == correctShallow, s"Incorrect shallow formula:\n${child.shallow} !=\n$correctShallow")
    }
    ExpansionTree(ETtWeak(Map() ++ instances.view.mapValues(_.term).toMap), polarity, shallow)
  }
  def withMerge(shallow: Formula, instances: Iterable[(Expr, ExpansionTree)]): ExpansionTree =
    ETWeakQuantifier(shallow, Map() ++ instances.groupBy(_._1).view.mapValues(children => ETMerge(children.map(_._2))).toMap)
  def unapply(et: ExpansionTree): Option[(Formula, Map[Expr, ExpansionTree])] =
    et match {
      case ExpansionTree(ETtWeak(instances), polarity, shallow @ Quant(bv, sh, isAll)) if isAll == polarity.inAnt =>
        Some((
          shallow,
          for ((inst, ch) <- instances)
            yield inst -> ExpansionTree(ch, polarity, Substitution(bv -> inst)(sh))
        ))
      case _ => None
    }
}

/** Represents nested weak quantifier nodes in an expansion tree, collecting the instances for a block of weak quantifiers. */
object ETWeakQuantifierBlock {
  def apply(shallow: Formula, blockSize: Int, instances: Iterable[(Seq[Expr], ExpansionTree)]): ExpansionTree =
    if (blockSize == 0) {
      ETMerge(instances map { _._2 })
    } else {
      ETWeakQuantifier(
        shallow,
        Map() ++ instances.groupBy(_._1.head).view.mapValues { children =>
          apply(instantiate(shallow, children.head._1.head), blockSize - 1, children map { case (ts, et) => ts.tail -> et })
        }.toMap
      )
    }

  def unapply(et: ExpansionTree): Some[(Formula, Int, Map[Seq[Expr], ExpansionTree])] = {
    val instances = mutable.Map[Seq[Expr], Set[ExpansionTree]]().withDefaultValue(Set())

    def maxQuants: ETt => Int = {
      case ETtWeakening => Int.MaxValue
      case ETtWeak(insts) =>
        if (insts.isEmpty) Int.MaxValue
        else insts.values.map(maxQuants).min match {
          case Int.MaxValue => Int.MaxValue
          case d            => d + 1
        }
      case ETtMerge(a, b) =>
        math.min(maxQuants(a), maxQuants(b))
      case _ => 0
    }
    val numberQuants0 = et.shallow match {
      case Ex.Block(vs, _) if et.polarity.inSuc  => vs.size
      case All.Block(vs, _) if et.polarity.inAnt => vs.size
    }
    val numberQuants = math.min(maxQuants(et.term), numberQuants0)

    def walk(et: ExpansionTree, terms: Seq[Expr], n: Int): Unit =
      if (n == 0) instances(terms) += et
      else et match {
        case ETWeakQuantifier(_, insts) =>
          for ((term, child) <- insts)
            walk(child, terms :+ term, n - 1)
        case ETMerge(a, b) =>
          walk(a, terms, n)
          walk(b, terms, n)
        case ETWeakening(_, _) =>
        case _ =>
          throw new IllegalStateException
      }
    walk(et, Seq(), numberQuants)

    Some((et.shallow, numberQuants, Map() ++ instances.view.mapValues(ETMerge(_)).toMap))
  }
}

/**
 * Expansion tree for a strong quantifier, containing the eigenvariable.
 *
 * It has the form Qx.A +^α^ E, where α is a variable (called the eigenvariable) and E is an expansion tree of A[x\α].
 */
object ETStrongQuantifier {
  def apply(shallow: Formula, eigenVariable: Var, child: ExpansionTree): ExpansionTree = {
    val (polarity, boundVar, qfFormula) = shallow match {
      case Ex(x, t)  => (Polarity.InAntecedent, x, t)
      case All(x, t) => (Polarity.InSuccedent, x, t)
    }
    require(child.polarity == polarity)
    require(child.shallow == Substitution(boundVar -> eigenVariable)(qfFormula))
    ExpansionTree(ETtStrong(eigenVariable, child.term), polarity, shallow)
  }

  def unapply(et: ExpansionTree): Option[(Formula, Var, ExpansionTree)] =
    et match {
      case ExpansionTree(ETtStrong(eigenVar, child), polarity, shallow @ Quant(bv, sh, isAll)) if isAll == polarity.inSuc =>
        Some((shallow, eigenVar, ExpansionTree(child, polarity, Substitution(bv -> eigenVar)(sh))))
      case _ => None
    }
}

/** Represents nested strong quantifier nodes in an expansion tree, collecting the eigenvariables for a block of strong quantifiers. */
object ETStrongQuantifierBlock {
  def apply(shallow: Formula, eigenVariables: Seq[Var], child: ExpansionTree): ExpansionTree = eigenVariables match {
    case ev +: evs =>
      ETStrongQuantifier(shallow, ev, ETStrongQuantifierBlock(instantiate(shallow, ev), evs, child))
    case Seq() => child
  }

  def unapply(et: ExpansionTree): Some[(Formula, Seq[Var], ExpansionTree)] = et match {
    case ETStrongQuantifier(sh, ev, ETStrongQuantifierBlock(_, evs, child)) => Some((sh, ev +: evs, child))
    case _                                                                  => Some((et.shallow, Seq(), et))
  }
}

/**
 * Expansion tree for a strong quantifier, containing a Skolem term.
 *
 * As an example let us consider an expansion proof of ∀z P(c,z) :- ∃x ∀y P(x,y).
 * For Skolemization we introduce the Skolem function `s_1` (for the single strong quantifier), this function
 * has the Skolem definition `λx ∀y P(x,y)` (see [[gapt.logic.hol.SkolemFunctions]] for details).
 * The natural expansion proof has the deep formula `P(c,s_1(c)) :- P(c,s_1(c))`, so we need a Skolem node with the
 * shallow formula `∀y P(c,y)`, and deep formula `P(c,s_1(c))`.  This Skolem node is constructed as
 * `ETSkolemQuantifier(∀y P(c,y), s_1(c), λx ∀y P(x,y), ETAtom(P(c,s_1(c)), InSuc))`.
 */
object ETSkolemQuantifier {
  def apply(shallow: Formula, skolemTerm: Expr, child: ExpansionTree): ExpansionTree = {
    val (polarity, boundVar, qfFormula) = shallow match {
      case Ex(x, t)  => (Polarity.InAntecedent, x, t)
      case All(x, t) => (Polarity.InSuccedent, x, t)
    }

    require(child.polarity == polarity)
    require(child.shallow == Substitution(boundVar -> skolemTerm)(qfFormula))

    ExpansionTree(ETtSkolem(skolemTerm, child.term), polarity, shallow)
  }

  def unapply(et: ExpansionTree): Option[(Formula, Expr, ExpansionTree)] = et match {
    case ExpansionTree(ETtSkolem(skTerm, child), polarity, shallow @ Quant(bv, sh, isAll)) if isAll == polarity.inSuc =>
      Some((shallow, skTerm, ExpansionTree(child, polarity, Substitution(bv -> skTerm)(sh))))
    case _ => None
  }
}

/**
 * Expansion tree for a definition node in an expansion tree.
 *
 * It has the form `φ +def E` where `φ` is the shallow formula of the definition node.
 * The formula `φ` should be definitionally equal to the shallow formula of `E`
 * (i.e., equal after unfolding all definitions).
 */
object ETDefinition {
  def apply(shallow: Formula, child: ExpansionTree): ExpansionTree =
    ExpansionTree(ETtDef(child.shallow, child.term), child.polarity, shallow)
  def unapply(et: ExpansionTree): Option[(Formula, ExpansionTree)] = et match {
    case ExpansionTree(ETtDef(sh1, ch), pol, sh2) =>
      Some((sh2, ExpansionTree(ch, pol, sh1)))
    case _ => None
  }

  def ifNecessary(shallow: Formula, child: ExpansionTree): ExpansionTree =
    if (child.shallow == shallow)
      child
    else
      ETDefinition(shallow, child)
}

/** Matches [[ETMerge]], [[ETAnd]], [[ETOr]], or [[ETImp]]. */
object BinaryExpansionTree {
  def unapply(et: ExpansionTree): Option[(ExpansionTree, ExpansionTree)] = et match {
    case ETMerge(a, b) => Some((a, b))
    case ETAnd(a, b)   => Some((a, b))
    case ETOr(a, b)    => Some((a, b))
    case ETImp(a, b)   => Some((a, b))
    case _             => None
  }
}
