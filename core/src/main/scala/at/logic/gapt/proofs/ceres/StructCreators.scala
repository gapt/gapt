package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.expr.{Apps, Const, _}
import at.logic.gapt.proofs.Context.{ProofDefinitions, ProofNames}
import at.logic.gapt.utils.logger._

/**
 * Algorithms extracting structs from LK proofs, preparing them for gui code etc.
 */

/**
 * Returns s.toString with color coding of struct operators. When a big struct is loaded in the cli, the string truncation
 * can mess up the terminal, therefore this is not the default behaviour.
 */
object coloredStructString {
  def apply[Data]( s: Struct[Data] ) = s match {
    case A( fo, _ ) =>
      fo.toString
    case Dual( sub ) =>
      Console.GREEN + "~(" + Console.RESET + sub + Console.GREEN + ")" + Console.RESET
    case Times( left, right, _ ) =>
      Console.RED + "(" + Console.RESET + left + Console.RED + " ⊗ " + Console.RESET + right + Console.RED + ")" + Console.RESET
    case Plus( left, right ) =>
      Console.BLUE + "(" + Console.RESET + left + Console.BLUE + " ⊕ " + Console.RESET + right + Console.BLUE + ")" + Console.RESET
    case EmptyPlusJunction()  => Console.RED + "ε" + Console.RESET
    case EmptyTimesJunction() => Console.BLUE + "ε" + Console.RESET
  }
}

object StructCreators {
  def size[Data]( s: Struct[Data] ): Int = size( s, 0 )
  //TODO:make tailrecursive
  def size[Data](s: Struct[Data], n: Int): Int = s match {
    case A(_, _) => n
    case CLS(_, _) => n
    case Dual(x) => size(x, n + 1)
    case Plus(l, r) => size(l, size(r, n + 1))
    case Times(l, r, _) => size(l, size(r, n + 1))
    case EmptyPlusJunction() => n
    case EmptyTimesJunction() => n
  }

  private val nLine = sys.props("line.separator")

  def toFormula[Data](s: Struct[Data]): Formula =
    And(CharacteristicClauseSet(s).toSeq map (_.toDisjunction))

  def extract[Data](p: LKProof)(implicit ctx: Context): Struct[Data] =
    extract[Data](p, p.endSequent.map(_ => false))(x => true, ctx)

  def extract[Data](p: LKProof, predicate: Formula => Boolean)(implicit ctx: Context): Struct[Data] =
    extract[Data](p, p.endSequent.map(_ => false))(predicate, ctx)

  private def mapToUpperProof[Formula](conn: SequentConnector, cut_occs: Sequent[Boolean], default: Boolean) =
    conn.parents(cut_occs).map(_.headOption getOrElse default)

  def extract[Data](p: LKProof, cut_occs: Sequent[Boolean])(implicit pred: Formula => Boolean, ctx: Context): Struct[Data] = {
    val cutanc_es = p.endSequent.zip(cut_occs).filter(_._2).map(_._1)
    val es = p.endSequent
    p match {
      case ReflexivityAxiom(e) =>
        if (cut_occs(Suc(0)))
          A(Eq(e, e))
        else
          EmptyTimesJunction()
      case ProofLink(rp, rs) =>
        val Apps(ps, _) = rp
        val Const(c, _) = ps
        if (ctx.get[ProofDefinitions].components.keySet.contains(c)) handleProofLink(rs, cut_occs, ps)
        else handleAxiom(rs, cut_occs)
      case InitialSequent(so) => handleAxiom(so, cut_occs)

      case EqualityLeftRule(upperProof, eq, aux, con) =>
        val new_occs = p.occConnectors(0).parents(cut_occs).flatMap { case Seq() => Seq(); case x => Seq(x.head) }
        val struct = extract[Data](upperProof, new_occs)
        val e_idx_conclusion = p.occConnectors(0).child(eq)
        val eqformula = upperProof.endSequent(eq)
        (cut_occs(p.mainIndices(0)), cut_occs(e_idx_conclusion)) match {
          case (true, true) =>
            struct
          case (true, false) =>
            Plus(A(eqformula, Nil), struct)
          case (false, true) =>
            Times(Dual(A(eqformula, Nil)), struct, Nil)
          case (false, false) =>
            struct
        }

      case EqualityRightRule(upperProof, eq, aux, con) =>
        val new_occs = p.occConnectors(0).parents(cut_occs).flatMap { case Seq() => Seq(); case x => Seq(x.head) }
        val struct = extract[Data](upperProof, new_occs)
        val e_idx_conclusion = p.occConnectors(0).child(eq)
        (cut_occs(p.mainIndices(0)), cut_occs(e_idx_conclusion)) match {
          case (true, true) =>
            struct
          case (true, false) =>
            Plus(A(p.endSequent(e_idx_conclusion), Nil), struct)
          case (false, true) =>
            Times(Dual(A(p.endSequent(e_idx_conclusion), Nil)), struct, Nil)
          case (false, false) =>
            struct
        }

      case UnaryLKProof(_, upperProof) =>
        require(
          p.mainIndices.size == 1,
          "Error: Struct extraction only works for rules which have exactly one primary formula!")
        val new_occs = p.occConnectors(0).parents(cut_occs).flatMap { case Seq() => Seq(); case x => Seq(x.head) }
        extract[Data](upperProof, new_occs)

      case rule@CutRule(p1, aux1, p2, aux2) =>
        if (pred(rule.cutFormula)) {
          val new_occs1 = mapToUpperProof(p.occConnectors(0), cut_occs, true)
          val new_occs2 = mapToUpperProof(p.occConnectors(1), cut_occs, true)
          Plus[Data](
            extract[Data](p1, new_occs1),
            extract[Data](p2, new_occs2))
        } else {
          val new_occs1 = mapToUpperProof(p.occConnectors(0), cut_occs, false)
          val new_occs2 = mapToUpperProof(p.occConnectors(1), cut_occs, false)
          Times[Data](
            extract[Data](p1, new_occs1),
            extract[Data](p2, new_occs2), List())
        }

      case BinaryLKProof(_, upperProofLeft, upperProofRight) =>
        require(
          p.mainIndices.size == 1,
          "Error: Struct extraction only works for rules which have exactly one primary formula! " + p)
        val new_occs1 = p.occConnectors(0).parents(cut_occs).map(_.head)
        val new_occs2 = p.occConnectors(1).parents(cut_occs).map(_.head)
        if (cut_occs(p.mainIndices(0)))
          Plus[Data](extract[Data](upperProofLeft, new_occs1), extract[Data](upperProofRight, new_occs2))
        else
          Times[Data](extract[Data](upperProofLeft, new_occs1), extract[Data](upperProofRight, new_occs2), List())
      case _ => throw new Exception("Missing rule in StructCreators.extract: " + p.name)
    }
  }

  def handleProofLink[Data](
                             so: HOLSequent,
                             cut_occs: Sequent[Boolean],
                             proofLink: Expr)(implicit ctx: Context): Struct[Data] = {
    val cutanc_seq: HOLSequent = so.zipWithIndex.filter(x => cut_occs(x._2)).map(_._1)
    val tautology_projection = cutanc_seq.antecedent.exists(x => cutanc_seq.succedent.contains(x))
    tautology_projection match {
      case true =>
        /* in the case of an axiom A :- A, if both occurrences of A are cut-ancestors, we need to return plus not times.
         * treat an axiom of the form \Gamma, A :- A, \Delta as if \Gamma and \Delta were added by weakening */
        EmptyPlusJunction()
      case false =>
        val cutAncInAntecedent = cutanc_seq.antecedent.map(x => Dual[Data](A(x, Nil)))
        val cutAncInSuccedent = cutanc_seq.succedent.map(x => A[Data](x))
        val structs: Vector[Struct[Data]] = cutAncInAntecedent ++ cutAncInSuccedent
        //This code matches positiions for terms passed through the proof links
        val Const(pn,_) = proofLink
        val (Apps(_, vs), hs: HOLSequent) = ctx.get[ProofNames].names.get(pn) match {
          case Some((ex, hs)) => (ex, hs)
          case None => (Const("", Ti), HOLSequent())
        }
        val termLocations = vs.map(arg => {
          hs.antecedent.map(formA => {
            val listplaces = formA.find(arg)
            if (listplaces.nonEmpty) Some((hs.find(ff => formA.equals(ff)) match {
              case Some(f) => f
              case None => -1
            }, listplaces.head))
            else None
          }).find(x => !x.isEmpty) match {
            case Some(Some(pos)) => pos
            case _ => hs.succedent.map(formA => {
              val listplaces = formA.find(arg)
              if (listplaces.nonEmpty) Some((hs.find(ff => formA.equals(ff)) match {
                case Some(f) => f
                case None => -1
              }, listplaces.head))
              else None
            }).find(x => !x.isEmpty) match {
              case Some(Some(pos)) => pos
              case _ => (-1, HOLPosition())
            }
          }
        })
        val subvals = termLocations.map(pairs => {
          so(pairs._1.asInstanceOf[SequentIndex]).get(pairs._2) match {
            case Some(termn) => termn
            case None => sys.error("Should not be here")
          }
        })
        CLS(Apps(proofLink,subvals), cut_occs)
    }
  }
  def handleAxiom[Data](
    so:        HOLSequent,
    cut_occs:  Sequent[Boolean],
    )(implicit ctx:Context): Struct[Data] = {

    val cutanc_seq: HOLSequent = so.zipWithIndex.filter( x => cut_occs( x._2 ) ).map( _._1 )
    val tautology_projection = cutanc_seq.antecedent.exists( x => cutanc_seq.succedent.contains( x ) )
    tautology_projection match {
      case true =>
        /* in the case of an axiom A :- A, if both occurrences of A are cut-ancestors, we need to return plus not times.
         * treat an axiom of the form \Gamma, A :- A, \Delta as if \Gamma and \Delta were added by weakening */
        EmptyPlusJunction()
      case false =>
        val cutAncInAntecedent = cutanc_seq.antecedent.map( x => Dual[Data]( A( x, Nil ) ) )
        val cutAncInSuccedent = cutanc_seq.succedent.map( x => A[Data]( x ) )
        val structs: Vector[Struct[Data]] = cutAncInAntecedent ++ cutAncInSuccedent
        Times[Data]( structs, List[Data]() )

    }
  }

}

