package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lk.{LKProof, SolveUtils, TopAxiom}

import scala.collection.immutable.Iterable

/**
  * Created by matthias on 5/12/16.
  */
object Deskolemize extends Deskolemize {
}

class Deskolemize extends SolveUtils {
  type Error = (Seq[ETImp], ExpansionSequent)

  def apply(sequent: Sequent[HOLFormula], expSequent: Sequent[ExpansionTree]): Sequent[ExpansionTree] = {
    require(sequent.length == expSequent.length)
    val antecedent = sequent.antecedent.zip(expSequent.antecedent)
    val deskAnt = for { (a, e) <- antecedent } yield desk(false, 0, Nil, a, e)
    val succedent = sequent.succedent.zip(expSequent.succedent)
    val deskSucc = for { (b, f) <- succedent } yield desk(true, 0, Nil, b, f)
    Sequent(deskAnt, deskSucc)
  }

  def desk(polarity: Boolean, m: Int, selected: List[LambdaExpression], a: LambdaExpression, e: ExpansionTree) : ExpansionTree = {
    println ("------------------------------------------------------------------")
    println ("polarity: " + polarity)
    println ("m       : " + m)
    println ("selected: " + selected)
    println ("a       : " + a)
    println ("e       : " + e)
    println ("class   : " + e.getClass())
    // TODO a needed? information seems to be available inside of ExpansionTree objects
    (a, e) match {
      case (_, ETBottom(_)) => e
      case (_, ETTop(_))    => e
      case (_, ETWeakening(f, p)) => {
        // TODO
        println( "Weakening f: " + f)
        println( "Weakening p: " + p)
        e
      }
      case (Neg(a1), ETNeg(e1)) => {
        ETNeg(desk(!polarity, m, selected, a1, e1))
      }
      case (Or(a1, a2), ETOr(e1, e2)) => {
        println( "Or a1: " + a1)
        println( "Or a2: " + a2)
        println( "Or e1: " + e1)
        println( "Or e2: " + e2)
        val q = qocc(a1, polarity)
        println("qocc: " + q)
        ETOr(
          desk( polarity, m, selected, a1, e1 ),
          desk( polarity, m + q, selected, a2, e2 )
        )
      }
      case (And(a1, a2), ETAnd(e1, e2)) => {
        println( "And a1: " + a1)
        println( "And a2: " + a2)
        println( "And e1: " + e1)
        println( "And e2: " + e2)
        val q = qocc(a1, polarity)
        println("qocc: " + q)
        ETAnd(
          desk( polarity, m, selected, a1, e1 ),
          desk( polarity, m + q, selected, a2, e2 )
        )
      }
      case (Imp(a1, a2), ETImp(e1, e2)) => {
        println( "Imp a1: " + a1)
        println( "Imp a2: " + a2)
        println( "Imp e1: " + e1)
        println( "Imp e2: " + e2)
        val q = qocc(a1, polarity)
        println("qocc: " + q)
        ETImp(
          desk(!polarity, m, selected, a1, e1 ),
          desk(polarity, m + q, selected, a2, e2)
        )
      }
      case (All(x, a1), _) if polarity => {
        // TODO
        e
      }
      case (All(x, a1), q @ ETWeakQuantifier(s, i)) if !polarity => {
        println( "WeakQuantifier x: " + x)
        println( "WeakQuantifier a1: " + a1)
        println( "WeakQuantifier s: " + s)
        println( "WeakQuantifier i: " + i)
        val tmp = i.map{ case (t, v) => {
          val pos: List[HOLPosition] = a1.find(x)
          val fprime: LambdaExpression = a1.replace(pos, t)
          println( "WeakQuantifier v: " + v)
          println( "WeakQuantifier f: " + a1 + "\n  {" + x + " -> " + t + "}--> fprime: " + fprime)
          (t -> desk(false, m, t :: selected, fprime, v))
        } }
        println( "WeakQuantifier tmp: " + tmp)
        ETWeakQuantifier(s, tmp)
      }
      case (Ex(x, a1), _) if !polarity => {
        // TODO
        e
      }
      case (Ex(x, a1), q @ ETWeakQuantifier(s, i)) if polarity => {
        println( "WeakQuantifier x: " + x)
        println( "WeakQuantifier a1: " + a1)
        println( "WeakQuantifier s: " + s)
        println( "WeakQuantifier i: " + i)
        val tmp = i.map{ case (t, v) => {
          val pos: List[HOLPosition] = a1.find(x)
          val fprime: LambdaExpression = a1.replace(pos, t)
          println( "WeakQuantifier v: " + v)
          println( "WeakQuantifier f: " + a1 + "\n  {" + x + " -> " + t + "}--> fprime: " + fprime)
          (t -> desk(true, m, t :: selected, fprime, v))
        } }
        println( "WeakQuantifier tmp: " + tmp)
        ETWeakQuantifier(s, tmp)
      }
      case (_, ETSkolemQuantifier(a1, skTerm, skDef, e1)) => {
        println("a1    : " + a1)
        println("skTerm: " + skTerm)
        println("skDef : " + skDef)
        println("e1    : " + e1)
        desk(polarity, m, selected, a1, e1)
      }
      case (_, ETAtom(a, p)) => {
        e
      }
      case (_, _) => {
        println( "UNSUPPORTED" )
        println()
        e
      }
    }
  }


  def qocc(a: LambdaExpression, polarity: Boolean): Int = {
    a match {
      case Neg(a1)     => qocc(a1, !polarity)
      case Or(a1, a2)  => qocc(a1, polarity) + qocc(a2, polarity)
      case And(a1, a2) => qocc(a1, polarity) + qocc(a2, polarity)
      case Imp(a1, a2) => qocc(a1, !polarity) + qocc(a2, polarity)
      case Ex(_, a1) if polarity   => qocc(a1, true)
      case Ex(_, a1) if !polarity  => 1 + qocc(a1, false)
      case All(_, a1) if polarity  => 1 + qocc(a1, true)
      case All(_, a1) if !polarity => qocc(a1, false)
      case _   => 0
    }
  }
  /*
  def pr(sequent: Sequent): LKProof = TopAxiom

  def permL(i: Int, sequent: Sequent, proof: LKProof) = ()

  def permR(i: Int, sequent: Sequent, proof: LKProof) = ()
  */
}
