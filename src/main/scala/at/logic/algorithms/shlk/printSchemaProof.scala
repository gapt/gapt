package at.logic.algorithms.shlk

import at.logic.language.schema._
import at.logic.calculi.lk.base.{LKProof, Sequent}
import at.logic.calculi.lk.{BinaryLKProof, UnaryLKProof, Axiom}
import at.logic.calculi.slk._

object printSchemaProof {

  // TODO: this should move to where Sequent is declared...
  def sequentToString(s : Sequent) : String = {
    var sb = new scala.StringBuilder()
    var first = true
    for (f <- s.antecedent) {
      if (! first) sb.append(", ")
      else first = false
      sb.append(f.toString)
    }
    sb.append(Console.RED+" \u22a2 "+Console.RESET)
    first =true
    for (f <- s.succedent) {
      if (! first) sb.append(", ")
      else first = false
      sb.append(f.formula.toString)
    }
    sb.toString
  }

  def apply(p: LKProof):Unit = p match {
    case SchemaProofLinkRule( seq, _, _) => println("\n SchemaProofLinkRule : "+sequentToString(seq))
    case Axiom(seq) => println("\n Axiom : " + sequentToString(seq))

    case UnaryLKProof(_, up, r, _, _) => {
      apply(up)
      println("\n"+ p.rule + " : " + sequentToString(r))
    }
    case BinaryLKProof(_, up1, up2, r, _, _, _) => {
      apply(up1)
      apply(up2)
      println("\n"+ p.rule + " : " + sequentToString(r))
    }

    case AndEquivalenceRule1(up, r, _, _) =>  {
      apply(up)
      println("\n"+ p.rule + " : "+sequentToString(r))
    }
    case AndEquivalenceRule2(up, r, _, _) =>  {
      apply(up)
      println("\n"+ p.rule + " : "+sequentToString(r))
    }
    case AndEquivalenceRule3(up, r, _, _) =>  {
      apply(up)
      println("\n"+ p.rule + " : "+sequentToString(r))
    }
    case OrEquivalenceRule1(up, r, _, _) =>  {
      apply(up)
      println("\n"+ p.rule + " : "+sequentToString(r))
    }
    case OrEquivalenceRule2(up, r, _, _) =>  {
      apply(up)
      println("\n UnaryProof : "+sequentToString(r))
    }
    case OrEquivalenceRule3(up, r, _, _) =>  {
      apply(up)
      println("\n UnaryProof : "+sequentToString(r))
    }
    case TermEquivalenceRule1(up, r, _, _) =>  {
      apply(up)
      println("\n UnaryProof : "+sequentToString(r))
    }
    case trsArrowRule(up, r, _, _) =>  {
      apply(up)
      println("\n"+ p.rule + " : "+sequentToString(r))
    }
    case foldLeftRule(up, r, _, _) =>  {
      apply(up)
      println("\n"+ p.rule + " : "+sequentToString(r))
    }
    case _ => println("ERROR in printSchemaProof : "+p.rule)
  }
}
