package at.logic.algorithms.shlk

import at.logic.calculi.lk.base.{LKProof, Sequent}
import at.logic.calculi.lk.lkExtractors.{BinaryLKProof, UnaryLKProof}
import at.logic.calculi.lk.propositionalRules.Axiom
import at.logic.language.schema.{foVar, indexedFOVar}

object printSchemaProof {
  import at.logic.language.lambda.symbols._
  import at.logic.language.hol.logicSymbols._
  import at.logic.language.hol.{Or => HOLOr, Neg => HOLNeg, And => HOLAnd, _}
  import at.logic.language.lambda.typedLambdaCalculus._
  import at.logic.language.lambda.types._
  import at.logic.language.lambda.types.ImplicitConverters._
  import at.logic.language.schema.{IntVar, IntZero, IndexedPredicate, SchemaFormula, Succ, BigAnd, BigOr, IntegerTerm, IntConst}
  import at.logic.calculi.slk._


  def formulaToString(f:LambdaExpression) : String = f match {
    case BigAnd(v, formula, init, end) =>
      "⋀" + formulaToString(v) + "=(" + formulaToString(init) + ".." + formulaToString(end) + ")(" + formulaToString(formula) + ")"

    case BigOr(v, formula, init, end) =>
      "⋁" + formulaToString(v) + "=(" + formulaToString(init) + ".." + formulaToString(end) + ")(" + formulaToString(formula) + ")"

    case t : IntegerTerm  => parseIntegerTerm(t, 0)

      //this is for the case of sTerm
    case Function(name, args, _) if args.length != 0 && args.head.exptype == Tindex() => {
      if(args.length == 1)
        return name+"("+formulaToString(args.head)+")"
      else {
        return name+"("+formulaToString(args.head)+args.tail.foldRight("")((x,rez) => ","+formulaToString(x)+rez )+")"
      }
    }
    case App(x,y) => x match {
      case App(Var(name,tp),z) =>
        if (name.toString.matches("""[\w\p{InGreek}]*""")) name.toString+"("+formulaToString(z)+","+formulaToString(y)+")"
        else "("+formulaToString(z)+" "+name.toString()+" "+formulaToString(y)+")"
      case Var(name,tp) => tp match {
        case ->(To(), To()) => name.toString+formulaToString(y)
        case _ => y match {
          case Abs(x1,y1) => "("+name.toString+formulaToString(x1)+")"+formulaToString(y1)
          case _ => name.toString()+"("+formulaToString(y)+")"
        }
      }
      case _ => formulaToString(x) +"("+ formulaToString(y) +")"
    }
    case ifo:indexedFOVar => ifo.name.toString() + "_{"+ parseIntegerTerm(ifo.index.asInstanceOf[IntegerTerm], 0)+"}"
    case fo:foVar => fo.name.toString()
    case Var(name,t) => name.toString()
    case Abs(x,y) => formulaToString(y)
    case  x : Any    => "(unmatched class: "+x.getClass() + ")"
  }

  def parseIntegerTerm( t: IntegerTerm, n: Int) : String = t match {
    // FIXME: in the first case, we implicitely assume
    // that all IntConsts are 0!
    // this is just done for convenience, and should be changed ASAP
    case z : IntConst => n.toString
    case IntZero() => n.toString

    case v : IntVar => if (n > 0)
      v.toStringSimple + "+" + n.toString
    else
      v.toStringSimple
    case Succ(t) => parseIntegerTerm( t, n + 1 )
  }

  def sequentToString(s : Sequent) : String = {
    var sb = new scala.StringBuilder()
    var first = true
    for (f <- s.antecedent) {
      if (! first) sb.append(", ")
      else first = false
      sb.append(formulaToString(f.formula))
    }
    sb.append(Console.RED+" \u22a2 "+Console.RESET)
    first =true
    for (f <- s.succedent) {
      if (! first) sb.append(", ")
      else first = false
      sb.append(formulaToString(f.formula))
    }
    sb.toString
  }
  //def sequentToString(seq : Sequent): String = {
  //  seq.antecedent.toList.map(fo => fo.formula.toString+" <> " )+" |- "+ seq.succedent.toList.map(fo => fo.formula.toString+" <> ")
  //}

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