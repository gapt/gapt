package at.logic.calculi.lkmodulo

import _root_.at.logic.calculi.proofs.UnaryRuleTypeA
import _root_.at.logic.language.fol._
import _root_.at.logic.language.fol.equations.Equation
import _root_.at.logic.language.hol.logicSymbols.ConstantSymbolA
import _root_.at.logic.language.lambda.substitutions.Substitution
import _root_.at.logic.language.lambda.symbols.{VariableSymbolA, VariableStringSymbol}
import _root_.at.logic.language.lambda.typedLambdaCalculus.{App, AbsInScope, Var, LambdaExpression}
import _root_.at.logic.language.lambda.types.->
import at.logic.calculi.lk.base.LKProof
import at.logic.calculi.lk._
import collection.immutable.HashSet

trait LKModuloRule

case object ConversionLeftRuleType extends UnaryRuleTypeA
case object ConversionRightRuleType extends UnaryRuleTypeA


abstract class REequalityA {
  val equational_rules : Set[Equation];
  val rewrite_rules : Set[Tuple2[FOLFormula, FOLFormula]];

  def reequal_to(s : FOLFormula, t : FOLFormula) : Boolean;
}

abstract class EequalityA extends REequalityA {
  /* the set of rewrite rules is empty in a pure equational theory */
  override val rewrite_rules = Set[Tuple2[FOLFormula, FOLFormula]]()
  override def reequal_to(s : FOLFormula, t : FOLFormula) : Boolean = reequal_to_(s,t)

  def universal_closure_of(f : FOLFormula) : FOLFormula = {
    val free_vars = getFreeVariablesFOL(f)
    free_vars.foldRight(f)((v : FOLVar, f : FOLFormula) => AllVar(v,f))
  }

  // this is nearly the same as LambdaExpression.getFreeAndBoundVariables, but returns the variabes in the order encountered
  def getOrderedFreeAndBoundVariables(expression: LambdaExpression):Tuple2[List[Var],List[Var]] = expression match {
    case v: Var if v.isFree && v.name.isInstanceOf[VariableSymbolA]=> (List(v), List())
    case v: Var if v.name.isInstanceOf[VariableSymbolA] => (List(), List(v))
    case v: Var => (List(), List())// not variables (constants in this case)
    case App(exp, arg) => {
      val mFBV = getOrderedFreeAndBoundVariables(exp)
      val nFBV = getOrderedFreeAndBoundVariables(arg)
      (removeDoubles(mFBV._1 ::: nFBV._1), removeDoubles(mFBV._2 ::: nFBV._2))
    }
    case AbsInScope(v, exp) => {
      val mFBV = getOrderedFreeAndBoundVariables(exp)
      val bound = removeDoubles(mFBV._2 ::: List(v))
      (mFBV._1, bound)
    }
  }


  def canonical_renaming_of(f: LambdaExpression) : LambdaExpression = {
    // TODO: canonical_renaming_of should be generalized to lambda expressions
    /*
    val freeandbound = f.getFreeAndBoundVariables()
    val free_vars = freeandbound._1
    val bound_vars = freeandbound._2

    val prefix = "x_"
    val pairs = free_vars.zip(between(0, free_vars.size)).map( (el : (Var, Int)) => (el._1.asInstanceOf[FOLVar], FOLVar(new VariableStringSymbol(prefix+el._2))) )
    val subs = Substitution(pairs.toList)

    //val subs = Substitution(free_vars.foldLeft() (f : Var) => (f.asInstanceOf[FOLVar], FOLVar(new VariableStringSymbol(prefix+ (counter++))))  ))






    subs.apply(f)*/
    f
  }

  private def removeDoubles[T](l : List[T]) : List[T] = {
    removeDoubles_(l.reverse).reverse
  }

  private def removeDoubles_[T](l : List[T]) : List[T] = {
    l match {
      case head :: tail =>
        if (tail.contains(head))
          removeDoubles(tail)
        else
          head :: removeDoubles(tail)
      case Nil => Nil
    }
  }

  private def between(lower :Int, upper : Int) : List[Int] = {
    if (lower > upper)
      List()
    else
      lower :: between (lower+1, upper)
  }

  def replaceLeftmostBoundOccurenceOf(variable : FOLVar, by : FOLVar, formula : FOLFormula) :
   (Boolean, FOLFormula) = {
    //println("replacing "+variable+" by "+by+" in "+formula)
    formula match {
      case Atom(_, _) => (false, formula)

      case Neg(f) =>
        val r = replaceLeftmostBoundOccurenceOf(variable, by, f )
        (r._1, Neg(r._2))

      case And(f1,f2) =>
        val r1 = replaceLeftmostBoundOccurenceOf(variable, by, f1)
        if (r1._1 == true)
          (true, And(r1._2, f2))
        else {
          val r2 = replaceLeftmostBoundOccurenceOf(variable, by, f2)
          (r2._1, And(f1, r2._2))
        }

      case Or(f1,f2) =>
        val r1 = replaceLeftmostBoundOccurenceOf(variable, by, f1)
        if (r1._1 == true)
          (true, Or(r1._2, f2))
        else {
          val r2 = replaceLeftmostBoundOccurenceOf(variable, by, f2)
          (r2._1, Or(f1, r2._2))
        }

      case ExVar(v, f)  =>
          val r = replaceLeftmostBoundOccurenceOf(variable, by, f)
          (r._1, ExVar(v, r._2))

      case AllVar(v, f)  =>
        if ((v =^ variable) && (v != variable)) {
          println("Warning: comparing two variables, which are syntactically the equal but not completely equal (probably different binding context)")
        }

        if (v == variable) {
          (true, AllVar(by, Substitution[LambdaExpression](variable, by).apply(f).asInstanceOf[FOLFormula]))
        }
        else {
          val r = replaceLeftmostBoundOccurenceOf(variable, by, f)
          (r._1, AllVar(v, r._2))
        }

       case _ => throw new Exception("Unknown operator encountered during renaming of outermost bound variable. Formula is: "+formula)

    }
  }


  def replaceFreeOccurenceOf(variable : FOLVar, by : FOLVar, formula : FOLFormula) : FOLFormula = {
    formula match {
      case Atom(_, args) => Substitution[LambdaExpression](variable, by).apply(formula).asInstanceOf[FOLFormula]

      case Neg(f) =>
        Neg(replaceFreeOccurenceOf(variable, by, f ))

      case And(f1,f2) =>
        val r1 = replaceFreeOccurenceOf(variable, by, f1)
        val r2 = replaceFreeOccurenceOf(variable, by, f2)
        And(r1,r2)

      case Or(f1,f2) =>
        val r1 = replaceFreeOccurenceOf(variable, by, f1)
        val r2 = replaceFreeOccurenceOf(variable, by, f2)
        Or(r1,r2)

      case ExVar(v, f)  =>
        if (v.syntaxEquals(variable))
          formula
        else
          ExVar(v, replaceFreeOccurenceOf(variable, by, f))

      case AllVar(v, f)  =>
        if (v.syntaxEquals(variable))
          formula
        else
          AllVar(v, replaceFreeOccurenceOf(variable, by, f))

       case _ => throw new Exception("Unknown operator encountered during renaming of outermost bound variable. Formula is: "+formula)

    }
  }



  def canonical_renaming_of(f: FOLFormula) : FOLFormula = {
    val boundandfree = getOrderedFreeAndBoundVariables(f)
    val free_variables : List[Var] = boundandfree._1.toList
    val bound_variables : List[Var] = boundandfree._2.toList.map(
      (x : Var) => x match { case Var(symbol, exptype) =>  (x.factory.createVar(symbol,exptype)) }
    )

    var freevar_count = free_variables.size
    val names : List[FOLVar] = between(0, freevar_count - 1).map((n:Int) => FOLVar(new VariableStringSymbol("x_" + n) ))

    //println(boundandfree)

    var sentence = f
    for (pair <- free_variables zip names) {
      sentence = replaceFreeOccurenceOf(pair._1.asInstanceOf[FOLVar], pair._2, sentence)
    }

    for (v <- bound_variables) {
      sentence = replaceLeftmostBoundOccurenceOf(v.asInstanceOf[FOLVar], FOLVar(new VariableStringSymbol("x_"+freevar_count)), sentence)._2
      freevar_count = freevar_count +1
    }

    //println(sentence)

    sentence
  }

   private def canonical_renaming_of(f: FOLFormula, index : Int) : (FOLFormula, Int) = {
     (f,index)
   }


  private def reequal_to_(s : FOLFormula, t : FOLFormula) : Boolean = {
    def tuples_equals(el : Tuple2[FOLTerm, FOLTerm] ) : Boolean = (word_equalsto(el._1, el._2))

    (s,t) match {
      case (Atom( sym1: ConstantSymbolA, args1: List[FOLTerm]), Atom( sym2: ConstantSymbolA, args2: List[FOLTerm])) =>
        (sym1 == sym2) &&
        (args1.length == args2.length) &&
        ( (args1 zip args2) forall (tuples_equals))

      case (Neg(f1), Neg(f2)) =>
        reequal_to_(f1,f2)

      case (And(f1,f2), And(g1,g2)) =>
        reequal_to_(f1,g2) && reequal_to (f2,g2)

      case (Or(f1,f2), Or(g1,g2)) =>
        reequal_to_(f1,g2) && reequal_to (f2,g2)

      /* these two rules work only if the variables are canonically renamed in both formulas */
      case (AllVar(x1,t1), AllVar(x2,t2)) =>
        (x1 == x2) && reequal_to_ (t1,t2)

      case (ExVar(x1,t1), ExVar(x2,t2)) =>
        (x1 == x2) && reequal_to_ (t1,t2)

      case default => false
    }
  }

  def word_equalsto(s : FOLTerm, t : FOLTerm) : Boolean
  def unifies_with(s : FOLTerm, t : FOLTerm) : Option[Substitution[FOLTerm]]
}


object ConversionRightRule {
  def apply(premise : LKProof ) = null
}