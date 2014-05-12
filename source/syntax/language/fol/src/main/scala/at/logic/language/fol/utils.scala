/**
 * Helper functions for first order logic
 */

package at.logic.language.fol

import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols.getRenaming
import at.logic.language.lambda.{freeVariables => freeVariablesLambda, rename => renameLambda}
import at.logic.language.hol.{isPrenex => isPrenexHOL, containsQuantifier => containsQuantifierHOL, getMatrix => getMatrixHOL, lcomp => lcompHOL}
import at.logic.language.hol.logicSymbols._
import scala.Some
import scala.Tuple3

// Returns a list *without duplicates* of the free variables in the expression.
// There is no guarantee on the ordering of the list.
object freeVariables {
  def apply(e: FOLExpression) : List[FOLVar] = freeVariablesLambda(e).asInstanceOf[List[FOLVar]]
}

// matches for consts and vars, but nothing else
object VarOrConst {
  def unapply(e:FOLExpression) = e match {
    case FOLVar(name) => Some(name)
    case FOLConst(name) => Some(name)
    case _ => None
  }
}

object isPrenex {
  def apply(e: FOLExpression) : Boolean = isPrenexHOL(e)
}

object containsQuantifier {
  def apply(e: FOLExpression) : Boolean = containsQuantifierHOL(e)
}

// Instantiates a term in a quantified formula (using the first quantifier).
object instantiate {
  def apply(f: FOLFormula, t: FOLTerm) : FOLFormula = f match {
    case AllVar(v, form) =>
      val sub = Substitution(v, t)
      sub(form)
    case ExVar(v, form) => 
      val sub = Substitution(v, t)
      sub(form)
    case _ => throw new Exception("ERROR: trying to replace variables in a formula without quantifier.") 
  }
}

// get a new variable/constant (similar to the current and) different from all 
// variables/constants in the blackList, returns this variable if this variable 
// is not in the blackList
object rename {
  // FIXME
  // Why doesn't the first method work??? If needed, the same should be done for renaming of constants...
  //def apply(v: FOLVar, blackList: List[FOLVar]) : FOLVar = renameLambda(v, blackList).asInstanceOf[FOLVar]
  def apply(v: FOLVar, blackList: List[FOLVar]) : FOLVar = new FOLVar(getRenaming(v.sym, blackList.map(v => v.sym)))
  def apply(c: FOLConst, blackList: List[FOLConst]) : FOLConst = renameLambda(c, blackList).asInstanceOf[FOLConst]

  // renames a list of variables to pairwise distinct variables
  // while avoiding names from blackList.
  def apply(vs: Set[FOLVar], blackList: Set[FOLVar]) : Map[FOLVar,FOLVar] = {
    val v_list = vs.toList
    ( v_list zip 
      v_list.foldLeft(Nil : List[FOLVar])( 
        (res, v) => res :+ apply( v, (blackList ++ res).toList ) ) ).toMap
  }
}

/** Returns whether t is a function. */
/** Returns whether t is a function whose name fulfills to a given condition. */
object isFunc {
  def apply(t:FOLTerm) : Boolean = isFunc(t,_ => true)
  def apply(t:FOLTerm, cond: String => Boolean) : Boolean = t match {
    case Function(f,_) => cond(f.toString)
    case _ => false
  }
}

/** Returns whether t is a variable. */
object isVar {
  def apply(t:FOLTerm) : Boolean = t match {
    case FOLVar(_) => true
    case _ => false
  }
}

/** Unsafely extracts the function name from a term. Fails if the term is not a function. */
object fromFunc {
  def apply(t:FOLTerm) = t match { case Function(f,_) => f }
}  
  
/** Unsafely extracts the function arguments from a term. Fails if the term is not a function. */
object fromFuncArgs {
  def apply(t:FOLTerm) = t match { case Function(_,a) => a}
}

object replaceLeftmostBoundOccurenceOf {
  def apply(variable : FOLVar, by : FOLVar, formula : FOLFormula) : (Boolean, FOLFormula) = {
    formula match {
      case Atom(_, _) => (false, formula)
      
      case Neg(f) => 
        val r = replaceLeftmostBoundOccurenceOf(variable, by, f)
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
        if ((v == variable) && (v != variable)) {
          println("Warning: comparing two variables, which have the same syntactic representation but differ on other things (probably different binding context)")
        }

        if (v == variable) {
          (true, AllVar(by, Substitution(variable, by).apply(f)))
        }
        else {
          val r = replaceLeftmostBoundOccurenceOf(variable, by, f)
          (r._1, AllVar(v, r._2))
        }

       case _ => throw new Exception("Unknown operator encountered during renaming of outermost bound variable. Formula is: "+formula)
    }
  }
}

// Instantiates all quantifiers of the formula with the terms in lst.
// OBS: the number of quantifiers in the formula must greater or equal than the
// number of terms in lst.
object instantiateAll {
  def apply(f: FOLFormula, lst: List[FOLTerm]) : FOLFormula = lst match {
    case Nil => f
    case h :: t => instantiateAll(instantiate(f, h), t)
  }
}

// TODO: some of the methods below should work for FOL and HOL...

// Transforms a formula to negation normal form (transforming also
// implications into disjunctions)
object toNNF {
  def apply(f: FOLFormula) : FOLFormula = f match {
    case Atom(_,_) => f
    case Function(_,_) => f
    case Imp(f1,f2) => Or(toNNF(Neg(f1)), toNNF(f2))
    case And(f1,f2) => And(toNNF(f1), toNNF(f2))
    case Or(f1,f2) => Or(toNNF(f1), toNNF(f2))
    case ExVar(x,f) => ExVar(x, toNNF(f))
    case AllVar(x,f) => AllVar(x, toNNF(f))
    case Neg(f) => f match {
      case Atom(_,_) => Neg(f)
      case Function(_,_) => Neg(f)
      case Neg(f1) => toNNF(f1)
      case Imp(f1,f2) => And(toNNF(f1), toNNF(Neg(f2)))
      case And(f1,f2) => Or(toNNF(Neg(f1)), toNNF(Neg(f2)))
      case Or(f1,f2) => And(toNNF(Neg(f1)), toNNF(Neg(f2)))
      case ExVar(x,f) => AllVar(x, toNNF(Neg(f)))
      case AllVar(x,f) => ExVar(x, toNNF(Neg(f)))
      case _ => throw new Exception("ERROR: Unexpected case while transforming to negation normal form.")
    }
    case _ => throw new Exception("ERROR: Unexpected case while transforming to negation normal form.")
  }
}

// Distribute Ors over Ands
object distribute {
  def apply(f: FOLFormula) : FOLFormula = f match {
    case Atom(_,_) => f
    // Negation has only atomic scope
    case Neg(Atom(_,_)) => f
    case And(f1, f2) => And(distribute(f1), distribute(f2))
    case Or(f1, And(f2,f3)) => And(distribute(Or(f1,f2)), distribute(Or(f1,f3)))
    case Or(And(f1,f2), f3) => And(distribute(Or(f1,f3)), distribute(Or(f2,f3)))
    case Or(f1, f2) => Or(distribute(f1), distribute(f2))
    case _ => throw new Exception("ERROR: Unexpected case while distributing Ors over Ands.")
  }
}

// Transforms a formula to conjunctive normal form
// 1. Transform to negation normal form
// 2. Distribute Ors over Ands
// OBS: works for propositional formulas only
// TODO: tests for this
object toCNF {
  def apply(f: FOLFormula) : FOLFormula = distribute(toNNF(f))
}

object numOfAtoms {
  def apply(f: FOLFormula) : Int = f match {
    case Atom(_,_) => 1
    case Function(_,_) => 1
    case Imp(f1,f2) => numOfAtoms(f1) + numOfAtoms(f2)
    case And(f1,f2) => numOfAtoms(f1) + numOfAtoms(f2)
    case Or(f1,f2) => numOfAtoms(f1) + numOfAtoms(f2)
    case ExVar(x,f) => numOfAtoms(f)
    case AllVar(x,f) => numOfAtoms(f)
    case Neg(f) => numOfAtoms(f)
    case _ => throw new Exception("ERROR: Unexpected case while counting the number of atoms.")
  }
}

// Returns the quantifier free part of a prenex formula
object getMatrix {
  def apply(f: FOLFormula) : FOLFormula = getMatrixHOL(f).asInstanceOf[FOLFormula]
}

/** Replaces all free ocurrences of a variable by another variable in a FOL formula.
  *
  * @param variable The name of the free variable to replace.
  * @param by The name of the new variable.
  * @param formula The formula in which to replace [variable] with [by].
  */
object replaceFreeOccurenceOf {
  def apply(variable: String, by: String, formula: FOLFormula) : FOLFormula = {
    replaceFreeOccurenceOf(FOLVar(variable), FOLVar(by), formula)
  }
  def apply(variable: String, by: String, term: FOLTerm) : FOLTerm = term match {
    case Function(f,terms) => Function(f, terms.map(x => replaceFreeOccurenceOf(variable, by, x)))
    case (v @ FOLVar(x)) => if (x.toString() == variable) FOLVar(by) else v
    case (c @ FOLConst(_)) => c
  }
  def apply(variable : FOLVar, by : FOLVar, formula : FOLFormula) : FOLFormula = {
    formula match {
      case Atom(_, args) => Substitution(variable, by).apply(formula)
     
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
}

// Transforms a list of literals into an implication formula, with negative 
// literals on the antecedent and positive literals on the succedent.
object reverseCNF {
  def apply(f: List[FOLFormula]) : FOLFormula = {
    val (ant, succ) = f.foldRight((List[FOLFormula](), List[FOLFormula]())) {
      case (f, (ant, succ)) => f match {
        case Neg(a) => (a::ant, succ)
        case a => (ant, a::succ)
      }
    }
    val conj = And(ant)
    val disj = Or(succ)
    Imp(conj, disj)
  }
}

/** Adds a list of universal quantifiers to a FOL formula.
  * The first element of the list will be the outermost quantifier.
  * A generalization of applying AllVar(x,f).
  *
  * It always holds that addQuantifiers(f,removeQuantifiers(f)._1) = f.
  *
  * @param f A FOL formula, typically with the free variables of xs.
  * @param xs A list of variables [x1,...,xn] over which to universally quantify f.
  * @return [forall x1,...,xn] f
  */
object addQuantifiers {
  def apply(f : FOLFormula, xs : List[FOLVar]) = xs.reverse.foldLeft(f)((f,x) => AllVar(x, f))
}

/** Strips the initial universal quantifiers from a FOL formula that begins
  * with a quantifier block.
  * A generalization of unapplying AllVar(x,f).
  * 
  * @param f A FOL formula of the form [forall x1,...,xn] f'.
  * @return The tuple ([xn,...,x1], f').
  */
object removeQuantifiers {
  def apply(f : FOLFormula) : (List[FOLVar], FOLFormula) = f match {
    case AllVar(x, f) => {
      val (xs,fret) = removeQuantifiers(f)
      (x :: xs, fret)
    }
    case f => (List[FOLVar](),f)
  }
}

/** Removes at most n universal quantifiers from a FOL formula that begins
  * with a quantifier block.
  *
  * See removeQuantifiers.
  *
  * @param f A FOL formula of the form [forall x1,...,xm] f'.
  * @param n The number of quantifiers to strip.
  * @return The tuple ([x1',...,xn], f'') where n' <= n & n' <= m and f' is a subformula
  * of f''.
  */
object removeNQuantifiers {
  def apply(f: FOLFormula, n: Int) : (List[FOLVar], FOLFormula) = f match {
    case AllVar(x, f) => {
      if (n > 0) {
        val (xs,fret) = removeNQuantifiers(f, n-1)
        (xs :+ x, fret)
      }
      else { (List[FOLVar](), AllVar(x, f)) }
    }
    case f => (List[FOLVar](), f)
  }
}

/** Given varName and an integer n,
  * returns the list [varName_0,...,varName_(n-1)],
  * where varName_i is a FOLVar with the same name.
  */
object createFOLVars {
  def apply(varName: String, n: Int) = {
    (0 to (n-1)).map(n => FOLVar((varName + "_" + n))).toList
  }
}

/** Returns the list (not set!) of all occurring variables, free or bound, in a FOL FORMULA, from left to right.
  *
  * @param f The FOL formula in which to collect the variables.
  * @return The list of occurring variables, from left to right. If a variable occurs multiple times
  *         in the formula, it will occur multiple times in the returned list.
  */
object collectVariables {
  def apply(f: FOLFormula) : List[FOLVar] = f match {
    case And(f1,f2) => collectVariables(f1) ++ collectVariables(f2)
    case Or(f1,f2) => collectVariables(f1) ++ collectVariables(f2)
    case Imp(f1,f2) => collectVariables(f1) ++ collectVariables(f2)
    case Neg(f1) => collectVariables(f1)
    case AllVar(_,f1) => collectVariables(f1)
    case ExVar(_,f1) => collectVariables(f1)
    case Atom(_,f1) => f1.map(f => collectVariables(f)).foldLeft(List[FOLVar]())(_ ++ _)
    case _ => throw new IllegalArgumentException("Unhandled case in fol.utils.collectVariables(FOLFormula)!")
  }
  
  def apply(f: FOLTerm) : List[FOLVar] = f match {
    case FOLVar(x) => List(FOLVar(x))
    case Function(_,terms) => terms.map(t => collectVariables(t)).foldLeft(List[FOLVar]())(_ ++ _)
    case FOLConst(_) => Nil
    case _ => throw new IllegalArgumentException("Unhandled case in fol.utils.collectVariables(FOLTerm)!")
  }
}

/** Helper function for checking whether a FOLVar is an eigenvariable.
  * This is used in computing cutIntroduction.Deltas.UnboundedVariableDelta
  * and GeneralizedGrammar.eigenvariables.
  * 
  * isEigenvariable(x, ev) == true iff x's name matches the format [ev]_[n],
  * where n is some non-negative integer.
  */
object isEigenvariable {
  def apply(x : FOLVar, eigenvariable : String) = x.toString.split('_') match {
    case Array(eigenvariable, n) => n.forall(Character.isDigit)
    case _ => false
  }
}

object lcomp {
  def apply(f: FOLFormula) = lcompHOL(f) 
}

object Utils {
  // Constructs the FOLTerm f^k(a)
  def iterateTerm( a: FOLTerm, f: String, k: Int ) : FOLTerm =
    if ( k < 0 ) throw new Exception("iterateTerm called with negative iteration count")
    else if ( k == 0 ) a
    else Function( f, iterateTerm( a, f, k-1 )::Nil )

  // Constructs the FOLTerm s^k(0)
  def numeral( k: Int ) = iterateTerm( FOLConst( "0" ).asInstanceOf[FOLTerm], "s" , k )


  // TODO: these functions should go to listSupport in dssupport in the
  // utils project.

  def removeDoubles[T](l : List[T]) : List[T] = {
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

  //auxiliary function which removes duplications from list of type:
  //List[List[(String, Tree[AnyRef], Set[FormulaOccurrence])]]
  //and type
  ////List[List[(String, Tree[AnyRef], (Set[FormulaOccurrence], Set[FormulaOccurrence]))]]

  def removeDoubles3[T,R](l : List[Tuple3[String,T,R]]) : List[Tuple3[String,T,R]] = {
    l match {
      case head :: tail =>
        if (tail.map(tri => tri._3).contains(head._3))
          removeDoubles3(tail)
        else
          head :: removeDoubles3(tail)
      case Nil => Nil
    }
  }
}


object toAbbreviatedString {
  /**
   * This function takes a FOL construction and converts it to a abbreviated string version. The abbreviated string version is made
   * by replacing the code construction for logic symbols by string versions in the file language/hol/logicSymbols.scala.
   * Several recursive function calls will be transformed into an abbreviated form (e.g. f(f(f(x))) => f^3(x)).
   * Terms are also handled by the this function.
   *
  @param  e  The method has no parameters other then the object which is to be written as a string
   *
  @throws Exception This occurs when an unknown subformula is found when parsing the FOL construction
   *
  @return A String which contains the defined symbols in language/hol/logicSymbols.scala.
   *
   */
  def apply(e:FOLExpression) : String = {

    val p = pretty(e)

    val r : String = e match {
      case Function(x, args) => {
        if(p._1 != p._2 && p._2 != "tuple1")
          if(p._3 > 0)
            return p._2 + "^"+(p._3+1)+"("+p._1+") "
          else
            return p._1
        else
          return p._1
      }
      case _ => return p._1
    }

    return r
  }

  private def pretty(exp : FOLExpression) : (String, String, Int) = {

    val s : (String, String, Int) = exp match {
      case null => ("null", "null", -2)
      case FOLVar(x) => (x.toString(), x.toString(), 0)
      case Atom(x, args) => {
        (x.toString() + "(" + (args.foldRight(""){  case (x,"") => "" + toAbbreviatedString(x)
        case (x,str) => toAbbreviatedString(x) + ", " + str
        }) + ")", x.toString(), 0)
      }
      case Function(x, args) => {
        // if only 1 argument is provided
        // check if abbreviating of recursive function calls is possible
        if(args.length == 1)
        {
          val p = pretty(args.head)

          // current function is equal to first and ONLY argument
          if( p._2 == x.toString() )
          {
            // increment counter and return (<current-string>, <functionsymbol>, <counter>)
            return (p._1, x.toString(), p._3+1)
          }
          // function symbol has changed from next to this level
          else
          {

            // in case of multiple recursive function calls
            if(p._3 > 0)
            {
              return (p._2+"^"+p._3+"("+p._1+")", x.toString(), 0)
            }
            // otherwise
            else
            {
              return (p._1, x.toString(), 1)
            }
          }
        }
        else
        {
          return (x.toString()+"("+ (args.foldRight(""){   case (x,"") => toAbbreviatedString(x)
          case (x,s) => toAbbreviatedString(x) + ", " + s
          })+ ")", x.toString(), 0)
        }

      }
      case And(x,y) => ("(" + toAbbreviatedString(x) + " " + AndSymbol + " " + toAbbreviatedString(y) + ")", AndSymbol.toString(), 0)
      case Equation(x,y) => ("(" + toAbbreviatedString(x) + " " + EqSymbol + " " + toAbbreviatedString(y) + ")", EqSymbol.toString(), 0)
      case Or(x,y) => ("(" + toAbbreviatedString(x) + " " + OrSymbol + " " + toAbbreviatedString(y) + ")", OrSymbol.toString(), 0)
      case Imp(x,y) => ("(" + toAbbreviatedString(x) + " " + ImpSymbol + " " + toAbbreviatedString(y) + ")", ImpSymbol.toString(), 0)
      case Neg(x) => (NegSymbol + toAbbreviatedString(x), NegSymbol.toString(), 0)
      case ExVar(x,f) => (ExistsSymbol + toAbbreviatedString(x) + "." + toAbbreviatedString(f), ExistsSymbol.toString(), 0)
      case AllVar(x,f) => (ForallSymbol + toAbbreviatedString(x) + "." + toAbbreviatedString(f), ForallSymbol.toString(), 0)
      case FOLAbs(v, exp) => ("(λ" + toAbbreviatedString(v) + "." + toAbbreviatedString(exp) + ")", "λ", 0)
      case FOLApp(l,r) => ("(" + toAbbreviatedString(l) + ")(" + toAbbreviatedString(r) + ")", "()()", 0)
      case FOLConst(x) => (x.toString(),x.toString(), 0)
      case _ => throw new Exception("ERROR: Unknown FOL expression.");
    }
    return s

  }
}