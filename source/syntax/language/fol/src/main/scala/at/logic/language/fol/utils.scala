/**
 * Created by IntelliJ IDEA.
 * User: marty
 * Date: 10/3/11
 * Time: 5:16 PM
 */

package at.logic.language.fol

import at.logic.language.hol.logicSymbols.ConstantSymbolA
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.symbols.{VariableSymbolA, VariableStringSymbol}
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression}
import at.logic.language.lambda.types.->
import at.logic.language.lambda.types.{To, Ti, TA}

/** Utility functions for the manipulation of
  * first-order formulas.
  */
object Utils {
  // universally closes off the given fol formula
  def universal_closure_of(f : FOLFormula) : FOLFormula = {
    val free_vars = getFreeVariablesFOL(f)
    free_vars.foldRight(f)((v : FOLVar, f : FOLFormula) => AllVar(v,f))
  }

  def isFirstOrderType( exptype: TA ) = isFunctionType( exptype ) || isPredicateType( exptype )

  def isFunctionType( exptype: TA ) = checkType( exptype, Ti(), Ti() )

  def isPredicateType( exptype: TA ) = checkType( exptype, To(), Ti() )

  def checkType( toCheck: TA, retType : TA, argType: TA ) : Boolean =
    toCheck match {
      case t : Ti => t == retType
      case t : To => t == retType
      case ->(ta, tr) => ta == argType && checkType( tr, retType, argType )
  }

  /** Returns whether t is a function. */
  def isFunc(t:FOLTerm) : Boolean = isFunc(t,_ => true)

  /** Returns whether t is a variable. */
  def isVar(t:FOLTerm) : Boolean = t match {
    case FOLVar(_) => true
    case _ => false
  }

  /** Returns whether t is a function whose name fulfills to a given condition. */
  def isFunc(t:FOLTerm, cond: String => Boolean) : Boolean = t match {
    case Function(f,_) => cond(f.toString)
    case _ => false
  }

  /** Unsafely extracts the function name from a term. Fails if the term is not a function. */
  def fromFunc(t:FOLTerm) = t match { case Function(f,_) => f }
  /** Unsafely extracts the function arguments from a term. Fails if the term is not a function. */
  def fromFuncArgs(t:FOLTerm) = t match { case Function(_,a) => a}

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
          println("Warning: comparing two variables, which have the same syntactic representation but differ on other things (probably different binding context)")
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

  /**
    * Replaces all free ocurrences of a variable by another variable in a FOL formula.
    *
    * @param variable The free variable to replace.
    * @param by The new variable.
    * @param formula The formula in which to replace [variable] with [by].
    */
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

  /** Replaces all free ocurrences of a variable by another variable in a FOL formula.
    *
    * @param variable The name of the free variable to replace.
    * @param by The name of the new variable.
    * @param formula The formula in which to replace [variable] with [by].
    */
  def replaceFreeOccurenceOf(variable: String, by: String, formula: FOLFormula) : FOLFormula = {
    replaceFreeOccurenceOf(FOLVar(new VariableStringSymbol(variable)), FOLVar(new VariableStringSymbol(by)), formula)
  }

  /** Replaces all free ocurrences of a variable by another variable in a FOL term.
    *
    * @param variable The name of the free variable to replace.
    * @param by The name of the new variable.
    * @param formula The formula in which to replace [variable] with [by].
    */
  def replaceFreeOccurenceOf(variable: String, by: String, term: FOLTerm) : FOLTerm = term match {
    case Function(f,terms) => Function(f, terms.map(x => replaceFreeOccurenceOf(variable, by, x)))
    case (v@FOLVar(x)) => if (x.toString() == variable) FOLVar(new VariableStringSymbol(by)) else v
    case (c@FOLConst(_)) => c
  }

  // TODO: the following three methods can be implemented for HOL.

  // Transforms a list of literals into an implication formula, with negative 
  // literals on the antecedent and positive literals on the succedent.
  def reverseCNF(f: List[FOLFormula]) : FOLFormula = {
    val (ant, succ) = f.foldRight((List[FOLFormula](), List[FOLFormula]())) {
      case (f, (ant, succ)) => f match {
        case Neg(a) => (a::ant, succ)
        case a => (ant, a::succ)
      }
    }
    val conj = andN(ant)
    val disj = orN(succ)
    Imp(conj, disj)
  }

  // Iterated disjunction
  // Assume that fs is nonempty
  def orN(fs: List[FOLFormula]) : FOLFormula = fs match {
    case Nil => BottomC //throw new Exception("ERROR: Cannot generate a disjunction of an empty list.")
    case f::Nil => f
    case f::rest => Or(f, orN( rest ) )
  }
  
  // Iterated conjunction
  // Assume that fs is nonempty
  def andN(fs: List[FOLFormula]) : FOLFormula = fs match {
    case Nil => TopC //throw new Exception("ERROR: Cannot generate a conjunction of an empty list.")
    case f::Nil => f
    case f::rest => And(f, andN( rest ) )
  }

  // Constructs the FOLTerm f^k(a)
  def iterateTerm( a: FOLTerm, f: ConstantStringSymbol, k: Int ) : FOLTerm =
    if ( k < 0 ) throw new Exception("iterateTerm called with negative iteration count")
    else if ( k == 0 ) a
    else Function( f, iterateTerm( a, f, k-1 )::Nil )

  // Constructs the FOLTerm s^k(0)
  def numeral( k: Int ) = iterateTerm( FOLConst( ConstantStringSymbol( "0" )), ConstantStringSymbol( "s" ), k )


  // TODO: maybe these functions should go to listSupport in dssupport in the
  // utils project.

  def removeDoubles[T](l : List[T]) : List[T] = {
    removeDoubles_(l.reverse).reverse
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

  def between(lower :Int, upper : Int) : List[Int] = {
    if (lower > upper)
      List()
    else
      lower :: between (lower+1, upper)
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
  def addQuantifiers(f : FOLFormula, xs : List[FOLVar]) = xs.reverse.foldLeft(f)((f,x) => AllVar(x, f))

  /** Strips the initial universal quantifiers from a FOL formula that begins
    * with a quantifier block.
    * A generalization of unapplying AllVar(x,f).
    * 
    * @param f A FOL formula of the form [forall x1,...,xn] f'.
    * @return The tuple ([xn,...,x1], f').
    */
  def removeQuantifiers(f : FOLFormula) : (List[FOLVar], FOLFormula) = f match {
    case AllVar(x, f) => {
      val (xs,fret) = removeQuantifiers(f)
      (x :: xs, fret)
    }
    case f => (List[FOLVar](),f)
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
  def removeNQuantifiers(f: FOLFormula, n: Int) : (List[FOLVar], FOLFormula) = f match {
    case AllVar(x, f) => {
      if (n > 0) {
        val (xs,fret) = removeNQuantifiers(f, n-1)
        (xs :+ x, fret)
      }
      else { (List[FOLVar](), AllVar(x, f)) }
    }
    case f => (List[FOLVar](), f)
  }

  /** Given varName and an integer n,
    * returns the list [varName_0,...,varName_(n-1)],
    * where varName_i is a FOLVar with the same name.
    */
  def createFOLVars(varName: String, n: Int) = {
    (0 to (n-1)).map(n => FOLVar(new VariableStringSymbol(varName + "_" + n))).toList
  }

  /** Returns the list (not set!) of all occurring variables, free or bound, in a FOL FORMULA, from left to right.
    *
    * @param f The FOL formula in which to collect the variables.
    * @return The list of occurring variables, from left to right. If a variable occurs multiple times
    *         in the formula, it will occur multiple times in the returned list.
    */
  def collectVariables(f: FOLFormula) : List[FOLVar] = f match {
    case And(f1,f2) => collectVariables(f1) ++ collectVariables(f2)
    case Or(f1,f2) => collectVariables(f1) ++ collectVariables(f2)
    case Imp(f1,f2) => collectVariables(f1) ++ collectVariables(f2)
    case Neg(f1) => collectVariables(f1)
    case AllVar(_,f1) => collectVariables(f1)
    case ExVar(_,f1) => collectVariables(f1)
    case Atom(_,f1) => f1.map(collectVariables).foldLeft(List[FOLVar]())(_ ++ _)
    case _ => throw new IllegalArgumentException("Unhandled case in fol.utils.collectVariables(FOLFormula)!")
  }

  /** Returns the list (not set!) of all occurring variables, free or bound, in a FOL TERM, from left to right.
    *
    * @param f The FOL term in which to collect the variables.
    * @return The list of occurring variables, from left to right. If a variable occurs multiple times
    *         in the formula, it will occur multiple times in the returned list.
    */
  def collectVariables(f: FOLTerm) : List[FOLVar] = f match {
    case FOLVar(x) => List(FOLVar(x))
    case Function(_,terms) => terms.map(collectVariables).foldLeft(List[FOLVar]())(_ ++ _)
    case FOLConst(_) => Nil
    case _ => throw new IllegalArgumentException("Unhandled case in fol.utils.collectVariables(FOLTerm)!")
  }

  /** Helper function for checking whether a FOLVar is an eigenvariable.
    * This is used in computing cutIntroduction.Deltas.UnboundedVariableDelta
    * and GeneralizedGrammar.eigenvariables.
    * 
    * isEigenvariable(x, ev) == true iff x's name matches the format [ev]_[n],
    * where n is some non-negative integer.
    */
def isEigenvariable(x : FOLVar, eigenvariable : String) = x.toString.split('_') match {
    case Array(eigenvariable, n) => n.forall(Character.isDigit)
    case _ => false
  }
}
