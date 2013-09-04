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
import at.logic.language.lambda.symbols.VariableSymbolA
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression}
import at.logic.language.lambda.types.->
import at.logic.language.lambda.types.{To, Ti, TA}

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
          println("Warning: comparing two variables, which have the same sytactic representatio but differ on other things (probably different binding context)")
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
    case Nil => throw new Exception("ERROR: Cannot generate a disjunction of an empty list.")
    case f::Nil => f
    case f::rest => Or(f, orN( rest ) )
  }
  
  // Iterated conjunction
  // Assume that fs is nonempty
  def andN(fs: List[FOLFormula]) : FOLFormula = fs match {
    case Nil => throw new Exception("ERROR: Cannot generate a conjunction of an empty list.")
    case f::Nil => f
    case f::rest => And(f, andN( rest ) )
  }

  // Constructs the FOLTerm f^k(a)
  def iterateTerm( a: FOLTerm, f: ConstantStringSymbol, k: Int ) : FOLTerm =
    if ( k == 0 ) a else Function( f, iterateTerm( a, f, k-1 )::Nil )

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

}
