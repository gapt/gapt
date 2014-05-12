
/*
See comment in ACUnification.scala

package at.logic.algorithms.unification

import at.logic.language.fol.{Function, FOLConst, FOLVar, FOLTerm}
//import at.logic.language.lambda.symbols.{VariableSymbolA, VariableStringSymbol}

object TermUtils {
  //val generator = new VariableGenerator("z_")

  // returns a list of all variables in the term
  def getVariableContext(term: FOLTerm): List[FOLVar] = term match {
    case FOLVar(_) => List(term.asInstanceOf[FOLVar])
    case FOLConst(_) => Nil
    case Function(_, args) => (args.map(x => getVariableContext(x))).reduceLeft(_ ++ _)
  }

  // defines a lexicographic recursive term-ordering - since variables, constants and function symbols
  // only share their namespace by convention, an ordering on term type is also implemented: const < var < fun
  def term_<(term1: FOLTerm, term2: FOLTerm): Boolean = {
    //var < const < f; for equal terms: symbol name string less than, for function equal symbols recursive
    term1 match {
      case FOLConst(c1) => term2 match {
        case FOLConst(c2) => c1.toString < c2.toString;
        case _ => true
      }
      case FOLVar(v1) => term2 match {
        case FOLVar(v2) => v1.toString < v2.toString;
        case FOLConst(_) => false;
        case _ => true
      }
      case Function(f1, args1) => term2 match {
        case Function(f2, args2) =>
          if (f1.toString == f2.toString) {
            var lt = false
            for (i <- args1 zip args2) {
              if (term_<(i._1, i._2)) lt = true
            }
            lt
          } else {
            f1.toString < f2.toString
          }
        case _ => false
      }
    }
  }

}

object MathUtils {
  // greatest common divisor of x and y - only works for x>0 and y>0
  def gcd(x: Int, y: Int) = {
    //Euclidian Algorithm
    var m = if (x < y) x else y
    var n = if (x < y) y else x
    var temp = 0
    while (n != 0) {
      temp = m % n
      m = n
      n = temp
    }
    m
  }

  // least common multiple of x and y
  def lcm(x: Int, y: Int) = x * y / gcd(x, y)

  // least common multiple of a list
  def lcm(xs: List[Int]) = xs.foldLeft(1)((x, y) => x * y / gcd(x, y))

  // product of a list
  def product(l: List[Int]) = l.foldLeft(1)(_ * _)

  // powerset definition for lists
  def powerset[A](l: List[A]): List[List[A]] = {
    l match {
      case x :: xs =>
        val pxs = powerset(xs)
        pxs ::: (pxs map (x :: _))
      case Nil => List(Nil)
    }
  }

  def min(x: Int, y: Int) = if (x < y) x else y

  def max(x: Int, y: Int) = if (x > y) x else y

}

// TODO: put this in dssupport
object ListUtils {

  // zip for three lists
  def zip3[A, B, C](l1: List[A], l2: List[B], l3: List[C]): List[(A, B, C)] = {
    (l1, l2, l3) match {
      case (Nil, Nil, Nil) => Nil
      case (x :: xs, y :: ys, z :: zs) => (x, y, z) :: zip3(xs, ys, zs)
      case _ => throw new Exception("zip3: lists not of equal length")
    }
  }

  // a generalization of map: fun now returns more than one element, so the list must be flattened
  def collect[A, B](substitutions: List[A], fun: (A => List[B])): List[B] =
    (substitutions map fun).flatten

  // drops elements of l up to e and returns the rest
  def dropuntil[A](e: A, l: List[A]): List[A] = {
    l match {
      case Nil => Nil
      case x :: xs => if (e != x) dropuntil(e, xs) else xs
    }
  }

  // an insert for insertion sort
  def insertIntoSortedList[A](lt_pred: (A, A) => Boolean, v: A, l: List[A]): List[A] = {
    l match {
      case Nil => List(v)
      case x :: xs =>
        if (lt_pred(v, x))
          v :: (x :: xs)
        else
          x :: insertIntoSortedList(lt_pred, v, xs)
    }
  }

  
  def rflattenLists[A](ls: List[List[A]]): List[A] = ls.foldLeft(Nil: List[A])(_ ::: _)

  def flattenLists[A](ls: List[List[A]]): List[A] = rflattenLists(ls).reverse
  

}

class VariableGenerator(var constant_prefix: String) {
  var maxindex = 0

  def potbrak(m: Int, s: String): String = if (m < 10) "" else s

  def reset() = {maxindex = 0}

  def getFreshVariable(): VariableSymbolA = {maxindex += 1; VariableStringSymbol(constant_prefix + potbrak(maxindex, "{") + maxindex + potbrak(maxindex, "}"))}

}
*/
