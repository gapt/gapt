package diophantine

import _root_.at.logic.algorithms.diophantine.{Vector, LankfordSolver, DiophantineSolver}
import _root_.at.logic.language.hol.logicSymbols.ConstantSymbolA
import _root_.at.logic.language.lambda.symbols.{VariableStringSymbol, StringSymbol}
import _root_.at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.language.fol._
import substitutions.Substitution
import collection.Map
import collection.mutable.HashMap
import collection.immutable.HashSet

object ACUnification {
  type TermCount = (FOLTerm,Int)
  type ListEntry = (Int, Vector, List[Vector])
  type MapEntry = (Int, List[Vector])
  type ArrayEntry = (Vector, MapEntry)

  var constant_prefix = "z_"
  var maxindex = 1

  def getFreshVariable() = { maxindex += 1; VariableStringSymbol(constant_prefix+maxindex) }
  

  def unify(function: ConstantSymbolA, term1 : FOLTerm, term2 : FOLTerm) : Option[Substitution] = {
    val counted_symbols = countSymbols(nestedFunctions_toList(function,term1), nestedFunctions_toList(function,term2))
    val (ts1,count1) = List unzip counted_symbols 

    val (lhs,rhs) = (counted_symbols partition (_._2 >0)) // this works because countSymbols olny returns values != 0
    val vlhs = Vector(lhs map (_._2))
    val vrhs = Vector(rhs map (_._2 * -1))

    val vlhs_length = vlhs.length
    val vrhs_length = vrhs.length

    if ((lhs == Nil) || (rhs == Nil)) {
      None
    }
    else {
      val s = Substitution()
      //println(" "+vlhs + " "+vrhs)
      val basis = LankfordSolver solve (vlhs,vrhs)
      //println("Basis: " + basis)
      
      val sums = new HashMap[Vector,List[(Int, List[Vector])]]
      var oldnewest : List[(Int, Vector,List[Vector])] = Nil
      var newest : List[(Int, Vector, List[Vector])] = Nil

      for (b<-basis) {
        val weight = vector_weight(vlhs,b)
        sums(b) = List((weight,List(b)))
        newest = (weight,b,List(b)) :: newest
      }

      val maxweight = calculateMaxWeight(vlhs,vrhs)
      //println(maxweight)
      
      while (newest.size > 0) {
        oldnewest = newest
        newest = Nil
        
        for (v <- oldnewest) {
          val candidates = basis map (x => (vector_weight(vlhs,x) + v._1 , x + v._2, x :: v._3  ))

          for (candidate <- candidates) {
            val (weight,sum,vectors) = candidate
            val entry : (Int, List[Vector]) = (weight, vectors sort Vector.lex_<)
            val newest_entry : (Int, Vector, List[Vector]) = (weight, sum, entry._2)


            if (sums.contains(sum)) {
              val l : List[(Int,List[Vector])] = sums(sum)
              if (! l.contains(entry))
                sums(sum) = entry :: l
            } else {
              sums(sum) = List(entry)
              if (weight < maxweight && sum.anyeqzero)
                newest = newest_entry :: newest
            }
          }
        }
      }

/*            val atransform : ArrayEntry => (Vector, List[Vector]) = (_._1, _._2._2)
            val afilter : (Vector, List[Vector]) = _._1.allgreaterzero
            */

      def gzero(v : Vector) : Boolean = v.allgreaterzero

      var results : List[Vector] = Nil
      for (v <- sums.toList ) {
        if (gzero(v._1))
          results = v._1 ::results
      }
      /**/

      //results = sums.keySet.toList //AC1 Unification does not filter out

      var temp = results sort Vector.lex_<
      results = Nil
      while (temp != Nil) {
        temp match {
          case x::xs =>
            results = x :: results
            temp = xs filter (y=> !(y>=x))
          case Nil =>
            throw new Exception("Error in AC Unification algorithm: list is empty even if it may not be")
        }
      }

      

      

      /*
      for(i<-results)
        //println(i+ " ::: "+sums(i))
        println(i)
      
      println(results.size)
            */

      Some(s)
    }
  }

  def composable_by(v:Vector, vs:List[Vector]) : Boolean = {
    vs match {
      case Nil => false
      case _ =>
        val reduced = (vs map (_ - v))
        if (reduced contains v.zero)
          true
        else {
          def gzero(v:Vector) = v.allgreaterzero
          composable_by(v, reduced filter gzero)
        }
    }

  }

  def vector_weight(vlhs:Vector, v:Vector ) : Int = vlhs * Vector(v.vector slice(0, vlhs.length))

  def calculateMaxWeight(l : Vector, r : Vector) : Int = {
    /*
    def check(f:(Int,Int) => Boolean, xs:List[Int]) = {
      var min = xs(0);
      for (x<-xs)
        if (f(x,min)) min = x;
      min;
    }*/

    def product(l:List[Int]) = l.foldLeft (1) (_*_)

    def min(x:Int,y:Int) = if (x<y) x else y
    def max(x:Int,y:Int) = if (x>y) x else y

    
    return max(l.length,r.length) * max(lcm(l.vector),lcm(r.vector))
    
    
  }

  def gcd(x :Int, y:Int) = {
    //Euclidian Algorithm
    var m = if (x<y) x else y
    var n = if (x<y) y else x
    var temp = 0
    while (n != 0) {
      temp = m % n
      m = n
      n = temp
    }
    m
  }

  def lcm(x:Int,y:Int) = x*y/gcd(x,y)
  def lcm(xs : List[Int]) = xs.reduceLeft((x,y)=>x*y/gcd(x,y))
  
  
  def insertIntoSortedList[A](lt_pred: (A,A) => Boolean, v:A,l:List[A] ) : List[A] = {
    l match {
      case Nil => List(v)
      case x :: xs =>
        if (lt_pred(v,x))
          v :: (x :: xs)
        else
          x :: insertIntoSortedList(lt_pred, v,xs)
    }
  }

  def nestedFunctions_toList(function: ConstantSymbolA, term : FOLTerm) : List[FOLTerm] = {
    term match {
      case v : FOLVar => List(v)
      //case c : FOLConst => List(c)
      case Function(name,args) =>
        if (name == function) {
          val join = ((x:List[FOLTerm], y:List[FOLTerm]) => x ++ y)
          args.map(nestedFunctions_toList(function,_)) reduceLeft join
        } else {
          List(Function(name,args))
        }
      case _ =>
        Nil
    }
  }

  def countSymbols(terms1:List[FOLTerm], terms2 : List[FOLTerm]) : List[TermCount] = {
    var result : List[TermCount] = Nil
    for(t <- terms1) {
      result = insertTerm(t,result)
    }
    for(t <- terms2) {
      result = removeTerm(t,result)
    }
    result filter (_._2 != 0)
  }

  def insertTerm(term: FOLTerm, list : List[TermCount]) : List[TermCount]= {
    list match {
      case Nil => List((term,1))
      case (lterm,count) :: rest =>
        if (term == lterm)
          (lterm,count+1) :: rest
        else
          (lterm,count) :: insertTerm(term,rest)
    }
  }

  def removeTerm(term: FOLTerm, list : List[TermCount]) : List[TermCount]= {
    list match {
      case Nil => List((term,-1))
      case (lterm,count) :: rest =>
        if (term == lterm)
          (lterm,count-1) :: rest
        else
          (lterm,count) :: removeTerm(term,rest)
    }
  }

  
}