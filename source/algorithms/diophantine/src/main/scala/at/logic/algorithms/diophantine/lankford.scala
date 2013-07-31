package at.logic.algorithms.diophantine

/* Solves diophantine equations via Lankford's Algorithm as described in
 * "Non-negative Integer Basis Algorithms for Linear Equations with Integer Coefficients",
 *  D.Lankford, J. of Automated Reasoning 5 (1989)" */


import collection.mutable.{HashSet => MHashSet}

trait DiophantineSolver[Data] {
  def solve(coeff_lhs: Vector, coeff_rhs: Vector) : List[Vector]
}

object LankfordSolver {
  /*
  def solve(coeff_lhs: List[Int], coeff_rhs: List[Int]) : List[Vector] = {
    val solver = new LankfordSolverInstance(Vector(coeff_lhs), Vector(coeff_rhs))
    solver.solve.toList
  }*/

  def solve(coeff_lhs: Vector, coeff_rhs: Vector) : List[Vector] = {
    val solver = new LankfordSolverInstance(coeff_lhs, coeff_rhs)
    solver.solve.toList
  }
}

case class LankfordSolverInstance(val a : Vector, val b : Vector) {
  val ab = Vector(a.vector ::: (b * -1).vector)
  val alength = a.length
  val blength = b.length
  val ablength = alength + blength
  
  /* the norm is defined as theinner product - see p.30 */
  def norm(v : Vector) = ab * v

  /* follows the inductive definition on p.31 of the paper:
   * while P_k and N_k are nonempty:
   *   X_k+1 = {A+N_k} union {B+P_k}
   *   P_k+1 = {S|S in X_k+1, |S|>0, S irreducible rel. Z_k}
   *   N_k+1 = {S|S in X_k+1, |S|<0, S irreducible rel. Z_k}
   *   Z_k+1 = {S|S in X_k+1, |S|=0}
   */
  def solve = {
    val im = MathHelperFunctions.createIdentityMatrix(ablength)
    val sim = im splitAt alength
    val a = new MHashSet[Vector]
    val b = new MHashSet[Vector]

    for (i<-sim._1)
      a += new Vector(i)
    for (i<-sim._2)
      b += new Vector(i)

    val positive : MHashSet[Vector] = new MHashSet[Vector]
    val negative : MHashSet[Vector] = new MHashSet[Vector]
    val zero     : MHashSet[Vector] = new MHashSet[Vector]
    var x        : MHashSet[Vector] = new MHashSet[Vector]
    var zero_new : MHashSet[Vector] = null
    var stage = 1

    positive ++= a
    negative ++= b

    while (!positive.isEmpty || !negative.isEmpty) {
      //println("=== "+stage+" ===")
      val positive_sums = for (i <- b; j <- positive) yield { i+j }
      val negative_sums = for (i <- a; j <- negative) yield { i+j }

      x = negative_sums ++ positive_sums
      //println(x)
      positive.clear
      negative.clear
      
      zero_new = new MHashSet[Vector]
      for (s <- x) {
        val ns = norm(s)
        //println("looking at: "+s+" with norm="+ns)

        if ((ns > 0) && z_irreducible(s,zero))
          positive += s
        if ((ns < 0) && z_irreducible(s,zero))
          negative += s
        if (ns == 0)
          zero_new += s
      }


      zero ++= zero_new 
      stage += 1
    }
    //println("=== done in stage "+stage+ " "+ positive.size +" positive remaining, "+ negative.size +" negative remaining ===")

    //for (z<- zero) println("result: "+z+" with norm="+norm(z))

    zero
  }

  def reduceVector(v : Vector, zero:List[Vector]) = {
    var w = v
    var temp = v.zero
    for (i <- zero) {
      temp = w - i     
      while ( temp.anylesszero ) {
        w = w - i
        temp = w -i
      }
    }
    
    w
  }

  /* s is reducible relative to Z_k iff there exists some z in Z_k s.t.
     each coordinate of z is >= to the corresponding coordinate of s
     -- corr. typo in the paper: x should be z */
  /* addition: therefore s is irreducible relative to Z_k iff there is no
   * z in Z_k s.t. each coordinate of z is >= to the corresponding coordinate of s*/
  def z_irreducible(s:Vector, zero:Iterable[Vector]) : Boolean = {
    var r = true
    for (z<-zero)
      if (s>=z)
	      r = false
    r
  }
  
}

object MathHelperFunctions {
  def divisibleBy(x:Int, y:Int) : Boolean = x % y == 0
  def sumOfCoefficients[Data](xs:List[(Int,Data)]) : Int = {
    xs match {
      case (v, _ ) :: rest => v + sumOfCoefficients(rest)
      case _ => 0
    }
  }


  def mergeCoefficientsWithSolutions[Data](cs : List[(Int,Data)], xs : List[(Int,Data)]) : List[(Int,Int,Data)] = {
    cs match {
      case (c, cdata) :: crest =>
        xs match {
          case (x,xdata) :: xrest =>
              if (cdata != xdata) throw new Exception("Could not merge coefficient and solution list, wrong order!")
              (c,x,xdata) :: mergeCoefficientsWithSolutions(crest,xrest)
          case _ =>
            throw new Exception("Could not merge coefficient and solution list, lists not of equal size!")  
        }
      case _ =>
        xs match {
          case Nil => Nil
          case _ =>
            throw new Exception("Could not merge coefficient and solution list, lists not of equal size!")          
        }
    }
    
  }

  def sumOfSolvedEquation[Data](xs:List[(Int,Int,Data)]) : Int = {
    xs match {
      case (c,v, _ ) :: rest => c*v + sumOfSolvedEquation(rest)
      case _ => 0
    }
  }


  def createZeroRow(n:Int) : List[Int] = {
    if (n<=0) {
      Nil
    } else {
      0 :: createZeroRow(n-1)
    }
  }

  def createIdentityRow(i:Int,n:Int) : List[Int] = {
    if (n<=0) {
      Nil
    } else {
      if (i==0)
        1 :: createIdentityRow (i-1,n-1)
      else
        0 :: createIdentityRow (i-1,n-1)
    }
  }

  def createIdentityMatrix(n:Int) : List[List[Int]] = {
    if (n<= 0) {
      Nil
    }
    else {
      var l : List[List[Int]] = Nil
      for (i <- 0 to n-1)
          l = createIdentityRow (n-1-i,n) :: l
      return l
    }
  }

  def addVectors(l1:List[Int],l2:List[Int]) = mapVectors((x,y)=>x+y, l1,l2)
  def subVectors(l1:List[Int],l2:List[Int]) = mapVectors((x,y)=>x-y, l1,l2)

  def mapVectors[A](fun: ((Int,Int)=>A), x : List[Int], y : List[Int]) : List[A] = {
    x match {
      case i::is =>
        y match {
          case j::js => fun(i,j) :: mapVectors (fun,is,js)
          case Nil => throw new Exception("Mapping vectors of different length!")
        }
      case Nil =>
        y match {
          case _ :: _ => throw new Exception("Mapping vectors of different length!")
          case Nil => Nil
      }
    }
  }

  def columnsGreaterZero(v : List[Int]) : Boolean = {
    for (i <- v) {
      if (i <= 0)
        false
    }

    true
  }

  def columnsGreaterEqualZero(v : List[Int]) : Boolean = {
    for (i <- v) {
      if (i < 0)
        false
    }

    true
  }

}
