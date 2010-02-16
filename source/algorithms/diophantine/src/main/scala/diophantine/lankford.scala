package at.logic.algorithms.diophantine

/* Solves diophantine equations via Lankford's Algorithm as described in
 * "Non-negative Integer Basis Algorithms for Linear Equations with Integer Coefficients",
 *  D.Lankford, J. of Automated Reasoning 5 (1989)" */


import collection.mutable.Set
import collection.mutable.HashSet

trait DiophantineSolver[Data] {
  def solve(coeff_lhs: Vector, coeff_rhs: Vector) : List[Vector]
}



class Vector(val vector : List[Int]) {
  

  def +(v:Vector) : Vector = apply(mapVectors(_+_, vector, v.vector))
  def -(v:Vector) : Vector = apply(mapVectors(_-_, vector, v.vector))

  def <(v:Vector)  : Boolean = { mapVectors(_<_,  vector,v.vector).foldLeft(true)(_&&_)  }
  def <=(v:Vector) : Boolean = { mapVectors(_<=_, vector,v.vector).foldLeft(true)(_&&_)  }
  def >(v:Vector)  : Boolean = { mapVectors(_>_,  vector,v.vector).foldLeft(true)(_&&_)  }
  def >=(v:Vector) : Boolean = { mapVectors(_>=_, vector,v.vector).foldLeft(true)(_&&_)  }

  override def equals(v:Any) : Boolean = { try { vector equals v.asInstanceOf[Vector].vector } catch { case _ => false} }
  override def toString = "Vector(" + (vector.foldRight(")") ((x:Int,y:String) => if (y==")") x.toString+y else x+","+ y))
  override def hashCode = vector.hashCode

  def anyless(v:Vector)  : Boolean = { mapVectors( _<_ ,  vector,v.unapply).foldLeft(false)(_||_)  }
  def anylesszero = { vector.map( _< 0).foldLeft(false)(_||_)  }
  def zero = apply(MathHelperFunctions.createZeroRow(vector.length))

  def length = vector.length

  def *(v:Vector) : Int = mapVectors(_*_, vector, v.vector).foldLeft(0)(_+_)
  def *(s:Int) : Vector = apply(vector.map(_*s))
  
  
  def apply(v : Int*) = new Vector(v.toList)
  def apply(v : List[Int]) = new Vector(v)
  def unapply = vector


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

  
  def reducedAgainst(y:Vector) : (Boolean, Vector) = {
    if (y.vector(0) !=  0) {
      (false,this)
    } else {
      var v_old = this
      var v_new = this -y
      var changed = false

      while (! v_new.anylesszero ) {
        v_old = v_new
        v_new = v_new - y
        changed = true
      }

      (changed, v_old)
    }
  }

  
}


object Vector {
  def apply(v : Int*) = new Vector(v.toList)
  def apply(v : List[Int]) = new Vector(v)
  def unapply(v : Vector) = v.vector
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

  def addSets(set1: Set[Vector], set2:Set[Vector]) : HashSet[Vector] = {
    val merged = new HashSet[Vector]
    for (i <- set1)
      for (j <- set2)
        merged += (i+j)

    merged
  }

  def unionSets(set1:Set[Vector], set2:Set[Vector]) : HashSet[Vector] = {
    val merged = new HashSet[Vector]
    for (i <- set1)
      merged += i

    for (j <- set2)
        merged += j

    merged
  }

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
    val a = new HashSet[Vector]
    val b = new HashSet[Vector]

    for (i<-sim._1)
      a += new Vector(i)
    for (i<-sim._2)
      b += new Vector(i)

    val positive : HashSet[Vector] = new HashSet[Vector]
    val negative : HashSet[Vector] = new HashSet[Vector]
    val zero     : HashSet[Vector] = new HashSet[Vector]
    var x        : HashSet[Vector] = new HashSet[Vector]
    var zero_new : HashSet[Vector] = null 
    var stage = 1

    positive ++= a
    negative ++= b

    while (!positive.isEmpty || !negative.isEmpty) {
      //println("=== "+stage+" ===")
      x = unionSets(addSets(a,negative), addSets(b,positive))
      //println(x)
      positive.clear
      negative.clear
      
      zero_new = new HashSet[Vector]
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

  /*
  def addVectors(x : List[Int], y : List[Int]) : List[Int] = {
    x match {
      case i::is =>
        y match {
          case j::js => (i+j) :: addVectors (is,js)
          case Nil => throw new Exception("Adding vectors of different length!")
        }
      case Nil =>
        y match {
          case _ :: _ => throw new Exception("Adding vectors of different length!")
          case Nil => Nil
      }
    }
  } */

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


class LankfordSolver[Data] {
  import MathHelperFunctions._

  def solve(lhs: List[(Int,Data)], rhs: List[(Int,Data)]) : List[List[(Int,Data)]] = {
    //val coefficients = lhs ++ rhs.map( ((x) => x match {case (x,d) => (-x,d)}) )
    val labels : List[Data] = lhs.map((x : (Int,Data)) => x._2 ) ++ rhs.map((x : (Int,Data)) => x._2 )
    //println(labels)
    val n = lhs.length + rhs.length 
    var im = createIdentityMatrix(n)
    var positive_matrix : List[List[Int]] = Nil
    var negative_matrix : List[List[Int]] = Nil

    for  (c <- lhs) {
      c match {
        case (x,data) =>
          im match {
            case head :: tail =>
              positive_matrix = (x::head) :: positive_matrix
              im = tail
            case Nil =>
          }
      }
    }

    //for ( (x,d) <- rhs)

    for  (c <- rhs) {
      c match {
        case (x,data) =>
          im match {
            case head :: tail =>
              negative_matrix = (-x::head) :: negative_matrix
              im = tail
            case Nil =>
          }
      }
    }
    

    var positive_new : List[List[Int]] = Nil
    var negative_new : List[List[Int]] = Nil
    var bases : List[List[Int]] = Nil

    for (pos <- positive_matrix)
      for (neg <- negative_matrix) {
        val v = addVectors(pos,neg)
        if (v(0) < 0) {
          negative_new = v :: negative_new
        } else if (v(0)>0) {
          positive_new = v :: positive_new
        } else {
          bases = v :: bases
        }
      }

    var positive_old : List[List[Int]] = Nil
    var negative_old : List[List[Int]] = Nil


    do {
      /*
      println("positive")
      println(positive_matrix)
      println("negative")
      println(negative_matrix)
      */

      positive_old = positive_new
      negative_old = negative_new

      positive_new = Nil
      negative_new = Nil

      for (pos <- positive_matrix) {
        for (neg <- negative_old) {
          val v = addVectors(pos,neg)
          //println("adding "+pos+" + "+neg+ " = " + v)
          v match {
            case head :: tail =>
              if (columnsGreaterEqualZero(tail)) {
                if (head < 0) {
                  if (! (negative_matrix.contains(v) || (negative_old.contains(v))))
                    negative_new = v :: negative_new
                } else if (head >0) {
                  if (! (positive_matrix.contains(v) || (positive_old.contains(v))))
                    positive_new = v :: positive_new
                } else {
                  if (! bases.contains(v))
                    bases = v :: bases
                }
              }
            case Nil =>
              throw new Exception("working on vectors of zero length!")
          }
        }
      }

      for (neg <- negative_matrix) {
        for (pos <- positive_old) {
          val v = addVectors(pos,neg)
          //println("adding "+pos+" + "+neg+ " = " + v)
          v match {
            case head :: tail =>
              if (columnsGreaterEqualZero(tail)) {
                if (head < 0) {
                  if (! (negative_matrix.contains(v) || (negative_old.contains(v))))
                    negative_new = v :: negative_new
                } else if (head>0) {
                  if (! (positive_matrix.contains(v) || (positive_old.contains(v))))
                    positive_new = v :: positive_new
                } else {
                  if (! bases.contains(v))
                    bases = v :: bases
                }
              }
            case Nil =>
              throw new Exception("working on vectors of zero length!")
          }
        }
      }

      positive_matrix = positive_matrix ++ positive_new
      negative_matrix = negative_matrix ++ negative_new


    } while (! (positive_new.isEmpty && negative_new.isEmpty))

    val reattach_labels = ((x:List[Int])  => x.zip(labels))
    val tail = ((x:List[Int])=> x.tail)
    bases.map(tail).map(reattach_labels)

    /*
    if (sum < 0) Nil
    else coefficients match {
      //handle last element, i.e. solve c*x = sum
      case (c, data) :: Nil =>
        if (divisibleBy(sum,c))
          List(List( (sum/c, data) ))
        else
          Nil
      
      //handle every element but the last one
      case (c, data) :: rest =>
              var l : List[List[(Int,Data)]] = Nil
              var i = sum
              var x = 0

              while (i >= 0) {
                val pair = (x,data)
                l = combine(pair, solve(rest, i)) ++ l
                i -= c
                x += 1
              }

              l
      //end of list        
      case _ => Nil
    } */                      
  }

  private def combine(alternative : (Int,Data), rest : List[List[(Int,Data)]]) : List[List[(Int,Data)]] = {
    val prepend : ( (List[(Int,Data)] => List[(Int,Data)]) ) = ( (xs :List[(Int,Data)])  => alternative::xs)
    rest.map(prepend)
  }

  
}

