package at.logic.algorithms.diophantine

trait DiophantineSolver[Data] {
  def solve(coefficients: List[(Int,Data)]) : List[(Int,Data)] = Nil
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

class LankfordSolver[Data] extends DiophantineSolver[Data] {
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
          println("adding "+pos+" + "+neg+ " = " + v)
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
          println("adding "+pos+" + "+neg+ " = " + v)
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

