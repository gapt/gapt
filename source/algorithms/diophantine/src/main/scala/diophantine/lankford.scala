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

  def createIdentityMatrix(n:Int) : List[List[Int]] = {
    if (n<= 0) {
      Nil
    }
    else {
      Nil
    }
    
    
  }

}

class LankfordSolver[Data] extends DiophantineSolver[Data] {
  import MathHelperFunctions._

  def solve(coefficients: List[(Int,Data)], sum : Int) : List[List[(Int,Data)]] = {
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
    }                       
  }

  private def combine(alternative : (Int,Data), rest : List[List[(Int,Data)]]) : List[List[(Int,Data)]] = {
    val prepend : ( (List[(Int,Data)] => List[(Int,Data)]) ) = ( (xs :List[(Int,Data)])  => alternative::xs)
    rest.map(prepend)
  }

  
}

