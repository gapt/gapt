package at.logic.gapt.expr.hol.unification

/* Solves diophantine equations via Lankford's Algorithm as described in
 * "Non-negative Integer Basis Algorithms for Linear Equations with Integer Coefficients",
 *  D.Lankford, J. of Automated Reasoning 5 (1989)" */

import at.logic.gapt.expr.hol.unification

import scala.collection.mutable.{ HashSet => MHashSet }

trait DiophantineSolver[Data] {
  def solve( coeff_lhs: at.logic.gapt.expr.hol.unification.Vector, coeff_rhs: at.logic.gapt.expr.hol.unification.Vector ): List[at.logic.gapt.expr.hol.unification.Vector]
}

object LankfordSolver {
  /*
  def solve(coeff_lhs: List[Int], coeff_rhs: List[Int]) : List[Vector] = {
    val solver = new LankfordSolverInstance(Vector(coeff_lhs), Vector(coeff_rhs))
    solver.solve.toList
  }*/

  def solve( coeff_lhs: at.logic.gapt.expr.hol.unification.Vector, coeff_rhs: at.logic.gapt.expr.hol.unification.Vector ): List[at.logic.gapt.expr.hol.unification.Vector] = {
    val solver = new LankfordSolverInstance( coeff_lhs, coeff_rhs )
    solver.solve.toList
  }
}

case class LankfordSolverInstance( val a: at.logic.gapt.expr.hol.unification.Vector, val b: at.logic.gapt.expr.hol.unification.Vector ) {
  val ab = unification.Vector( a.vector ::: ( b * -1 ).vector )
  val alength = a.length
  val blength = b.length
  val ablength = alength + blength

  /* the norm is defined as theinner product - see p.30 */
  def norm( v: at.logic.gapt.expr.hol.unification.Vector ) = ab * v

  /* follows the inductive definition on p.31 of the paper:
   * while P_k and N_k are nonempty:
   *   X_k+1 = {A+N_k} union {B+P_k}
   *   P_k+1 = {S|S in X_k+1, |S|>0, S irreducible rel. Z_k}
   *   N_k+1 = {S|S in X_k+1, |S|<0, S irreducible rel. Z_k}
   *   Z_k+1 = {S|S in X_k+1, |S|=0}
   */
  def solve = {
    val im = MathHelperFunctions.createIdentityMatrix( ablength )
    val sim = im splitAt alength
    val a = new MHashSet[at.logic.gapt.expr.hol.unification.Vector]
    val b = new MHashSet[at.logic.gapt.expr.hol.unification.Vector]

    for ( i <- sim._1 )
      a += new at.logic.gapt.expr.hol.unification.Vector( i )
    for ( i <- sim._2 )
      b += new at.logic.gapt.expr.hol.unification.Vector( i )

    val positive: MHashSet[at.logic.gapt.expr.hol.unification.Vector] = new MHashSet[at.logic.gapt.expr.hol.unification.Vector]
    val negative: MHashSet[at.logic.gapt.expr.hol.unification.Vector] = new MHashSet[at.logic.gapt.expr.hol.unification.Vector]
    val zero: MHashSet[at.logic.gapt.expr.hol.unification.Vector] = new MHashSet[at.logic.gapt.expr.hol.unification.Vector]
    var x: MHashSet[at.logic.gapt.expr.hol.unification.Vector] = new MHashSet[at.logic.gapt.expr.hol.unification.Vector]
    var zero_new: MHashSet[at.logic.gapt.expr.hol.unification.Vector] = null
    var stage = 1

    positive ++= a
    negative ++= b

    while ( !positive.isEmpty || !negative.isEmpty ) {
      //println("=== "+stage+" ===")
      val positive_sums = for ( i <- b; j <- positive ) yield { i + j }
      val negative_sums = for ( i <- a; j <- negative ) yield { i + j }

      x = negative_sums ++ positive_sums
      //println(x)
      positive.clear
      negative.clear

      zero_new = new MHashSet[at.logic.gapt.expr.hol.unification.Vector]
      for ( s <- x ) {
        val ns = norm( s )
        //println("looking at: "+s+" with norm="+ns)

        if ( ( ns > 0 ) && z_irreducible( s, zero ) )
          positive += s
        if ( ( ns < 0 ) && z_irreducible( s, zero ) )
          negative += s
        if ( ns == 0 )
          zero_new += s
      }

      zero ++= zero_new
      stage += 1
    }
    //println("=== done in stage "+stage+ " "+ positive.size +" positive remaining, "+ negative.size +" negative remaining ===")

    //for (z<- zero) println("result: "+z+" with norm="+norm(z))

    zero
  }

  def reduceVector( v: at.logic.gapt.expr.hol.unification.Vector, zero: List[at.logic.gapt.expr.hol.unification.Vector] ) = {
    var w = v
    var temp = v.zero
    for ( i <- zero ) {
      temp = w - i
      while ( temp.anylesszero ) {
        w = w - i
        temp = w - i
      }
    }

    w
  }

  /* s is reducible relative to Z_k iff there exists some z in Z_k s.t.
     each coordinate of z is >= to the corresponding coordinate of s
     -- corr. typo in the paper: x should be z */
  /* addition: therefore s is irreducible relative to Z_k iff there is no
   * z in Z_k s.t. each coordinate of z is >= to the corresponding coordinate of s*/
  def z_irreducible( s: at.logic.gapt.expr.hol.unification.Vector, zero: Iterable[at.logic.gapt.expr.hol.unification.Vector] ): Boolean = {
    var r = true
    for ( z <- zero )
      if ( s >= z )
        r = false
    r
  }

}

object MathHelperFunctions {
  def divisibleBy( x: Int, y: Int ): Boolean = x % y == 0
  def sumOfCoefficients[Data]( xs: List[( Int, Data )] ): Int = {
    xs match {
      case ( v, _ ) :: rest => v + sumOfCoefficients( rest )
      case _                => 0
    }
  }

  def mergeCoefficientsWithSolutions[Data]( cs: List[( Int, Data )], xs: List[( Int, Data )] ): List[( Int, Int, Data )] = {
    cs match {
      case ( c, cdata ) :: crest =>
        xs match {
          case ( x, xdata ) :: xrest =>
            if ( cdata != xdata ) throw new Exception( "Could not merge coefficient and solution list, wrong order!" )
            ( c, x, xdata ) :: mergeCoefficientsWithSolutions( crest, xrest )
          case _ =>
            throw new Exception( "Could not merge coefficient and solution list, lists not of equal size!" )
        }
      case _ =>
        xs match {
          case Nil => Nil
          case _ =>
            throw new Exception( "Could not merge coefficient and solution list, lists not of equal size!" )
        }
    }

  }

  def sumOfSolvedEquation[Data]( xs: List[( Int, Int, Data )] ): Int = {
    xs match {
      case ( c, v, _ ) :: rest => c * v + sumOfSolvedEquation( rest )
      case _                   => 0
    }
  }

  def createZeroRow( n: Int ): List[Int] = {
    if ( n <= 0 ) {
      Nil
    } else {
      0 :: createZeroRow( n - 1 )
    }
  }

  def createIdentityRow( i: Int, n: Int ): List[Int] = {
    if ( n <= 0 ) {
      Nil
    } else {
      if ( i == 0 )
        1 :: createIdentityRow( i - 1, n - 1 )
      else
        0 :: createIdentityRow( i - 1, n - 1 )
    }
  }

  def createIdentityMatrix( n: Int ): List[List[Int]] = {
    if ( n <= 0 ) {
      Nil
    } else {
      var l: List[List[Int]] = Nil
      for ( i <- 0 to n - 1 )
        l = createIdentityRow( n - 1 - i, n ) :: l
      return l
    }
  }

  def addVectors( l1: List[Int], l2: List[Int] ) = mapVectors( ( x, y ) => x + y, l1, l2 )
  def subVectors( l1: List[Int], l2: List[Int] ) = mapVectors( ( x, y ) => x - y, l1, l2 )

  def mapVectors[A]( fun: ( ( Int, Int ) => A ), x: List[Int], y: List[Int] ): List[A] = {
    x match {
      case i :: is =>
        y match {
          case j :: js => fun( i, j ) :: mapVectors( fun, is, js )
          case Nil     => throw new Exception( "Mapping vectors of different length!" )
        }
      case Nil =>
        y match {
          case _ :: _ => throw new Exception( "Mapping vectors of different length!" )
          case Nil    => Nil
        }
    }
  }

  def columnsGreaterZero( v: List[Int] ): Boolean = {
    for ( i <- v ) {
      if ( i <= 0 )
        false
    }

    true
  }

  def columnsGreaterEqualZero( v: List[Int] ): Boolean = {
    for ( i <- v ) {
      if ( i < 0 )
        false
    }

    true
  }

}
