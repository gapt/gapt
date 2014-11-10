package at.logic.algorithms.diophantine

/* A vector implementation with addition, scalar product etc. */
object Vector {
  def apply(v: Int*) = new Vector(v.toList)

  def apply(v: List[Int]) = new Vector(v)

  def unapply(v: Vector) = v.vector

  def lex_<(v1: Vector, v2: Vector): Boolean = {
    if (v1.length != v2.length) throw new Exception("Comparing vectors of different length!")

    if (v1.length == 0) return true
    if (v1.vector(0) < v2.vector(0)) return true
    if (v1.vector(0) == v2.vector(0))
      return Vector(v1.vector.tail) lex_< Vector(v2.vector.tail)
    return false
  }

  def sum_<(v1: Vector, v2: Vector): Boolean = {
    v1.vector.foldLeft(0)(_ + _) < v2.vector.foldLeft(0)(_ + _)
  }

  def vectorSum(l:List[Vector], zero:Vector) : Vector = l.foldLeft(zero)(_+_)

  def gzero(v : Vector) : Boolean = v.allgreaterzero

  def geqzero(v : Vector) : Boolean = v.allgreatereqzero
}

class Vector(val vector: List[Int]) {
  def +(v: Vector): Vector = apply(mapVectors(_ + _, vector, v.vector))

  def -(v: Vector): Vector = apply(mapVectors(_ - _, vector, v.vector))

  def <(v: Vector): Boolean = {mapVectors(_ < _, vector, v.vector).foldLeft(true)(_ && _)}

  def <=(v: Vector): Boolean = {mapVectors(_ <= _, vector, v.vector).foldLeft(true)(_ && _)}

  def >(v: Vector): Boolean = {mapVectors(_ > _, vector, v.vector).foldLeft(true)(_ && _)}

  def >=(v: Vector): Boolean = {mapVectors(_ >= _, vector, v.vector).foldLeft(true)(_ && _)}


  def lex_<(v: Vector): Boolean = Vector.lex_<(this, v)

  override def equals(v: Any): Boolean = {try {vector equals v.asInstanceOf[Vector].vector} catch {case _: Throwable => false}}

  override def toString = "Vector(" + (vector.foldRight(")")((x: Int, y: String) => if (y == ")") x.toString + y else x + "," + y))

  override def hashCode = vector.hashCode

  def anyless(v: Vector): Boolean = {mapVectors(_ < _, vector, v.unapply).foldLeft(false)(_ || _)}

  def anylesszero = {vector.map(_ < 0).foldLeft(false)(_ || _)}

  def anylesseqzero = {vector.map(_ <= 0).foldLeft(false)(_ || _)}

  def anyeqzero = {vector.map(_ == 0).foldLeft(false)(_ || _)}

  def allgreaterzero = !anylesseqzero

  def allgreatereqzero = !anylesszero

  def zero = apply(MathHelperFunctions.createZeroRow(vector.length))

  def length = vector.length

  def *(v: Vector): Int = mapVectors(_ * _, vector, v.vector).foldLeft(0)(_ + _)

  def *(s: Int): Vector = apply(vector.map(_ * s))


  def apply(v: Int*) = new Vector(v.toList)

  def apply(v: List[Int]) = new Vector(v)

  def unapply = vector


  def mapVectors[A](fun: ((Int, Int) => A), x: List[Int], y: List[Int]): List[A] = {
    x match {
      case i :: is =>
        y match {
          case j :: js => fun(i, j) :: mapVectors(fun, is, js)
          case Nil => throw new Exception("Mapping vectors of different length!")
        }
      case Nil =>
        y match {
          case _ :: _ => throw new Exception("Mapping vectors of different length!")
          case Nil => Nil
        }
    }
  }


  def reducedAgainst(y: Vector): (Boolean, Vector) = {
    if (y.vector(0) != 0) {
      (false, this)
    } else {
      var v_old = this
      var v_new = this - y
      var changed = false

      while (!v_new.anylesszero) {
        v_old = v_new
        v_new = v_new - y
        changed = true
      }

      (changed, v_old)
    }
  }
}


