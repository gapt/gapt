/*
 * Simple functions that operate on lambda-expressions
 *
 */

package at.logic.gapt.expr

import at.logic.gapt.expr.{ SymbolA, getRenaming }
import at.logic.gapt.proofs.lk.{Axiom, BinaryLKProof, UnaryLKProof}
import at.logic.gapt.proofs.lk.base.{Sequent, FSequent, LKProof}

// Returns a list *without duplicates* of the free variables in the expression.
// There is no guarantee on the ordering of the list.
object freeVariables {
  def apply( e: LambdaExpression ): List[Var] = getFreeVariables( e, List() ).distinct
  def apply( e: FOLExpression ): List[FOLVar] =
    apply( e.asInstanceOf[LambdaExpression] ).asInstanceOf[List[FOLVar]]
  def apply( es: List[FOLExpression] ): List[FOLVar] = es.flatMap( apply( _ ) )

  private def getFreeVariables( e: LambdaExpression, bound: List[Var] ): List[Var] = e match {
    case v: Var =>
      if ( !bound.contains( v ) ) List( v )
      else List()
    case Const( _, _ )   => List()
    case App( exp, arg ) => getFreeVariables( exp, bound ) ++ getFreeVariables( arg, bound )
    case Abs( v, exp )   => getFreeVariables( exp, v :: bound )
  }
}

// Returns a list *with duplicates* of the bound variables in the expression.
// There is no guarantee on the ordering of the list.
object boundVariables {
  def apply( e: LambdaExpression ): List[Var] = e match {
    case Var( _, _ )     => List()
    case Const( _, _ )   => List()
    case App( exp, arg ) => boundVariables( exp ) ++ boundVariables( arg )
    case Abs( v, exp )   => v :: boundVariables( exp )
  }
}

// get a new variable/constant (similar to the current and) different from all 
// variables/constants in the blackList, returns this variable if this variable 
// is not in the blackList
object rename {
  def apply( v: Var, blackList: List[Var] ): Var = Var( getRenaming( v.sym, blackList.map( v => v.sym ) ), v.exptype )
  def apply( v: FOLVar, blackList: List[Var] ): FOLVar =
    apply( v.asInstanceOf[Var], blackList ).asInstanceOf[FOLVar]
  def apply( a: SymbolA, blackList: List[SymbolA] ): SymbolA = getRenaming( a, blackList )
  def apply( c: Const, blackList: List[Const] ): Const = Const( getRenaming( c.sym, blackList.map( c => c.sym ) ), c.exptype )

  // renames a list of variables to pairwise distinct variables
  // while avoiding names from blackList.
  def apply( vs: Set[FOLVar], blackList: Set[FOLVar] ): Map[FOLVar, FOLVar] = {
    val v_list = vs.toList
    ( v_list zip
      v_list.foldLeft( Nil: List[FOLVar] )(
        ( res, v ) => res :+ apply( v, ( blackList ++ res ).toList ) ) ).toMap
  }
}

/** Models the signature of an expression
 *
 * @param bVars Set of bound variables
 * @param fVars Set of free variables
 * @param consts Set of constants
 */
class Signature(val bVars: Set[Var], val fVars: Set[Var], val consts: Set[Const]) {

  /** Creates a signature from lists by converting to sets
   *
   * @param bv List of bound variables
   * @param fv List of free variables
   * @param c List of constants
   * @return
   */
  def this(bv: List[Var], fv: List[Var], c: List[Const]) = this(bv.toSet, fv.toSet, c.toSet)

  /** Computes the union of two signatures
   *
   * @param that Another signature
   * @return
   */
  def union(that: Signature) = new Signature(this.bVars union that.bVars, this.fVars union that.fVars, this.consts union that.consts)

  /** Computes the intersection of two signatures
   *
   * @param that Another signature
   * @return
   */
  def intersect(that: Signature) = new Signature(this.bVars intersect that.bVars, this.fVars intersect that.fVars, this.consts intersect that.consts)

  /** Adds a variable to the set of bound variables and removes it from free variables
   *
   * @param v A variable
   * @return
   */
  def bind(v: Var): Signature = new Signature(bVars + v, fVars - v, consts)

  /** Adds a variable ot the set of free variables and removes it from bound variables
   *
   * @param v A variable
   * @return
   */
  def unbind(v: Var): Signature = new Signature(bVars - v, fVars + v, consts)

  /** Prints the signature
   *
   */
  def display : Unit = {
    println("Bound variables:")
    bVars foreach {
      v => println("\t" + v.name + ": " + v.exptype.toString)
    }

    println("Free variables:")
    fVars foreach {
      v => println("\t" + v.name + ": " + v.exptype.toString)
    }

    println("Constants:")
    consts foreach {
      c => println("\t" + c.name  + ": " + c.exptype.toString)
    }
  }

  /** Converts the signature to a tuple
   *
   * @return The tuple (bVars, fVars, consts)
   */
  def toTuple: (Set[Var], Set[Var], Set[Const]) = (bVars, fVars, consts)

  override def equals(that: Any): Boolean = that match {
    case Signature(bv, fv, c) =>
      bVars == bv && fVars == fv && consts == c
    case _ => false
  }

  override def hashCode: Int = (((41 + bVars.hashCode) * 41) + fVars.hashCode * 41) + consts.hashCode

}

object Signature {

  /** Computes the signature of a lambda expression
   *
   * @param e A lambda expression
   * @return The signature of e
   */
  def apply(e: LambdaExpression): Signature = e match {
    case v: Var => new Signature(Nil, List(v), Nil)
    case c: LogicalConstant => new Signature(Nil, Nil, Nil)
    case c: Const => new Signature(Nil, Nil, List(c))
    case App(exp, arg) =>
      Signature(exp) union Signature(arg)
    case Abs(v, exp) =>
      Signature(exp).bind(v)
  }

  /** Computes the signature of an FSequent
   *
   * @param s An FSequent
   * @return The signature of s
   */
  def apply(s: FSequent): Signature = apply(s.toFormula)

  /** Computes the signature of a Sequent
   *
   * @param s A sequent
   * @return The signature of s
   */
  def apply(s: Sequent): Signature = apply(s.toFormula)

  /** Computes the signature of an LKProof
   *
   * @param p An LKProof
   * @return The signature of p
   */
  def apply(p: LKProof): Signature = p match {
    case Axiom(seq) => Signature(seq)

    case UnaryLKProof(_, u1, seq, _, _) =>
      Signature(seq) union Signature(u1)

    case BinaryLKProof(_, u1, u2, seq, _, _, _) =>
      Signature(seq) union Signature(u1) union Signature(u2)
  }

  def unapply(s: Any): Option[(Set[Var], Set[Var], Set[Const])] = s match {
    case sig: Signature => Some(sig.bVars, sig.fVars, sig.consts)
    case _ => None
  }
}

