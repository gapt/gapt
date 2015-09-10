/*
 * Utility functions for the lambda calculus.
 */

package at.logic.gapt.expr

import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lk.{ Axiom, BinaryLKProof, UnaryLKProof }
import at.logic.gapt.proofs.lk.base._

import scala.collection.GenTraversable
import scala.collection.mutable

/**
 * Matches constants and variables, but nothing else.
 */
object VarOrConst {
  def unapply( e: LambdaExpression ): Option[( String, TA )] = e match {
    case Var( name, et )   => Some( ( name, et ) )
    case Const( name, et ) => Some( ( name, et ) )
    case _                 => None
  }
}

/**
 * A lambda term is in variable-normal form (VNF) if different binders bind
 * different variables.
 */
object isInVNF {
  def apply( e: LambdaExpression ): Boolean = apply_( e )._1

  private def apply_( e: LambdaExpression ): ( Boolean, Set[Var] ) = e match {
    case Var( _, _ )   => ( true, Set() )
    case Const( _, _ ) => ( true, Set() )
    case App( exp, arg ) => {
      val ih_exp = apply_( exp )
      val ih_arg = apply_( arg )

      val ok = ih_exp._1 && ih_arg._1 && ( ( ih_exp._2 intersect ih_arg._2 ) == Set() )
      val vars = ih_exp._2 union ih_arg._2

      ( ok, vars )
    }
    case Abs( v, exp ) => {
      val ih = apply_( exp )

      val ok = ih._1 && !ih._2.contains( v )
      val vars = ih._2 + v

      ( ok, vars )
    }
  }
}

/**
 * Transforms an expression into an alpha-equivalent expression in
 * variable-normal form, where no two binders bind the same variable.
 */
object toVNF {
  def apply( e: LambdaExpression ): LambdaExpression = {
    val seen = mutable.Set[Var]()

    def makeDistinct( e: LambdaExpression ): LambdaExpression = e match {
      case Var( _ )    => e
      case Const( _ )  => e
      case App( a, b ) => App( makeDistinct( a ), makeDistinct( b ) )
      case Abs( v, a ) if seen contains v =>
        val newVar = rename( v, seen toList )
        makeDistinct( Abs( newVar, Substitution( v -> newVar )( a ) ) )
      case Abs( v, a ) if !( seen contains v ) =>
        seen += v
        Abs( v, makeDistinct( a ) )
    }

    makeDistinct( e )
  }
}

/**
 * Returns the set of all variables occurring in the given argument (including
 * vacuously bound variables).
 */
object variables {
  def apply( e: LambdaExpression ): Set[Var] = e match {
    case v: Var      => Set( v )
    case c: Const    => Set()
    case App( s, t ) => apply( s ) ++ apply( t )
    case Abs( v, t ) => apply( v ) ++ apply( t )
  }

  def apply( t: FOLTerm ): Set[FOLVar] = apply( t.asInstanceOf[LambdaExpression] ).asInstanceOf[Set[FOLVar]]
  def apply( s: HOLSequent ): Set[Var] = ( s.antecedent ++ s.succedent ).foldLeft( Set[Var]() )( ( x, y ) => x ++ apply( y ) )
  def apply( s: OccSequent )( implicit dummy: DummyImplicit ): Set[Var] = apply( s.toHOLSequent )
  def apply( p: LKProof ): Set[Var] = p.fold( apply )( _ ++ apply( _ ) )( _ ++ _ ++ apply( _ ) )
}

/**
 * Returns the set of free variables in the given argument.
 */
object freeVariables {
  def apply( e: LambdaExpression ): Set[Var] = apply_( e, Set() )

  def apply( e: FOLExpression ): Set[FOLVar] = apply( e.asInstanceOf[LambdaExpression] ).asInstanceOf[Set[FOLVar]]

  def apply( es: GenTraversable[LambdaExpression] ): Set[Var] = ( Set.empty[Var] /: es ) { ( acc, e ) => acc union apply( e ) }

  def apply( es: GenTraversable[FOLExpression] )( implicit dummyImplicit: DummyImplicit ): Set[FOLVar] = ( Set.empty[FOLVar] /: es ) { ( acc, e ) => acc union apply( e ) }

  def apply( seq: HOLSequent ): Set[Var] = apply( seq.antecedent ++ seq.succedent )

  def apply( seq: Sequent[FOLFormula] )( implicit dummyImplicit: DummyImplicit ): Set[FOLVar] = apply( seq.elements )

  private def apply_( e: LambdaExpression, boundvars: Set[Var] ): Set[Var] = e match {
    case v: Var          => if ( !boundvars.contains( v ) ) Set( v ) else Set()
    case Const( _, _ )   => Set()
    case App( exp, arg ) => apply_( exp, boundvars ) ++ apply_( arg, boundvars )
    case Abs( v, exp )   => apply_( exp, boundvars + v )
  }
}

/**
 * Returns the set of non-logical constants occuring in the given argument.
 */
object constants {
  def apply( e: LambdaExpression ): Set[Const] = e match {
    case _: Var             => Set()
    case _: LogicalConstant => Set()
    case c: Const           => Set( c )
    case App( exp, arg )    => constants( exp ) union constants( arg )
    case Abs( v, exp )      => constants( exp )
  }

  def apply( es: GenTraversable[LambdaExpression] ): Set[Const] = ( Set.empty[Const] /: es ) { ( acc, e ) => acc union apply( e ) }

  def apply( s: HOLSequent ): Set[Const] = ( s.antecedent ++ s.succedent ).foldLeft( Set[Const]() )( ( x, y ) => x ++ apply( y ) )
  def apply( s: OccSequent )( implicit dummy: DummyImplicit ): Set[Const] = apply( s.toHOLSequent )
  def apply( p: LKProof ): Set[Const] = p.fold( apply )( _ ++ apply( _ ) )( _ ++ _ ++ apply( _ ) )
}

/**
 * Returns the set of all subterms of the given lambda term.
 */
object subTerms {
  def apply( e: LambdaExpression ): Set[LambdaExpression] = e match {
    case Var( _, _ ) | Const( _, _ ) => Set( e )
    case Abs( _, e0 )                => apply( e0 ) + e
    case App( e1, e2 )               => ( apply( e1 ) ++ apply( e2 ) ) + e
  }
}

object expressionSize {
  def apply( e: LambdaExpression ): Int = e match {
    case Var( _ ) | Const( _ ) => 1
    case Abs( _, f )           => 1 + expressionSize( f )
    case App( a, b )           => 1 + expressionSize( a ) + expressionSize( b )
  }
}

/**
 * get a new variable/constant (similar to the current and) different from all
 * variables/constants in the blackList, returns this variable if this variable
 * is not in the blackList.
 */
object rename {
  def apply( v: Var, blackList: List[Var] ): Var = Var( getRenaming( v.sym, blackList.map( v => v.sym ) ), v.exptype )
  def apply( v: FOLVar, blackList: List[Var] ): FOLVar =
    apply( v.asInstanceOf[Var], blackList ).asInstanceOf[FOLVar]
  def apply( a: SymbolA, blackList: List[SymbolA] ): SymbolA = getRenaming( a, blackList )
  def apply( c: Const, blackList: List[Const] ): Const = Const( getRenaming( c.sym, blackList.map( c => c.sym ) ), c.exptype )
  def apply( c: FOLConst, blackList: List[Const] ): FOLConst =
    apply( c.asInstanceOf[Const], blackList ).asInstanceOf[FOLConst]

  /**
   * renames a set of variables to pairwise distinct variables while avoiding names from blackList.
   */
  def apply( vs: Set[FOLVar], blackList: Set[FOLVar] ): Map[FOLVar, FOLVar] = {
    val v_list = vs.toList
    ( v_list zip
      v_list.foldLeft( Nil: List[FOLVar] )(
        ( res, v ) => res :+ apply( v, ( blackList ++ res ).toList )
      ) ).toMap
  }
}

object toImplications {
  /**
   * Transforms subformulas of the form ¬A ∨ B or A ∨ ¬B to A → B or B → A, respectively.
   *
   * @param formula
   * @return
   */
  def apply( formula: HOLFormula ): HOLFormula = formula match {
    case Or( Neg( f ), g ) =>
      Imp( apply( f ), apply( g ) )
    case Or( f, Neg( g ) ) =>
      Imp( apply( g ), apply( f ) )
    case Or( f, g ) =>
      Or( apply( f ), apply( g ) )
    case And( f, g ) =>
      And( apply( f ), apply( g ) )
    case Neg( f )    => Neg( apply( f ) )
    case Ex( v, f )  => Ex( v, apply( f ) )
    case All( v, f ) => All( v, apply( f ) )
    case _           => formula
  }

  def apply( formula: FOLFormula ): FOLFormula = apply( formula.asInstanceOf[HOLFormula] ).asInstanceOf[FOLFormula]
}
