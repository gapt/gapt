/*
 * Utility functions for the lambda calculus.
 */

package at.logic.gapt.expr

import at.logic.gapt.proofs.lk.{ Axiom, BinaryLKProof, UnaryLKProof }
import at.logic.gapt.proofs.lk.base.{ Sequent, FSequent, LKProof }

import scala.collection.GenTraversable

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
  def apply( s: FSequent ): Set[Var] = ( s.antecedent ++ s.succedent ).foldLeft( Set[Var]() )( ( x, y ) => x ++ apply( y ) )
  def apply( s: Sequent ): Set[Var] = apply( s.toFSequent )
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

  def apply( seq: FSequent ): Set[Var] = apply( seq.antecedent ++ seq.succedent )

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

  def apply( s: FSequent ): Set[Const] = ( s.antecedent ++ s.succedent ).foldLeft( Set[Const]() )( ( x, y ) => x ++ apply( y ) )
  def apply( s: Sequent ): Set[Const] = apply( s.toFSequent )
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

  /**
   * renames a set of variables to pairwise distinct variables while avoiding names from blackList.
   */
  def apply( vs: Set[FOLVar], blackList: Set[FOLVar] ): Map[FOLVar, FOLVar] = {
    val v_list = vs.toList
    ( v_list zip
      v_list.foldLeft( Nil: List[FOLVar] )(
        ( res, v ) => res :+ apply( v, ( blackList ++ res ).toList ) ) ).toMap
  }
}
