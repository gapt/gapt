/*
 * Utility functions for the lambda calculus.
 */

package at.logic.gapt.expr

import at.logic.gapt.proofs._

import scala.collection.GenTraversable
import scala.collection.mutable

/**
 * Matches constants and variables, but nothing else.
 */
object VarOrConst {
  def unapply( e: LambdaExpression ): Option[( String, Ty )] = e match {
    case Var( name, et )   => Some( ( name, et ) )
    case Const( name, et ) => Some( ( name, et ) )
    case _                 => None
  }
}

/**
 * A lambda term is in variable-normal form (VNF) if different binders bind
 * different variables, and bound variables are disjoint from the free ones.
 */
object isInVNF {
  def apply( e: LambdaExpression ): Boolean = {
    val seen = mutable.Set[Var]()
    seen ++= freeVariables( e )

    def check( e: LambdaExpression ): Boolean = e match {
      case _: Var | _: Const              => true
      case App( a, b )                    => check( a ) && check( b )
      case Abs( v, a ) if seen contains v => false
      case Abs( v, a )                    => seen += v; check( a )
    }

    check( e )
  }
}

/**
 * Transforms an expression into an alpha-equivalent expression in
 * variable-normal form, where no two binders bind the same variable,
 * and the bound variables are disjoint from the free ones.
 */
object toVNF {
  def apply( e: LambdaExpression ): LambdaExpression = {
    val seen = mutable.Set[Var]()

    def makeDistinct( e: LambdaExpression ): LambdaExpression = e match {
      case v @ Var( _, _ ) =>
        seen += v; v
      case Const( _, _ ) => e
      case App( a, b )   => App( makeDistinct( a ), makeDistinct( b ) )
      case Abs( v, a ) if seen contains v =>
        val newVar = rename( v, seen toList )
        makeDistinct( Abs( newVar, Substitution( v -> newVar )( a ) ) )
      case Abs( v, a ) if !( seen contains v ) =>
        seen += v
        Abs( v, makeDistinct( a ) )
    }

    makeDistinct( e )
  }

  def apply( f: HOLFormula ): HOLFormula = apply( f.asInstanceOf[LambdaExpression] ).asInstanceOf[HOLFormula]
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

  def apply( t: FOLExpression ): Set[FOLVar] = apply( t.asInstanceOf[LambdaExpression] ).asInstanceOf[Set[FOLVar]]
  def apply( s: HOLSequent ): Set[Var] = ( s.antecedent ++ s.succedent ).foldLeft( Set[Var]() )( ( x, y ) => x ++ apply( y ) )
  def apply( s: Sequent[FOLFormula] )( implicit dummyImplicit: DummyImplicit, dummyImplicit2: DummyImplicit ): Set[FOLVar] = s.elements flatMap apply toSet
  def apply( s: at.logic.gapt.proofs.lkOld.base.OccSequent )( implicit dummy: DummyImplicit ): Set[Var] = apply( s.map( _.formula ) )
  def apply( p: at.logic.gapt.proofs.lkOld.base.LKProof ): Set[Var] = p.fold( apply )( _ ++ apply( _ ) )( _ ++ _ ++ apply( _ ) )
  def apply[Expr <: LambdaExpression, Proof <: SequentProof[Expr, Proof]]( p: SequentProof[Expr, Proof] ): Set[Var] =
    p.subProofs flatMap { _.conclusion.elements } flatMap { variables( _ ) }
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
  def apply( expression: LambdaExpression ): Set[Const] = {
    val cs = mutable.Set[Const]()
    def f( e: LambdaExpression ): Unit = e match {
      case _: Var             =>
      case _: LogicalConstant =>
      case c: Const           => cs += c
      case App( exp, arg ) =>
        f( exp ); f( arg )
      case Abs( v, exp ) => f( exp )
    }
    f( expression )
    cs.toSet
  }

  def apply( es: GenTraversable[LambdaExpression] ): Set[Const] = ( Set.empty[Const] /: es ) { ( acc, e ) => acc union apply( e ) }

  def apply( s: HOLSequent ): Set[Const] = ( s.antecedent ++ s.succedent ).foldLeft( Set[Const]() )( ( x, y ) => x ++ apply( y ) )
  def apply( s: at.logic.gapt.proofs.lkOld.base.OccSequent )( implicit dummy: DummyImplicit ): Set[Const] = apply( s.map( _.formula ) )
  def apply( p: at.logic.gapt.proofs.lkOld.base.LKProof ): Set[Const] = p.fold( apply )( _ ++ apply( _ ) )( _ ++ _ ++ apply( _ ) )
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
    case Var( _, _ ) | Const( _, _ ) => 1
    case Abs( _, f )                 => 1 + expressionSize( f )
    case App( a, b )                 => 1 + expressionSize( a ) + expressionSize( b )
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
  def apply( vs: Set[Var], blackList: Set[Var] )( implicit dummyImplicit: DummyImplicit ): Map[Var, Var] = {
    val v_list = vs.toList
    ( v_list zip
      v_list.foldLeft( Nil: List[Var] )(
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
