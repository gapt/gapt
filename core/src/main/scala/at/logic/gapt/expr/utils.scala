/*
 * Utility functions for the lambda calculus.
 */

package at.logic.gapt.expr

import at.logic.gapt.proofs._
import at.logic.gapt.utils.NameGenerator

import scala.collection.GenTraversable
import scala.collection.mutable

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
  def apply( e: LambdaExpression, nameGen: NameGenerator ): LambdaExpression = e match {
    case v: VarOrConst => v
    case App( a, b )   => App( apply( a, nameGen ), apply( b, nameGen ) )
    case Abs( v, a ) =>
      val v_ = nameGen.fresh( v )
      if ( v == v_ ) Abs( v, apply( a, nameGen ) )
      else Abs( v_, apply( Substitution( v -> v_ )( a ), nameGen ) )
  }

  def apply( e: LambdaExpression ): LambdaExpression = apply( e, rename.awayFrom( freeVariables( e ) ) )
  def apply( f: HOLFormula ): HOLFormula = apply( f.asInstanceOf[LambdaExpression] ).asInstanceOf[HOLFormula]

  def apply( sequent: HOLSequent ): HOLSequent = {
    val nameGen = rename.awayFrom( freeVariables( sequent ) )
    sequent.map( apply( _, nameGen ).asInstanceOf[HOLFormula] )
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

  def apply( t: FOLExpression ): Set[FOLVar] = apply( t.asInstanceOf[LambdaExpression] ).asInstanceOf[Set[FOLVar]]
  def apply( s: HOLSequent ): Set[Var] = ( s.antecedent ++ s.succedent ).foldLeft( Set[Var]() )( ( x, y ) => x ++ apply( y ) )
  def apply( s: Sequent[FOLFormula] )( implicit dummyImplicit: DummyImplicit, dummyImplicit2: DummyImplicit ): Set[FOLVar] = s.elements flatMap apply toSet
  def apply[Expr <: LambdaExpression, Proof <: SequentProof[Expr, Proof]]( p: SequentProof[Expr, Proof] ): Set[Var] =
    p.subProofs flatMap { _.conclusion.elements } flatMap { variables( _ ) }
}

/**
 * Returns the set of free variables in the given argument.
 */
object freeVariables {
  def apply( e: LambdaExpression ): Set[Var] = freeVariables( Some( e ) )

  def apply( es: TraversableOnce[LambdaExpression] ): Set[Var] = {
    val fvs = Set.newBuilder[Var]
    def f( e: LambdaExpression ): Unit = e match {
      case v: Var => fvs += v
      case App( a, b ) =>
        f( a )
        f( b )
      case Abs( x, a ) => fvs ++= freeVariables( a ) - x
      case _           =>
    }
    es foreach f
    fvs.result()
  }

  def apply( seq: HOLSequent ): Set[Var] = apply( seq.elements )

  def apply( e: FOLExpression ): Set[FOLVar] = apply( Some( e ) )
  def apply( es: TraversableOnce[FOLExpression] )( implicit dummyImplicit: DummyImplicit ): Set[FOLVar] =
    freeVariables( es.asInstanceOf[TraversableOnce[LambdaExpression]] ).asInstanceOf[Set[FOLVar]]
  def apply( seq: FOLSequent )( implicit dummyImplicit: DummyImplicit ): Set[FOLVar] = apply( seq.elements )
}

object typeVariables {
  def apply( t: Ty ): Set[TVar] = t match {
    case a -> b   => apply( a ) ++ apply( b )
    case _: TBase => Set()
    case t: TVar  => Set( t )
  }

  def apply( e: LambdaExpression ): Set[TVar] = e match {
    case Const( _, t ) => apply( t )
    case Var( _, t )   => apply( t )
    case App( a, b )   => apply( a ) ++ apply( b )
    case Abs( v, s )   => apply( s ) ++ apply( v )
  }
}

/**
 * Returns the set of non-logical constants occuring in the given argument.
 */
object constants {
  def all( expression: LambdaExpression ): Set[Const] = {
    val cs = mutable.Set[Const]()
    def f( e: LambdaExpression ): Unit = e match {
      case _: Var   =>
      case c: Const => cs += c
      case App( exp, arg ) =>
        f( exp ); f( arg )
      case Abs( v, exp ) => f( exp )
    }
    f( expression )
    cs.toSet
  }
  def apply( expression: LambdaExpression ): Set[Const] =
    all( expression ).filter { !_.isInstanceOf[LogicalConstant] }

  def apply( es: GenTraversable[LambdaExpression] ): Set[Const] = ( Set.empty[Const] /: es ) { ( acc, e ) => acc union apply( e ) }

  def apply( s: HOLSequent ): Set[Const] = ( s.antecedent ++ s.succedent ).foldLeft( Set[Const]() )( ( x, y ) => x ++ apply( y ) )
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
  def awayFrom( blacklist: Iterable[VarOrConst] ): NameGenerator =
    new NameGenerator( blacklist map { _.name } )

  def apply( v: Var, blackList: Iterable[VarOrConst] ): Var = awayFrom( blackList ).fresh( v )
  def apply( v: FOLVar, blackList: Iterable[VarOrConst] ): FOLVar = awayFrom( blackList ).fresh( v )
  def apply( c: Const, blackList: Iterable[VarOrConst] ): Const = awayFrom( blackList ).fresh( c )
  def apply( c: FOLConst, blackList: Iterable[VarOrConst] ): FOLConst = awayFrom( blackList ).fresh( c )

  /**
   * renames a set of variables to pairwise distinct variables while avoiding names from blackList.
   */
  def apply( vs: Iterable[FOLVar], blackList: Iterable[VarOrConst] ): Map[FOLVar, FOLVar] = {
    val nameGen = awayFrom( blackList )
    vs map { v => v -> nameGen.fresh( v ) } toMap
  }
  def apply( vs: Iterable[Var], blackList: Iterable[VarOrConst] )( implicit dummyImplicit: DummyImplicit ): Map[Var, Var] = {
    val nameGen = awayFrom( blackList )
    vs map { v => v -> nameGen.fresh( v ) } toMap
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
