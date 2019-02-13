/*
 * Utility functions for the lambda calculus.
 */

package gapt.expr.util

import gapt.expr.->:
import gapt.expr.Abs
import gapt.expr.All
import gapt.expr.And
import gapt.expr.App
import gapt.expr.Apps
import gapt.expr.Const
import gapt.expr.Ex
import gapt.expr.Expr
import gapt.expr.FOLConst
import gapt.expr.FOLExpression
import gapt.expr.FOLFormula
import gapt.expr.FOLVar
import gapt.expr.Formula
import gapt.expr.Imp
import gapt.expr.LogicalConstant
import gapt.expr.Neg
import gapt.expr.Or
import gapt.expr.Substitution
import gapt.expr.TBase
import gapt.expr.TVar
import gapt.expr.To
import gapt.expr.Ty
import gapt.expr.Var
import gapt.expr.VarOrConst
import gapt.proofs._
import gapt.proofs.context.Context
import gapt.utils.NameGenerator

import scala.collection.GenTraversable
import scala.collection.mutable

/**
 * A lambda term is in variable-normal form (VNF) if different binders bind
 * different variables, and bound variables are disjoint from the free ones.
 */
object isInVNF {
  def apply( e: Expr ): Boolean = {
    val seen = mutable.Set[Var]()
    seen ++= freeVariables( e )

    def check( e: Expr ): Boolean = e match {
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
  def apply( e: Expr, nameGen: NameGenerator ): Expr = e match {
    case v: VarOrConst => v
    case App( a, b )   => App( apply( a, nameGen ), apply( b, nameGen ) )
    case Abs( v, a ) =>
      val v_ = nameGen.fresh( v )
      if ( v == v_ ) Abs( v, apply( a, nameGen ) )
      else Abs( v_, apply( Substitution( v -> v_ )( a ), nameGen ) )
  }

  def apply( e: Expr ): Expr = apply( e, rename.awayFrom( freeVariables( e ) ) )
  def apply( f: Formula ): Formula = apply( f.asInstanceOf[Expr] ).asInstanceOf[Formula]

  def apply( sequent: HOLSequent ): HOLSequent = {
    val nameGen = rename.awayFrom( freeVariables( sequent ) )
    sequent.map( apply( _, nameGen ).asInstanceOf[Formula] )
  }
}

/**
 * Returns the set of all variables occurring in the given argument (including
 * bound variables).
 */
object variables {
  def apply( e: Expr ): Set[Var] = {
    val vs = mutable.Set[Var]()
    def go( e: Expr ): Unit = e match {
      case v: Var   => vs += v
      case _: Const =>
      case App( a, b ) =>
        go( a ); go( b )
      case Abs( v, t ) => vs += v; go( t )
    }
    go( e )
    vs.toSet
  }

  def apply( t: FOLExpression ): Set[FOLVar] = apply( t.asInstanceOf[Expr] ).asInstanceOf[Set[FOLVar]]
  def apply( s: HOLSequent ): Set[Var] = ( s.antecedent ++ s.succedent ).foldLeft( Set[Var]() )( ( x, y ) => x ++ apply( y ) )
  def apply( s: Sequent[FOLFormula] )( implicit dummyImplicit: DummyImplicit, dummyImplicit2: DummyImplicit ): Set[FOLVar] = s.elements flatMap apply toSet
  def apply[Fml <: Expr, Proof <: SequentProof[Fml, Proof]]( p: SequentProof[Fml, Proof] ): Set[Var] =
    p.subProofs flatMap { _.conclusion.elements } flatMap { variables( _ ) }
}

/**
 * Returns the set of all bound variables occurring in the given argument.
 */
object boundVariables {
  def apply( e: Expr ): Set[Var] = {
    val vs = mutable.Set[Var]()
    def go( e: Expr ): Unit = e match {
      case _: Var   =>
      case _: Const =>
      case App( a, b ) =>
        go( a ); go( b )
      case Abs( v, t ) => vs += v; go( t )
    }
    go( e )
    vs.toSet
  }

  def apply( t: FOLExpression ): Set[FOLVar] = apply( t.asInstanceOf[Expr] ).asInstanceOf[Set[FOLVar]]
  def apply( s: HOLSequent ): Set[Var] = ( s.antecedent ++ s.succedent ).foldLeft( Set[Var]() )( ( x, y ) => x ++ apply( y ) )
  def apply( s: Sequent[FOLFormula] )( implicit dummyImplicit: DummyImplicit, dummyImplicit2: DummyImplicit ): Set[FOLVar] = s.elements flatMap apply toSet
  def apply[Fml <: Expr, Proof <: SequentProof[Fml, Proof]]( p: SequentProof[Fml, Proof] ): Set[Var] =
    p.subProofs flatMap { _.conclusion.elements } flatMap { variables( _ ) }
}

/**
 * Returns the set of free variables in the given argument.
 */
object freeVariables {
  def apply( e: Expr ): Set[Var] = freeVariables( Some( e ) )

  def apply( es: TraversableOnce[Expr] ): Set[Var] = {
    val free = Set.newBuilder[Var]
    def visit( e: Expr, bound: Set[Var] ): Unit = e match {
      case v: Var =>
        if ( !bound( v ) ) free += v
      case App( a, b ) =>
        visit( a, bound )
        visit( b, bound )
      case Abs( x, a ) =>
        visit( a, bound + x )
      case _: Const =>
    }
    es.foreach( visit( _, Set() ) )
    free.result()
  }

  def apply( seq: HOLSequent ): Set[Var] = apply( seq.elements )

  def apply( e: FOLExpression ): Set[FOLVar] = apply( Some( e ) )
  def apply( es: TraversableOnce[FOLExpression] )( implicit dummyImplicit: DummyImplicit ): Set[FOLVar] =
    freeVariables( es.asInstanceOf[TraversableOnce[Expr]] ).asInstanceOf[Set[FOLVar]]
  def apply( seq: FOLSequent )( implicit dummyImplicit: DummyImplicit ): Set[FOLVar] = apply( seq.elements )
}

object typeVariables {
  def apply( t: Ty ): Set[TVar] = t match {
    case a ->: b        => apply( a ) ++ apply( b )
    case TBase( _, ps ) => ps.view.flatMap( apply ).toSet
    case t: TVar        => Set( t )
  }

  def apply( ts: Iterable[Ty] ): Set[TVar] =
    ts.view.flatMap( apply ).toSet

  def apply( e: Expr ): Set[TVar] = e match {
    case Const( _, t, ps ) => apply( t ) ++ ps.flatMap( apply )
    case Var( _, t )       => apply( t )
    case App( a, b )       => apply( a ) ++ apply( b )
    case Abs( v, s )       => apply( s ) ++ apply( v )
  }

  def apply( es: Iterable[Expr] )( implicit dummyImplicit: DummyImplicit ): Set[TVar] =
    es.view.flatMap( apply ).toSet
}

/**
 * Returns the set of non-logical constants occuring in the given argument.
 */
object constants {
  /**
   * Find all constants in the expression
   */
  def all( expression: Expr ): Set[Const] = {
    val cs = mutable.Set[Const]()
    def f( e: Expr ): Unit = e match {
      case _: Var   =>
      case c: Const => cs += c
      case App( exp, arg ) =>
        f( exp ); f( arg )
      case Abs( v, exp ) => f( exp )
    }
    f( expression )
    cs.toSet
  }

  /**
   * Find all equality constants in the expression
   */
  def equalities( expression: Expr ): Set[Const] =
    all( expression ).filter {
      case Const( "=", t1 ->: t2 ->: To, _ ) => t1 == t2 //type arguments must agree
      case _                                 => false
    }

  def apply( expression: Expr ): Set[Const] =
    all( expression ).filter { !_.isInstanceOf[LogicalConstant] }

  def apply( es: GenTraversable[Expr] ): Set[Const] = ( Set.empty[Const] /: es ) { ( acc, e ) => acc union apply( e ) }

  def apply( s: HOLSequent ): Set[Const] = ( s.antecedent ++ s.succedent ).foldLeft( Set[Const]() )( ( x, y ) => x ++ apply( y ) )
}

/**
 * Returns the set of all subterms of the given lambda term.
 */
object subTerms {
  def apply( e: Expr ): Set[Expr] = e match {
    case Var( _, _ ) | Const( _, _, _ ) => Set( e )
    case Abs( _, e0 )                   => apply( e0 ) + e
    case App( e1, e2 )                  => ( apply( e1 ) ++ apply( e2 ) ) + e
  }
}

object expressionSize {
  def apply( e: Expr ): Int = e match {
    case Var( _, _ ) | Const( _, _, _ ) => 1
    case Abs( _, f )                    => 1 + expressionSize( f )
    case App( a, b )                    => 1 + expressionSize( a ) + expressionSize( b )
  }
}

object expressionDepth {
  /**
   * Computes the depth of an expression.
   *
   * @param t The expression whose depth is to be computed.
   * @return The depth of the given expression, that is, the maximum depth
   * of branches in the expression's tree representation.
   */
  def apply( t: Expr ): Int = t match {
    case Var( _, _ ) | Const( _, _, _ ) => 1
    case Abs( _, s )                    => apply( s ) + 1
    case App( a, b )                    => ( apply( a ) max apply( b ) ) + 1
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
  def apply( formula: Formula ): Formula = formula match {
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

  def apply( formula: FOLFormula ): FOLFormula = apply( formula.asInstanceOf[Formula] ).asInstanceOf[FOLFormula]
}

object isConstructorForm {
  /**
   * Checks whether a term is in constructor form.
   * @param term The term that is to be checked.
   * @param ctx The context which defines inductive types, etc.
   * @return true if the term is in constructor form, false otherwise.
   */
  def apply( term: Expr )( implicit ctx: Context ): Boolean = {
    val constructors = ctx.getConstructors( term.ty.asInstanceOf[TBase] ).get
    val Apps( head, arguments ) = term
    constructors.contains( head ) && arguments.filter( _.ty == term.ty ).forall( apply _ )
  }
}

object isGround {
  /**
   * Checks whether an expression is ground.
   * @param expr The expression that is to be checked.
   * @return true if the given expression does not contain any free variables, false otherwise.
   */
  def apply( expr: Expr ): Boolean = freeVariables( expr ).isEmpty
}
