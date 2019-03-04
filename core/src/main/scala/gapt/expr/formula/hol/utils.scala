/*
 * Utility functions for higher-order logic.
 */

package gapt.expr.formula.hol

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Eq
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Quant
import gapt.expr.formula.Top
import gapt.expr.formula.constants.LogicalConstant
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.expr.subst.FOLSubstitution
import gapt.expr.subst.Substitution
import gapt.expr.ty.FunctionType
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.expr.ty.Ty
import gapt.expr.util.LambdaPosition
import gapt.expr.util.freeVariables
import gapt.logic.Polarity
import gapt.proofs.{ FOLClause, HOLSequent, Sequent }

/**
 * Returns true iff the given Expr consists of a logical constant.
 */
object isLogicalConstant {
  def apply( e: Expr ): Boolean = e.isInstanceOf[LogicalConstant]
}

/**
 * Returns true iff the given Formula is a reflexivity atom.
 */
object isReflexivity {
  def apply( f: Formula ): Boolean = f match {
    case Eq( s, t ) if s == t => true
    case _                    => false
  }
}

/**
 * Returns true iff the given Formula is an atom (which does
 * not include top nor bottom).
 */
object isAtom {
  def apply( e: Formula ): Boolean = e match {
    case Atom( _, _ ) => true
    case _            => false
  }
}

/**
 * Returns true iff the given Formula is an extended atom, i.e. an
 * atom or top or bottom.
 */
object isExtendedAtom {
  def apply( e: Formula ): Boolean = e match {
    case Atom( _, _ ) | Top() | Bottom() => true
    case _                               => false
  }
}

/**
 * Returns true iff the given Formula starts with a negation.
 */
object isNeg {
  def apply( formula: Formula ): Boolean = formula match {
    case Neg( _ ) => true
    case _        => false
  }
}

/**
 * Remove the leading negation from a formula.
 */
object removeNeg {
  def apply( formula: Formula ): Formula = formula match {
    case Neg( f ) => f
    case _        => throw new Exception( "Formula does not start with negation." )
  }
}

/**
 * Returns true iff the given formula is prenex.
 */
object isPrenex {
  def apply( e: Formula ): Boolean = e match {
    case Top() | Bottom() => true
    case Neg( f )         => !containsQuantifier( f )
    case And( f1, f2 )    => !containsQuantifier( f1 ) && !containsQuantifier( f2 )
    case Or( f1, f2 )     => !containsQuantifier( f1 ) && !containsQuantifier( f2 )
    case Imp( f1, f2 )    => !containsQuantifier( f1 ) && !containsQuantifier( f2 )
    case Ex( v, f )       => isPrenex( f )
    case All( v, f )      => isPrenex( f )
    case Atom( _, _ )     => true
    case _                => throw new Exception( "ERROR: Unknow operator encountered while checking for prenex formula: " + this )
  }

  def apply( sequent: HOLSequent ): Boolean = sequent.forall( isPrenex( _ ) )
}

/**
 * True iff All or Ex matches any subterm of e.
 */
object containsQuantifier {
  def apply( e: Expr ): Boolean = e match {
    case Top() | Bottom()   => false
    case Var( x, tpe )      => false
    case Const( x, tpe, _ ) => false
    case And( x, y )        => containsQuantifier( x ) || containsQuantifier( y )
    case Or( x, y )         => containsQuantifier( x ) || containsQuantifier( y )
    case Imp( x, y )        => containsQuantifier( x ) || containsQuantifier( y )
    case Neg( x )           => containsQuantifier( x )
    case Ex( x, f )         => true
    case All( x, f )        => true
    // Is this really necessary? Yes, they handle cases like P( (\x.x) a ) .
    case Abs( v, exp )      => containsQuantifier( exp )
    case App( l, r )        => containsQuantifier( l ) || containsQuantifier( r )
    case _                  => throw new Exception( "Unrecognized symbol." )
  }
}

/**
 * True iff All or Ex is contained in the logical structure of the given Formula.
 * For example, P( (all x:x) ) contains a quantifier, but it is inside of an atom.
 */
object containsQuantifierOnLogicalLevel {
  def apply( f: Formula ): Boolean = f match {
    case Top() | Bottom() => false
    case And( x, y )      => containsQuantifierOnLogicalLevel( x ) || containsQuantifierOnLogicalLevel( y )
    case Or( x, y )       => containsQuantifierOnLogicalLevel( x ) || containsQuantifierOnLogicalLevel( y )
    case Imp( x, y )      => containsQuantifierOnLogicalLevel( x ) || containsQuantifierOnLogicalLevel( y )
    case Neg( x )         => containsQuantifierOnLogicalLevel( x )
    case Ex( x, g )       => true
    case All( x, g )      => true
    case Atom( x, args )  => false // contents of atoms is ignored
    case _                => throw new Exception( "Unrecognized symbol." )
  }
}

object containsHOQuantifier {
  def apply( f: Formula ): Boolean = f match {
    case Top() | Bottom() | _: Atom                     => false
    case Neg( x )                                       => apply( x )
    case And( x, y )                                    => apply( x ) || apply( y )
    case Or( x, y )                                     => apply( x ) || apply( y )
    case Imp( x, y )                                    => apply( x ) || apply( y )
    case Quant( Var( _, FunctionType( To, _ ) ), _, _ ) => true // TODO: check if variable occurs as atom
    case Quant( _, sub, _ )                             => apply( sub )
  }
}

object containsStrongQuantifier {
  def apply( f: Formula, pol: Polarity ): Boolean = f match {
    case Top() | Bottom() => false
    case And( s, t )      => containsStrongQuantifier( s, pol ) || containsStrongQuantifier( t, pol )
    case Or( s, t )       => containsStrongQuantifier( s, pol ) || containsStrongQuantifier( t, pol )
    case Imp( s, t )      => containsStrongQuantifier( s, !pol ) || containsStrongQuantifier( t, pol )
    case Neg( s )         => containsStrongQuantifier( s, !pol )
    case All( x, s )      => pol.inSuc || containsStrongQuantifier( s, pol )
    case Ex( x, s )       => pol.inAnt || containsStrongQuantifier( s, pol )
    case Atom( _, _ )     => false
  }

  def apply( s: HOLSequent ): Boolean =
    s.polarizedElements.exists( ( apply: ( Formula, Polarity ) => Boolean ).tupled )
}

object containsWeakQuantifier {
  def apply( f: Formula, pol: Polarity ): Boolean = containsStrongQuantifier( f, !pol )

  def apply( s: HOLSequent ): Boolean =
    s.polarizedElements.exists( ( apply: ( Formula, Polarity ) => Boolean ).tupled )
}

object freeHOVariables {
  /**
   * Computes the set of all HOL Variables which are not of type i in a formula. Together with
   * checks on quantifiers, this can be used to decide if a formula has "true" higher-order content.
   *
   * @param f the expressions to extract from
   * @return the list of free variables with type != Ti in e
   */
  def apply( f: Expr ): Set[Var] = freeVariables( f ).filter( _ match { case Var( _, Ti ) => false; case _ => true } )

}

/**
 * Return the list of all atoms in the given argument.
 */
object atoms {
  def apply( f: Formula ): Set[Atom] = f match {
    case f: Atom          => Set( f )
    case And( x, y )      => apply( x ) union apply( y )
    case Or( x, y )       => apply( x ) union apply( y )
    case Imp( x, y )      => apply( x ) union apply( y )
    case Neg( x )         => apply( x )
    case Top() | Bottom() => Set()
    case Ex( x, y )       => apply( y )
    case All( x, y )      => apply( y )
  }

  def apply( f: FOLFormula ): Set[FOLAtom] = atoms( f: Formula ).asInstanceOf[Set[FOLAtom]]

  def apply( s: HOLSequent ): Set[Atom] = atoms( s.toImplication )
}

/**
 * Return the number of atoms in the given argument.
 */
object numOfAtoms {
  def apply( f: Formula ): Int = f match {
    case Atom( _, _ )     => 1
    case Top() | Bottom() => 0
    case Imp( f1, f2 )    => apply( f1 ) + apply( f2 )
    case And( f1, f2 )    => apply( f1 ) + apply( f2 )
    case Or( f1, f2 )     => apply( f1 ) + apply( f2 )
    case Ex( x, g )       => apply( g )
    case All( x, g )      => apply( g )
    case Neg( g )         => apply( g )
    case _                => throw new Exception( "ERROR: Unexpected case while counting the number of atoms." )
  }
}

/**
 * the logical complexity of this formula, i.e. the number of logical connectives and atoms
 * starting from the root of the formula. The inner structure of atoms is not counted.
 */
object lcomp {
  def apply( formula: Formula ): Int = formula match {
    case Top() | Bottom() => 1
    case Neg( f )         => lcomp( f ) + 1
    case And( f, g )      => lcomp( f ) + lcomp( g ) + 1
    case Or( f, g )       => lcomp( f ) + lcomp( g ) + 1
    case Imp( f, g )      => lcomp( f ) + lcomp( g ) + 1
    case Ex( x, f )       => lcomp( f ) + 1
    case All( x, f )      => lcomp( f ) + 1
    case Atom( _, _ )     => 1
  }

  def apply( seq: HOLSequent ): Int = seq.map( lcomp( _ ) ).elements.sum
}

object universalClosure {
  /**
   * Closes the given formula universally
   * @param f the formula to be closed
   * @return forall x,,1,,... forall x,,n,, f, where {x,,i,, | 1 <= i <= n} = FV(f)
   */
  def apply( f: Formula ): Formula = freeVariables( f ).foldRight( f )( ( v, g ) => All( v, g ) )

  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[Formula] ).asInstanceOf[FOLFormula]
}

object existentialClosure {
  /**
   * Closes the given formula existentially
   * @param f the formula to be closed
   * @return exists x,,1,, ... exists x,,n,, f, where {x,,i,, | 1 <= i <= n} = FV(f)
   */
  def apply( f: Formula ): Formula = freeVariables( f ).foldRight( f )( ( v, g ) => Ex( v, g ) )

  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[Formula] ).asInstanceOf[FOLFormula]

  /**
   * Closes all formulas on the right of the sequent existentially and all formulas on the left universally.
   */
  def apply( seq: HOLSequent ): HOLSequent = seq.map( universalClosure( _ ), existentialClosure( _ ) )
}

/**
 * Dualize a formula in NNF by switching conjunctions with disjunctions,
 * universal with existential quantifiers, top with bottom and positive literals
 * with negative literals. The formula dualize( A ) is logically equivalent to
 * the negation of A.
 */
object dualize {
  def apply( f: Formula ): Formula = f match {
    case Top()                  => Bottom()
    case Bottom()               => Top()
    case Atom( x, args )        => Neg( Atom( x, args ) )
    case Neg( Atom( x, args ) ) => Atom( x, args )
    case And( f1, f2 )          => Or( apply( f1 ), apply( f2 ) )
    case Or( f1, f2 )           => And( apply( f1 ), apply( f2 ) )
    case All( v, g )            => Ex( v, apply( g ) )
    case Ex( v, g )             => All( v, apply( g ) )
    case _                      => throw new Exception( "Formula not in NNF!" )
  }

  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[Formula] ).asInstanceOf[FOLFormula]
}

object removeAllQuantifiers {
  /**
   * Removes all quantifiers from the logical level of a Formula. Atoms are not changed.
   */
  def apply( f: Formula ): Formula = f match {
    case Atom( _, _ ) | Top() | Bottom() => f
    case Neg( f1 )                       => Neg( apply( f1 ) )
    case Imp( f1, f2 )                   => Imp( apply( f1 ), apply( f2 ) )
    case And( f1, f2 )                   => And( apply( f1 ), apply( f2 ) )
    case Or( f1, f2 )                    => Or( apply( f1 ), apply( f2 ) )
    case Ex( x, f1 )                     => apply( f1 )
    case All( x, f1 )                    => apply( f1 )
  }
  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[Formula] ).asInstanceOf[FOLFormula]
}

/**
 * Instantiates a formula with terms.
 */
object instantiate {
  /**
   * Instantiate a formula with a term by replacing the first quantifier
   */
  def apply( f: Formula, t: Expr ): Formula = f match {
    case All( v, form ) =>
      val sub = Substitution( v, t )
      sub( form )
    case Ex( v, form ) =>
      val sub = Substitution( v, t )
      sub( form )
    case _ =>
      throw new Exception( "ERROR: trying to replace variables in a formula without quantifier." )
  }

  /**
   * Instantiates the initial quantifiers of a formula with the given list of terms
   */
  def apply( f: Formula, ts: Seq[Expr] ): Formula = ts match {
    case Seq()   => f
    case t +: ts => instantiate( instantiate( f, t ), ts )
  }

  /**
   * If f is a formula \forall x_1 ... x_n G, and lst is a list of lists of terms
   * such that each list has length <= n, this function returns the list
   * of instances of f obtained by calling instantiate on each list of terms.
   */
  def apply( f: Formula, tss: Seq[Seq[Expr]] )( implicit d: DummyImplicit ): Seq[Formula] =
    tss.map( ts => instantiate( f, ts ) )

  def apply( f: FOLFormula, t: FOLTerm ): FOLFormula = apply( f: Formula, t: Expr ).asInstanceOf[FOLFormula]
  def apply( f: FOLFormula, ts: Seq[FOLTerm] ): FOLFormula = apply( f: Formula, ts: Seq[Expr] ).asInstanceOf[FOLFormula]
  def apply( f: FOLFormula, tss: Seq[Seq[FOLTerm]] )( implicit d: DummyImplicit ): Seq[FOLFormula] =
    apply( f: Formula, tss: Seq[Seq[FOLTerm]] ).asInstanceOf[Seq[FOLFormula]]

  /**
   * Compute all clauses obtainable from substituting terms from the given set for variables in the given clause.
   */
  def apply( cl: FOLClause, ts: Set[FOLTerm] ): Set[FOLClause] = {
    val vars = freeVariables( cl )
    val mappings = vars.foldLeft( Set( Map[FOLVar, FOLTerm]() ) )( ( ms, x ) => {
      for { m <- ms; t <- ts } yield m + ( x -> t )
    } )
    mappings.map( m => FOLSubstitution( m )( cl ) )
  }

  /**
   * Compute all clauses obtainable from substituting terms from the given set for variables in one of the given clauses.
   */
  def apply( cls: Set[FOLClause], ts: Set[FOLTerm] ): Set[FOLClause] = {
    cls.flatMap( apply( _, ts ) )
  }

  /**
   * Compute all clauses obtainable from substituting terms from the given set for variables in one of the given clauses.
   */
  def apply( cls: List[FOLClause], ts: Set[FOLTerm] ): List[FOLClause] = apply( cls.toSet, ts ).toList
}

object normalizeFreeVariables {
  /**
   * Systematically renames the free variables by their left-to-right occurence in a HOL Formula f to x,,i,, where all
   * x,,i,, are different from the names of all bound variables in the term. I.e. reversing the substitution yields
   * the syntactically same formula.
   *
   * @param f the formula to be normalized
   * @return a pair (g,sub) such that g = sub(f). reversing sub allows to restore the original variables.
   */
  def apply( f: Formula ): ( Formula, Substitution ) = apply( f: Expr ).asInstanceOf[( Formula, Substitution )]

  /**
   * Systematically renames the free variables by their left-to-right occurence in a HOL Expression f to x_{i} where all
   * x_{i} are different from the names of all bound variables in the term. I.e. reversing the substitution yields
   * the syntactically same formula.
   *
   * @param f the expression to be normalized
   * @return a pair (g,sub) such that g = sub(f). reversing sub allows to restore the original variables.
   */
  def apply( f: Expr ): ( Expr, Substitution ) = {
    var i = 0
    //generate a blacklist that prevents renaming of bound variables
    val blacklist = LambdaPosition.getPositions( f ).flatMap( f( _ ) match {
      case All( x, _ ) => List( x.name )
      case Ex( x, _ )  => List( x.name )
      case _           => Nil
    } )

    apply( f, () => {
      var name = "x_{" + i + "}"
      do {
        i = i + 1
        name = "x_{" + i + "}"
      } while ( blacklist.contains( name ) )
      name
    } )
  }

  /**
   * Works exactly like normalizeFreeVaribles(f:Formula) but allows the specification of your own name generator.
   * Please note that such a normalized formula is still only unique up to alpha equality. Compare for example
   * (∀y P(x,y)) with (∀x,,0,, P(x,x,,0,,):
   * the first normalizes to (∀y P(x,,0,,,y)) whereas the second normalizes to (∀x_{0}1 P(x_{0},x_{0}1).
   *
   * @param f the formula to be normalized
   * @param freshName a function which generates a fresh name every call.
   * @return a pair (g,sub) such that g = sub(f). reversing sub allows to restore the original variables.
   */
  def apply( f: Formula, freshName: () => String ): ( Formula, Substitution ) =
    apply( f: Expr, freshName ).asInstanceOf[( Formula, Substitution )]

  /**
   * Works exactly like normalizeFreeVaribles(f:Expr) but allows the specification of your own name generator.
   * Please note that such a normalized formula is still only unique up to alpha equality. Compare for example
   * (all y P(x,y)) with (all x_{0} P(x,x_{0}):
   * the first normalizes to (all y P(x_{0},y) whereas the second normalizes to (all x_{0}1 P(x_{0},x_{0}1)).
   *
   * @param f the formula to be normalized
   * @param freshName a function which generates a fresh name every call.
   * @return a pair (g,sub) such that g = sub(f). reversing sub allows to restore the original variables.
   */
  def apply( f: Expr, freshName: () => String ): ( Expr, Substitution ) = {
    val vs = freeVariables( f )
    val map = vs.foldLeft( Map[Var, Var]() )( ( map, v ) => {
      if ( map.contains( v ) ) map else {
        val name = freshName()
        map + ( ( v, Var( name, v.ty ) ) )
      }
    } )

    val sub = Substitution( map )
    ( sub( f ), sub )
  }
}

/**
 * Removes top-level connectives from a formula.
 */
object formulaToSequent {
  /**
   * Returns a sequent that is equivalent to :- formula.
   */
  def pos( formula: Formula ): HOLSequent = formula match {
    case Or( a, b )  => pos( a ) ++ pos( b )
    case Imp( a, b ) => neg( a ) ++ pos( b )
    case Neg( a )    => neg( a )
    case Bottom()    => Sequent()
    case _           => Sequent() :+ formula
  }
  /**
   * Returns a sequent that is equivalent to formula :-.
   */
  def neg( formula: Formula ): HOLSequent = formula match {
    case And( a, b ) => neg( a ) ++ neg( b )
    case Neg( a )    => pos( a )
    case Top()       => Sequent()
    case _           => formula +: Sequent()
  }
}

object inductionPrinciple {
  def apply( indty: Ty, constrs: Seq[Const] ): Formula = {
    val pred = Var( "X", indty ->: To )

    val hyps = constrs.map { constr =>
      val FunctionType( `indty`, argtypes ) = constr.ty
      val vars = for ( ( at, i ) <- argtypes.zipWithIndex ) yield Var( s"x$i", at )

      All.Block( vars, vars.filter {
        _.ty == indty
      }.foldRight( pred( constr( vars: _* ) ) )( ( v, f ) => pred( v ) --> f ) )
    }

    hof"∀X (${And( hyps )} → ∀x $pred x)"
  }
}