/*
 * Utility functions for higher-order logic.
 */

package at.logic.gapt.expr.hol

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Sequent, HOLSequent, FOLClause }

/**
 * Returns true iff the given LambdaExpression consists of a logical constant.
 */
object isLogicalConstant {
  def apply( e: LambdaExpression ): Boolean = e.isInstanceOf[LogicalConstant]
}

/**
 * Returns true iff the given HOLFormula is a reflexivity atom.
 */
object isReflexivity {
  def apply( f: HOLFormula ): Boolean = f match {
    case Eq( s, t ) if s == t => true
    case _                    => false
  }
}

/**
 * Returns true iff the given HOLFormula is an atom (which does
 * not include top nor bottom).
 */
object isAtom {
  def apply( e: HOLFormula ): Boolean = e match {
    case HOLAtom( _, _ ) => true
    case _               => false
  }
}

/**
 * Returns true iff the given HOLFormula is an extended atom, i.e. an
 * atom or top or bottom.
 */
object isExtendedAtom {
  def apply( e: HOLFormula ): Boolean = e match {
    case HOLAtom( _, _ ) | Top() | Bottom() => true
    case _                                  => false
  }
}

/**
 * Returns true iff the given HOLFormula starts with a negation.
 */
object isNeg {
  def apply( formula: HOLFormula ) = formula match {
    case Neg( _ ) => true
    case _        => false
  }
}

/**
 * Remove the leading negation from a formula.
 */
object removeNeg {
  def apply( formula: HOLFormula ) = formula match {
    case Neg( f ) => f
    case _        => throw new Exception( "Formula does not start with negation." )
  }
}

/**
 * Returns true iff the given formula is prenex.
 */
object isPrenex {
  def apply( e: HOLFormula ): Boolean = e match {
    case Top() | Bottom() => true
    case Neg( f )         => !containsQuantifier( f )
    case And( f1, f2 )    => !containsQuantifier( f1 ) && !containsQuantifier( f2 )
    case Or( f1, f2 )     => !containsQuantifier( f1 ) && !containsQuantifier( f2 )
    case Imp( f1, f2 )    => !containsQuantifier( f1 ) && !containsQuantifier( f2 )
    case Ex( v, f )       => isPrenex( f )
    case All( v, f )      => isPrenex( f )
    case HOLAtom( _, _ )  => true
    case _                => throw new Exception( "ERROR: Unknow operator encountered while checking for prenex formula: " + this )
  }
}

/**
 * True iff All or Ex matches any subterm of e.
 */
object containsQuantifier {
  def apply( e: LambdaExpression ): Boolean = e match {
    case Top() | Bottom() => false
    case Var( x, tpe )    => false
    case Const( x, tpe )  => false
    case And( x, y )      => containsQuantifier( x ) || containsQuantifier( y )
    case Or( x, y )       => containsQuantifier( x ) || containsQuantifier( y )
    case Imp( x, y )      => containsQuantifier( x ) || containsQuantifier( y )
    case Neg( x )         => containsQuantifier( x )
    case Ex( x, f )       => true
    case All( x, f )      => true
    // Is this really necessary? Yes, they handle cases like P( (\x.x) a ) .
    case Abs( v, exp )    => containsQuantifier( exp )
    case App( l, r )      => containsQuantifier( l ) || containsQuantifier( r )
    case _                => throw new Exception( "Unrecognized symbol." )
  }
}

/**
 * True iff All or Ex is contained in the logical structure of the given HOLFormula.
 * For example, P( (all x:x) ) contains a quantifier, but it is inside of an atom.
 */
object containsQuantifierOnLogicalLevel {
  def apply( f: HOLFormula ): Boolean = f match {
    case Top() | Bottom()   => false
    case And( x, y )        => containsQuantifierOnLogicalLevel( x ) || containsQuantifierOnLogicalLevel( y )
    case Or( x, y )         => containsQuantifierOnLogicalLevel( x ) || containsQuantifierOnLogicalLevel( y )
    case Imp( x, y )        => containsQuantifierOnLogicalLevel( x ) || containsQuantifierOnLogicalLevel( y )
    case Neg( x )           => containsQuantifierOnLogicalLevel( x )
    case Ex( x, f )         => true
    case All( x, f )        => true
    case HOLAtom( x, args ) => false // contents of atoms is ignored
    case _                  => throw new Exception( "Unrecognized symbol." )
  }
}

object containsStrongQuantifier {
  def apply( f: HOLFormula, pol: Boolean ): Boolean = f match {
    case Top() | Bottom() => false
    case And( s, t )      => containsStrongQuantifier( s, pol ) || containsStrongQuantifier( t, pol )
    case Or( s, t )       => containsStrongQuantifier( s, pol ) || containsStrongQuantifier( t, pol )
    case Imp( s, t )      => containsStrongQuantifier( s, !pol ) || containsStrongQuantifier( t, pol )
    case Neg( s )         => containsStrongQuantifier( s, !pol )
    case All( x, s )      => if ( pol == true ) true else containsStrongQuantifier( s, pol )
    case Ex( x, s )       => if ( pol == false ) true else containsStrongQuantifier( s, pol )
    case HOLAtom( _, _ )  => false
    case _                => throw new Exception( "Unhandled case!" )
  }

  def apply( s: HOLSequent ): Boolean =
    s.antecedent.exists( x => containsStrongQuantifier( x, false ) ) ||
      s.succedent.exists( x => containsStrongQuantifier( x, true ) )
}

object freeHOVariables {
  /**
   * Computes the set of all HOL Variables which are not of type i in a formula. Together with
   * checks on quantifiers, this can be used to decide if a formula has "true" higher-order content.
   *
   * @param f the expressions to extract from
   * @return the list of free variables with type != Ti in e
   */
  def apply( f: LambdaExpression ) = freeVariables( f ).filter( _ match { case Var( _, Ti ) => false; case _ => true } )

}

/**
 * Return the list of all atoms *with duplicates* in the given argument.
 * TODO: why a list? why duplicates? why not a set?
 */
object atoms {
  def apply( f: HOLFormula ): List[HOLFormula] = f match {
    case Neg( f )         => apply( f )
    case And( f1, f2 )    => apply( f1 ) ++ apply( f2 )
    case Or( f1, f2 )     => apply( f1 ) ++ apply( f2 )
    case Imp( f1, f2 )    => apply( f1 ) ++ apply( f2 )
    case Ex( v, f )       => apply( f )
    case All( v, f )      => apply( f )
    case Bottom() | Top() => List()
    case HOLAtom( _, _ )  => List( f )
  }

  def apply( s: HOLSequent ): List[HOLFormula] = {
    val all = s.antecedent ++ s.succedent
    all.foldLeft( List[HOLFormula]() ) { case ( acc, f ) => apply( f ) ++ acc }
  }
}

/**
 * Return the number of atoms in the given argument.
 */
object numOfAtoms {
  def apply( f: HOLFormula ): Int = f match {
    case HOLAtom( _, _ )  => 1
    case Top() | Bottom() => 0
    case Imp( f1, f2 )    => apply( f1 ) + apply( f2 )
    case And( f1, f2 )    => apply( f1 ) + apply( f2 )
    case Or( f1, f2 )     => apply( f1 ) + apply( f2 )
    case Ex( x, f )       => apply( f )
    case All( x, f )      => apply( f )
    case Neg( f )         => apply( f )
    case _                => throw new Exception( "ERROR: Unexpected case while counting the number of atoms." )
  }
}

/**
 * the logical complexity of this formula, i.e. the number of logical connectives and atoms
 * starting from the root of the formula. The inner structure of atoms is not counted.
 */
object lcomp {
  def apply( formula: HOLFormula ): Int = formula match {
    case Top() | Bottom() => 1
    case Neg( f )         => lcomp( f ) + 1
    case And( f, g )      => lcomp( f ) + lcomp( g ) + 1
    case Or( f, g )       => lcomp( f ) + lcomp( g ) + 1
    case Imp( f, g )      => lcomp( f ) + lcomp( g ) + 1
    case Ex( x, f )       => lcomp( f ) + 1
    case All( x, f )      => lcomp( f ) + 1
    case HOLAtom( _, _ )  => 1
  }

  def apply( seq: HOLSequent ): Int = seq.antecedent.foldLeft( 0 )( _ + lcomp( _ ) ) + seq.succedent.foldLeft( 0 )( _ + lcomp( _ ) )
}

object variablesAll {
  /**
   * If formula starts with ∀x,,1,,…∀x,,n,,, returns [x,,1,,,…,x,,n,,]. Otherwise returns Nil.
   *
   * @param formula The formula under consideration.
   * @return
   */
  def apply( formula: HOLFormula ): List[Var] = formula match {
    case All( v, f ) => v +: apply( f )
    case _           => Nil
  }
}

object variablesEx {
  /**
   * If formula starts with ∃x,,1,,…∃x,,n,,, returns [x,,1,,,…,x,,n,,]. Otherwise returns Nil.
   *
   * @param formula The formula under consideration.
   * @return
   */
  def apply( formula: HOLFormula ): List[Var] = formula match {
    case Ex( v, f ) => v +: apply( f )
    case _          => Nil
  }
}

object univclosure {
  /**
   * Closes the given formula universally
   * @param f the formula to be closed
   * @return forall x_1 ... forall x_n f, where {x_i | 1 <= i <= n} = FV(f)
   */
  def apply( f: HOLFormula ): HOLFormula = freeVariables( f ).foldRight( f )( ( v, g ) => All( v, g ) )

  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[HOLFormula] ).asInstanceOf[FOLFormula]
}

object existsclosure {
  /**
   * Closes the given formula existentially
   * @param f the formula to be closed
   * @return exists x_1 ... exists x_n f, where {x_i | 1 <= i <= n} = FV(f)
   */
  def apply( f: HOLFormula ): HOLFormula = freeVariables( f ).foldRight( f )( ( v, g ) => Ex( v, g ) )

  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[HOLFormula] ).asInstanceOf[FOLFormula]

  def apply( seq: HOLSequent ): HOLSequent = seq.map( univclosure( _ ), existsclosure( _ ) )
}

/**
 * Dualize a formula in NNF by switching conjunctions with disjunctions,
 * universal with existential quantifiers, top with bottom and positive literals
 * with negative literals. The formula dualize( A ) is logically equivalent to
 * the negation of A.
 */
object dualize {
  def apply( f: HOLFormula ): HOLFormula = f match {
    case Top()                     => Bottom()
    case Bottom()                  => Top()
    case HOLAtom( x, args )        => Neg( HOLAtom( x, args ) )
    case Neg( HOLAtom( x, args ) ) => HOLAtom( x, args )
    case And( f1, f2 )             => Or( apply( f1 ), apply( f2 ) )
    case Or( f1, f2 )              => And( apply( f1 ), apply( f2 ) )
    case All( v, f )               => Ex( v, apply( f ) )
    case Ex( v, f )                => All( v, apply( f ) )
    case _                         => throw new Exception( "Formula not in NNF!" )
  }

  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[HOLFormula] ).asInstanceOf[FOLFormula]
}

object removeQuantifiers {
  /**
   * Removes the outermost block of quantifiers from a formula f.
   * @param f the formula of the form Qx1.Qx2. ... .Qxn.F[x1,...xn] where F is quantifier free. (n may be 0)
   * @return the stripped formula F[x1,...,xn]
   */
  def apply( f: HOLFormula ): HOLFormula = {
    f match {
      case Top() | Bottom() |
        HOLAtom( _, _ ) |
        Imp( _, _ ) |
        And( _, _ ) |
        Or( _, _ ) |
        Neg( _ ) => f
      case Ex( x, f0 )  => apply( f0 )
      case All( x, f0 ) => apply( f0 )
      case _            => throw new Exception( "ERROR: Unexpected case while extracting the matrix of a formula." )
    }
  }
  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[HOLFormula] ).asInstanceOf[FOLFormula]

  /**
   * Removes the leading n quantifiers of a formula.
   * It's only well-defined for formulas that begin with at least n quantifiers.
   *
   * @param formula A Formula
   * @param n Number of quantifiers to be removed
   * @throws exception in case f does not start with n quantifiers.
   * @return form without the first n quantifiers
   */
  def apply( f: HOLFormula, n: Int ): HOLFormula =
    if ( n == 0 )
      f
    else f match {
      case All( _, g ) => apply( g, n - 1 )
      case Ex( _, g )  => apply( g, n - 1 )
      case _           => throw new Exception( "Trying to remove too many quantifiers!" )
    }
}

object removeAllQuantifiers {
  /**
   * Removes all quantifiers from the logical level of a HOLFormula. Atoms are not changed.
   */
  def apply( f: HOLFormula ): HOLFormula = f match {
    case HOLAtom( _, _ ) | Top() | Bottom() => f
    case Neg( f1 )                          => Neg( apply( f1 ) )
    case Imp( f1, f2 )                      => Imp( apply( f1 ), apply( f2 ) )
    case And( f1, f2 )                      => And( apply( f1 ), apply( f2 ) )
    case Or( f1, f2 )                       => Or( apply( f1 ), apply( f2 ) )
    case Ex( x, f1 )                        => apply( f1 )
    case All( x, f1 )                       => apply( f1 )
  }
  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[HOLFormula] ).asInstanceOf[FOLFormula]
}

/**
 * Instantiates a formula with terms.
 */
object instantiate {
  /**
   * Instantiate a formula with a term by replacing the first quantifier
   */
  def apply( f: HOLFormula, t: LambdaExpression ): HOLFormula = f match {
    case All( v, form ) =>
      val sub = Substitution( v, t )
      sub( form )
    case Ex( v, form ) =>
      val sub = Substitution( v, t )
      sub( form )
    case _ => throw new Exception( "ERROR: trying to replace variables in a formula without quantifier." )
  }

  /**
   * Instantiates the initial quantifiers of a formula with the given list of terms
   */
  def apply( f: HOLFormula, ts: Seq[LambdaExpression] ): HOLFormula = ts match {
    case Nil     => f
    case t :: ts => instantiate( instantiate( f, t ), ts )
  }

  /**
   * If f is a formula \forall x_1 ... x_n G, and lst is a list of lists of terms
   * such that each list has length <= n, this function returns the list
   * of instances of f obtained by calling instantiate on each list of terms.
   */
  def apply( f: HOLFormula, tss: Seq[Seq[LambdaExpression]] )( implicit d: DummyImplicit ): Seq[HOLFormula] =
    tss.map( ts => instantiate( f, ts ) )

  def apply( f: FOLFormula, t: FOLTerm ): FOLFormula = apply( f.asInstanceOf[HOLFormula], t.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLFormula]
  def apply( f: FOLFormula, ts: Seq[FOLTerm] ): FOLFormula = apply( f.asInstanceOf[HOLFormula], ts.asInstanceOf[Seq[LambdaExpression]] ).asInstanceOf[FOLFormula]
  def apply( f: FOLFormula, tss: Seq[Seq[FOLTerm]] ): Seq[FOLFormula] = apply( f.asInstanceOf[HOLFormula], tss.asInstanceOf[Seq[Seq[FOLTerm]]] ).asInstanceOf[Seq[FOLFormula]]

  /**
   * Compute all clauses obtainable from substituting terms from the given set for variables in the given clause.
   */
  def apply( cl: FOLClause, ts: Set[FOLTerm] ): Set[FOLClause] = {
    val vars = freeVariables( cl )
    val mappings = vars.foldLeft( Set( Map[FOLVar, FOLTerm]() ) )( ( ms, x ) => {
      for { m <- ms; t <- ts } yield m + ( x -> t )
    } )
    mappings.map( m => { FOLSubstitution( m )( cl ) } ).asInstanceOf[Set[FOLClause]] //TODO: get rid of this cast (see issue 425)
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
   * Systematically renames the free variables by their left-to-right occurence in a HOL Formula f to x_{i} where all
   * x_{i} are different from the names of all bound variables in the term. I.e. reversing the substitution yields
   * the syntactically same formula.
   *
   * @param f the formula to be normalized
   * @return a pair (g,sub) such that g = sub(f). reversing sub allows to restore the original variables.
   */
  def apply( f: HOLFormula ): ( HOLFormula, Substitution ) = apply( f.asInstanceOf[LambdaExpression] ).asInstanceOf[( HOLFormula, Substitution )]

  /**
   * Systematically renames the free variables by their left-to-right occurence in a HOL Expression f to x_{i} where all
   * x_{i} are different from the names of all bound variables in the term. I.e. reversing the substitution yields
   * the syntactically same formula.
   *
   * @param f the expression to be normalized
   * @return a pair (g,sub) such that g = sub(f). reversing sub allows to restore the original variables.
   */
  def apply( f: LambdaExpression ): ( LambdaExpression, Substitution ) = {
    var i = 0
    //generate a blacklist that prevents renaming of bound variables
    val blacklist = LambdaPosition.getPositions( f ).flatMap( f( _ ) match {
      case All( x, _ ) => List( x.sym.toString )
      case Ex( x, _ )  => List( x.sym.toString )
      case _           => Nil
    } )

    apply( f, () => {
      var name = "x_{" + i + "}"
      do {
        i = i + 1;
        name = "x_{" + i + "}"
      } while ( blacklist.contains( name ) )
      name
    } )
  }

  /**
   * Works exactly like normalizeFreeVaribles(f:Formula) but allows the specification of your own name generator.
   * Please note that such a normalized formula is still only unique up to alpha equality. Compare for example
   * (all y P(x,y)) with (all x_{0} P(x,x_{0}):
   * the first normalizes to (all y P(x_{0},y whereas the second normalizes to (all x_{0}1 P(x_{0},x_{0}1).
   *
   * @param f the formula to be normalized
   * @param freshName a function which generates a fresh name every call.
   * @return a pair (g,sub) such that g = sub(f). reversing sub allows to restore the original variables.
   */
  def apply( f: HOLFormula, freshName: () => String ): ( HOLFormula, Substitution ) =
    apply( f.asInstanceOf[LambdaExpression], freshName ).asInstanceOf[( HOLFormula, Substitution )]

  /**
   * Works exactly like normalizeFreeVaribles(f:LambdaExpression) but allows the specification of your own name generator.
   * Please note that such a normalized formula is still only unique up to alpha equality. Compare for example
   * (all y P(x,y)) with (all x_{0} P(x,x_{0}):
   * the first normalizes to (all y P(x_{0},y) whereas the second normalizes to (all x_{0}1 P(x_{0},x_{0}1)).
   *
   * @param f the formula to be normalized
   * @param freshName a function which generates a fresh name every call.
   * @return a pair (g,sub) such that g = sub(f). reversing sub allows to restore the original variables.
   */
  def apply( f: LambdaExpression, freshName: () => String ): ( LambdaExpression, Substitution ) = {
    val vs = freeVariables( f )
    val map = vs.foldLeft( Map[Var, Var]() )( ( map, v ) => {
      if ( map.contains( v ) ) map else {
        val name = freshName()
        map + ( ( v, Var( name, v.exptype ) ) )
      }
    } )

    val sub = Substitution( map )
    ( sub( f ), sub )
  }
}

/**
 * Removes top-level connectives from a formula.
 */
object prenexify {
  /**
   * Returns a sequent that is equivalent to :- formula.
   */
  def pos( formula: HOLFormula ): HOLSequent = formula match {
    case Or( a, b )  => pos( a ) ++ pos( b )
    case Imp( a, b ) => neg( a ) ++ pos( b )
    case Neg( a )    => neg( a )
    case _           => Sequent() :+ formula
  }
  /**
   * Returns a sequent that is equivalent to formula :-.
   */
  def neg( formula: HOLFormula ): HOLSequent = formula match {
    case And( a, b ) => neg( a ) ++ neg( b )
    case Neg( a )    => pos( a )
    case _           => formula +: Sequent()
  }
}
