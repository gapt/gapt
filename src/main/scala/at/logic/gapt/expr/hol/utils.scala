/*
 * Simple functions that operate on LambdaExpressions, Formulas and sequents.
 */

package at.logic.gapt.expr.hol

import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.expr._

object freeHOVariables {
  /**
   * Computes a list of all HOL Variables which are not of type i in a formula, including repetitions. Together with
   * checks on quantifiers, this can be used to decide if a formula has "true" higher-order content.
   * @param f the expressions to extract from
   * @return the list of free variables with type != Ti in e
   */
  def apply( f: HOLFormula ) = freeVariables( f ).filter( _ match { case Var( _, Ti ) => false; case _ => true } )
}

// matches for consts and vars, but nothing else
object VarOrConst {
  def unapply( e: LambdaExpression ): Option[( String, TA )] = e match {
    case Var( name, et )   => Some( ( name, et ) )
    case Const( name, et ) => Some( ( name, et ) )
    case _                 => None
  }
}

// Instantiates a term in a quantified formula (using the first quantifier).
object instantiate {
  def apply( f: HOLFormula, t: LambdaExpression ): HOLFormula = f match {
    case All( v, form ) =>
      val sub = Substitution( v, t )
      sub( form )
    case Ex( v, form ) =>
      val sub = Substitution( v, t )
      sub( form )
    case _ => throw new Exception( "ERROR: trying to replace variables in a formula without quantifier." )
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
 * True iff All or Ex is contained in the logical structure of e.
 * For example, P( (all x:x) ) contains a quantifier, but it is inside of an atom.
 */
object containsQuantifierOnLogicalLevel {
  def apply( e: LambdaExpression ): Boolean = e match {
    case Top() | Bottom()   => false
    case Var( x, tpe )      => false
    case Const( x, tpe )    => false
    case And( x, y )        => containsQuantifierOnLogicalLevel( x ) || containsQuantifierOnLogicalLevel( y )
    case Or( x, y )         => containsQuantifierOnLogicalLevel( x ) || containsQuantifierOnLogicalLevel( y )
    case Imp( x, y )        => containsQuantifierOnLogicalLevel( x ) || containsQuantifierOnLogicalLevel( y )
    case Neg( x )           => containsQuantifierOnLogicalLevel( x )
    case Ex( x, f )         => true
    case All( x, f )        => true
    // Is this really necessary? Yes, they handle cases like P( (\x.x) a ) .
    case HOLAtom( x, args ) => false // contents of atoms is ignored
    case Abs( v, exp )      => containsQuantifierOnLogicalLevel( exp )
    case App( l, r )        => containsQuantifierOnLogicalLevel( l ) || containsQuantifierOnLogicalLevel( r )
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

  def apply( s: FSequent ): Boolean =
    s.antecedent.exists( x => containsStrongQuantifier( x, false ) ) ||
      s.succedent.exists( x => containsStrongQuantifier( x, true ) )
}

object isPrenex {
  def apply( e: LambdaExpression ): Boolean = e match {
    case Top() | Bottom() => true
    case Var( _, _ )      => true
    case Const( _, _ )    => true
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

object isAtom {
  def apply( e: LambdaExpression ): Boolean = e match {
    case HOLAtom( _, _ ) => true
    case _               => false
  }
}

object subTerms {
  def apply( e: LambdaExpression ): List[LambdaExpression] = e match {
    case Top() | Bottom()       => List( e )
    case Var( _, _ )            => List( e )
    case Const( _, _ )          => List( e )
    case And( x, y )            => e +: ( subTerms( x ) ++ subTerms( y ) )
    case Or( x, y )             => e +: ( subTerms( x ) ++ subTerms( y ) )
    case Imp( x, y )            => e +: ( subTerms( x ) ++ subTerms( y ) )
    case Neg( x )               => e +: subTerms( x )
    case All( _, x )            => e +: subTerms( x )
    case Ex( _, x )             => e +: subTerms( x )
    case Abs( _, x )            => e +: subTerms( x )
    case App( x, y )            => e +: ( subTerms( x ) ++ subTerms( y ) )
    case HOLAtom( _, args )     => e +: args.flatMap( a => subTerms( a ) )
    case HOLFunction( _, args ) => e +: args.flatMap( a => subTerms( a ) )
    case _                      => throw new Exception( "Unrecognized symbol." )
  }
}

object isLogicalSymbol {
  def apply( e: LambdaExpression ): Boolean = e.isInstanceOf[LogicalConstant]
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

  def apply( seq: FSequent ): Int = seq.antecedent.foldLeft( 0 )( _ + lcomp( _ ) ) + seq.succedent.foldLeft( 0 )( _ + lcomp( _ ) )
}

/**
 * Returns the quantifier free part of a prenex formula
 */
object getMatrix {
  /**
   * Strips the outermost block of quantifiers from a formula f in prenex form. The result is also called the
   * matrix of f.
   * @param f the formula of the form Qx1.Qx2. ... .Qxn.F[x1,...xn] where F is quantifier free. (n may be 0)
   * @return the stripped formula F[x1,...,xn]
   */
  def apply( f: HOLFormula ): HOLFormula = {
    assert( isPrenex( f ) )
    f match {
      case Top() | Bottom() |
        Var( _, _ ) |
        Const( _, _ ) |
        HOLAtom( _, _ ) |
        Imp( _, _ ) |
        And( _, _ ) |
        Or( _, _ ) |
        Neg( _ ) => f
      case Ex( x, f0 )  => getMatrix( f0 )
      case All( x, f0 ) => getMatrix( f0 )
      case _            => throw new Exception( "ERROR: Unexpected case while extracting the matrix of a formula." )
    }
  }

  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[HOLFormula] ).asInstanceOf[FOLFormula]
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
   * the first normalizes to (all y P(x_{0},y whereas the second normalizes to (all x_{0}1 P(x_{0},x_{0}1).
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

object toAbbreviatedString {
  /**
   * This function takes a HOL construction and converts it to a abbreviated string version. The abbreviated string version is made
   * by replacing the code construction for logic symbols by string versions in the file language/hol/logicC.names.scala.
   * Several recursive function calls will be transformed into an abbreviated form (e.g. f(f(f(x))) => f^3^(x)).
   * Terms are also handled by the this function.
   * @param  e  The method has no parameters other then the object which is to be written as a string
   * @throws Exception This occurs when an unknown subformula is found when parsing the HOL construction
   * @return A String which contains the defined symbols in language/hol/logicC.names.scala.
   *
   */
  def apply( e: LambdaExpression ): String = {

    val p = pretty( e )

    val r: String = e match {
      case HOLFunction( x, args ) => {
        if ( p._1 != p._2 && p._2 != "tuple1" )
          if ( p._3 > 0 )
            return p._2 + "^" + ( p._3 + 1 ) + "(" + p._1 + ") : " + e.exptype
          else
            return p._1
        else
          return p._1
      }
      case _ => return p._1
    }

    return r
  }

  private def pretty( exp: LambdaExpression ): ( String, String, Int ) = {

    val s: ( String, String, Int ) = exp match {
      case null                => ( "null", "null", -2 )
      case Var( x, t )         => ( x.toString() + " : " + t.toString(), x.toString(), 0 )
      case And( x, y )         => ( "(" + toAbbreviatedString( x ) + " " + AndC.name + " " + toAbbreviatedString( y ) + ")", AndC.name, 0 )
      case Eq( x, y )          => ( "(" + toAbbreviatedString( x ) + " " + EqC.name + " " + toAbbreviatedString( y ) + ")", EqC.name, 0 )
      case Or( x, y )          => ( "(" + toAbbreviatedString( x ) + " " + OrC.name + " " + toAbbreviatedString( y ) + ")", OrC.name, 0 )
      case Imp( x, y )         => ( "(" + toAbbreviatedString( x ) + " " + ImpC.name + " " + toAbbreviatedString( y ) + ")", ImpC.name, 0 )
      case Neg( x )            => ( NegC.name + toAbbreviatedString( x ), NegC.name, 0 )
      case Ex( x, f )          => ( ExistsC.name + toAbbreviatedString( x ) + "." + toAbbreviatedString( f ), ExistsC.name, 0 )
      case All( x, f )         => ( ForallC.name + toAbbreviatedString( x ) + "." + toAbbreviatedString( f ), ForallC.name, 0 )
      case Abs( v, exp )       => ( "(λ" + toAbbreviatedString( v ) + "." + toAbbreviatedString( exp ) + ")", "λ", 0 )
      case App( l, r )         => ( "(" + toAbbreviatedString( l ) + ")(" + toAbbreviatedString( r ) + ")", "()()", 0 )
      case Const( x, exptype ) => ( x.toString(), x.toString(), 0 )
      case HOLAtom( x, args ) => {
        ( x.toString() + "(" + ( args.foldRight( "" ) {
          case ( x, "" )  => "" + toAbbreviatedString( x )
          case ( x, str ) => toAbbreviatedString( x ) + ", " + str
        } ) + ")" + " : o", x.toString(), 0 )
      }
      case HOLFunction( x, args ) => {
        // if only 1 argument is provided
        // check if abbreviating of recursive function calls is possible
        if ( args.length == 1 ) {
          val p = pretty( args.head )

          // current function is equal to first and ONLY argument
          if ( p._2 == x.toString() ) {
            // increment counter and return (<current-string>, <functionsymbol>, <counter>)
            return ( p._1, x.toString(), p._3 + 1 )
          } // function symbol has changed from next to this level
          else {

            // in case of multiple recursive function calls
            if ( p._3 > 0 ) {
              return ( p._2 + "^" + p._3 + "(" + p._1 + ") : " + exp.exptype.toString(), x.toString(), 0 )
            } // otherwise
            else {
              return ( p._1, x.toString(), 1 )
            }
          }
        } else {
          return ( x.toString() + "(" + ( args.foldRight( "" ) {
            case ( x, "" ) => toAbbreviatedString( x )
            case ( x, s )  => toAbbreviatedString( x ) + ", " + s
          } ) + ") : " + exp.exptype.toString(), x.toString(), 0 )
        }

      }
      case _ => throw new Exception( "ERROR: Unknown HOL expression." );
    }
    return s

  }

}
