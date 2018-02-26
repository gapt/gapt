package at.logic.gapt.expr

import at.logic.gapt.expr.ExpressionParseHelper.Splice
import at.logic.gapt.formats.babel._
import at.logic.gapt.proofs.{ FOLClause, FOLSequent, HOLClause, HOLSequent, Sequent }

object ExpressionParseHelper {
  abstract class Splice[+ForType] {
    def spliceIn: preExpr.Expr
  }
  implicit class IdentifierSplice[+T]( val ident: String ) extends Splice[T] {
    def spliceIn = preExpr.Ident( ident, preExpr.freshMetaType(), None )
  }
  implicit class ExpressionSplice[+ExprType <: Expr]( val expr: ExprType ) extends Splice[ExprType] {
    def spliceIn = preExpr.QuoteWhitebox( expr )
  }
}

/**
 * Extension class that provides string interpolation functions for various expression types.
 *
 * @param sc A StringContext
 */
class ExpressionParseHelper( sc: StringContext, file: sourcecode.File, line: sourcecode.Line, sig: BabelSignature ) {
  private implicit def _sig = sig

  private def interpolateHelper( expressions: Seq[Splice[Expr]] ): ( String, preExpr.Expr => preExpr.Expr ) = {
    def repls( name: String ): preExpr.Expr =
      expressions( name.drop( placeholder.length ).toInt ).spliceIn
    def repl( expr: preExpr.Expr ): preExpr.Expr = expr match {
      case preExpr.LocAnnotation( e, loc )                            => preExpr.LocAnnotation( repl( e ), loc )
      case preExpr.TypeAnnotation( e, ty )                            => preExpr.TypeAnnotation( repl( e ), ty )
      case preExpr.Ident( name, _, _ ) if name startsWith placeholder => repls( name )
      case expr: preExpr.Ident                                        => expr
      case preExpr.Abs( v, sub ) =>
        repl( v ) match {
          case vNew @ preExpr.Ident( _, _, _ ) => // If repl(v) = v.
            preExpr.Abs( vNew, repl( sub ) )
          case preExpr.Quoted( Var( vNew, _ ), ty, _ ) => // If repl(v) = v'.
            preExpr.Abs( preExpr.Ident( vNew, ty, None ), repl( sub ) )
          case _ => // Otherwise
            throw new IllegalArgumentException( "Trying to substitute non-variable term in binding." )
        }
      case preExpr.App( a, b )  => preExpr.App( repl( a ), repl( b ) )
      case expr: preExpr.Quoted => expr
      case preExpr.FlatOps( children ) => preExpr.FlatOps( children.map {
        case Left( ( n, loc ) ) if n.startsWith( placeholder ) => Right( preExpr.LocAnnotation( repls( n ), loc ) )
        case tok @ Left( _ )                                   => tok
        case Right( e )                                        => Right( repl( e ) )
      } )
    }

    ( sc.parts.init.zipWithIndex.map { case ( s, i ) => s + " " + placeholder + i + " " }.mkString ++ sc.parts.last, repl )
  }

  private def interpolate( args: Seq[Splice[Expr]], baseAstTransformer: preExpr.Expr => preExpr.Expr ): Expr = {
    val ( combined, repl ) = interpolateHelper( args )

    def astTransformer( expr: preExpr.Expr ): preExpr.Expr = baseAstTransformer( repl( expr ) )

    BabelParser.tryParse( combined, astTransformer ) match {
      case Left( error ) => throw new IllegalArgumentException(
        s"Parse error at ${file.value}:${line.value}:\n${error.getMessage}" )
      case Right( expr ) => expr
    }
  }

  def ty( args: Nothing* ): Ty =
    BabelParser.tryParseType( sc.parts.mkString ) match {
      case Left( error ) => throw new IllegalArgumentException(
        s"Parse error at ${file.value}:${line.value}:\n${error.getMessage}" )
      case Right( ty ) => ty
    }

  // Higher order parsers

  /**
   * Parses a string as a [[Expr]].
   *
   */
  def le( args: Splice[Expr]* ): Expr = interpolate( args, identity )

  /**
   * Parses a string as a [[Formula]].
   *
   * @param args
   * @return
   */
  def hof( args: Splice[Expr]* ): Formula = interpolate( args, preExpr.TypeAnnotation( _, preExpr.Bool ) ).asInstanceOf[Formula]

  /**
   * Parses a string as a [[Atom]].
   *
   * @param args
   * @return
   */
  def hoa( args: Splice[Expr]* ): Atom = hof( args: _* ) match {
    case atom: Atom => atom
    case expr =>
      throw new IllegalArgumentException( s"Expression $expr appears not to be a HOL atom. Parse it with hof." )
  }

  /**
   * Parses a string as a [[Var]].
   *
   * @param args
   * @return
   */
  def hov( args: Splice[Expr]* ): Var = le( args: _* ) match {
    case v: Var => v
    case expr =>
      throw new IllegalArgumentException( s"Expression $expr cannot be read as a variable. Parse it with le." )
  }

  /**
   * Parses a string as a [[Const]].
   *
   * @param args
   * @return
   */
  def hoc( args: Splice[Expr]* ): Const = le( args: _* ) match {
    case c: Const    => c
    case Var( n, t ) => Const( n, t )
    case expr =>
      throw new IllegalArgumentException( s"Expression $expr cannot be read as a constant. Parse it with le." )
  }

  // First order parsers

  /**
   * Parses a string as a [[FOLExpression]].
   *
   * @param args
   * @return
   */
  def foe( args: Splice[FOLExpression]* ): FOLExpression = le( args: _* ) match {
    case folExpression: FOLExpression => folExpression
    case expr =>
      throw new IllegalArgumentException( s"Expression $expr appears not to be a FOL expression. Parse it with le." )
  }

  /**
   * Parses a string as a [[FOLFormula]].
   *
   * @param args
   * @return
   */
  def fof( args: Splice[FOLExpression]* ): FOLFormula = hof( args: _* ) match {
    case formula: FOLFormula => formula
    case expr =>
      throw new IllegalArgumentException( s"Formula $expr appears not to be a FOL formula. Parse it with hof." )
  }

  /**
   * Parses a string as a [[FOLAtom]].
   *
   * @param args
   * @return
   */
  def foa( args: Splice[FOLExpression]* ): FOLAtom = fof( args: _* ) match {
    case atom: FOLAtom => atom
    case expr =>
      throw new IllegalArgumentException( s"Formula $expr appears not to be an atom. Parse it with fof." )
  }

  /**
   * Parses a string as a [[FOLTerm]].
   *
   * @param args
   * @return
   */
  def fot( args: Splice[FOLTerm]* ): FOLTerm = le( args: _* ) match {
    case term: FOLTerm => term
    case expr =>
      throw new IllegalArgumentException( s"Expression $expr appears not to be FOL term. Parse it with le." )
  }

  /**
   * Parses a string as a [[FOLVar]].
   *
   * @param args
   * @return
   */
  def fov( args: Splice[FOLTerm]* ): FOLVar = le( args: _* ) match {
    case Var( n, _ ) => FOLVar( n )
    case expr =>
      throw new IllegalArgumentException( s"Term $expr cannot be read as a FOL variable. Parse it with fot." )
  }

  /**
   * Parses a string as a [[FOLConst]].
   *
   * @param args
   * @return
   */
  def foc( args: Splice[FOLTerm]* ): FOLConst = fot( args: _* ) match {
    case c: FOLConst => c
    case expr =>
      throw new IllegalArgumentException( s"Term $expr cannot be read as a FOL constant. Parse it with fot." )
  }

  /** Parses a string as a [[at.logic.gapt.proofs.HOLSequent]]. */
  def hos( args: Splice[Expr]* ): HOLSequent = {
    val ( combined, repl ) = interpolateHelper( args )

    BabelParser.tryParseSequent( combined, e => preExpr.TypeAnnotation( repl( e ), preExpr.Bool ) ) match {
      case Left( error ) => throw new IllegalArgumentException(
        s"Parse error at ${file.value}:${line.value}:\n${error.getMessage}" )
      case Right( sequent ) => sequent.map( _.asInstanceOf[Formula] )
    }
  }

  /** Parses a string as a labelled sequent. */
  def hols( args: Splice[Expr]* ): Sequent[( String, Formula )] = {
    val ( combined, repl ) = interpolateHelper( args )

    BabelParser.tryParseLabelledSequent( combined, repl ) match {
      case Left( error ) => throw new IllegalArgumentException(
        s"Parse error at ${file.value}:${line.value}:\n${error.getMessage}" )
      case Right( sequent ) => sequent
    }
  }

  /** Parses a string as a [[at.logic.gapt.proofs.HOLClause]]. */
  def hcl( args: Splice[Expr]* ): HOLClause = hos( args: _* ).map( _.asInstanceOf[Atom] )

  /** Parses a string as a [[at.logic.gapt.proofs.FOLSequent]]. */
  def fos( args: Splice[Expr]* ): FOLSequent = hos( args: _* ).map( _.asInstanceOf[FOLFormula] )

  /** Parses a string as a [[at.logic.gapt.proofs.FOLClause]]. */
  def fcl( args: Splice[Expr]* ): FOLClause = hos( args: _* ).map( _.asInstanceOf[FOLAtom] )

  private def placeholder = "__qq_"
}
