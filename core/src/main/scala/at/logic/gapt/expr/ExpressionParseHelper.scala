package at.logic.gapt.expr

import at.logic.gapt.expr.ExpressionParseHelper.Splice
import at.logic.gapt.formats.babel._
import at.logic.gapt.proofs.{ FOLClause, FOLSequent, HOLClause, HOLSequent }
import fastparse.core.ParseError

object ExpressionParseHelper {
  abstract class Splice[+ForType] {
    def spliceIn: preExpr.Expr
  }
  implicit class IdentifierSplice[+T]( val ident: String ) extends Splice[T] {
    def spliceIn = preExpr.Ident( ident, preExpr.freshMetaType() )
  }
  implicit class ExpressionSplice[+ExprType <: LambdaExpression]( val expr: ExprType ) extends Splice[ExprType] {
    def spliceIn = preExpr.LiftWhitebox( expr )
  }
}

/**
 * Extension class that provides string interpolation functions for various expression types.
 *
 * @param sc A StringContext
 */
class ExpressionParseHelper( sc: StringContext, file: sourcecode.File, line: sourcecode.Line, sig: BabelSignature ) {
  private implicit def _sig = sig

  private def interpolateHelper( expressions: Seq[Splice[LambdaExpression]] ): ( String, preExpr.Expr => preExpr.Expr ) = {
    def repl( expr: preExpr.Expr ): preExpr.Expr = expr match {
      case preExpr.TypeAnnotation( e, ty ) => preExpr.TypeAnnotation( repl( e ), ty )
      case preExpr.Ident( name, ty ) if name startsWith placeholder =>
        val i = name.drop( placeholder.length ).toInt
        expressions( i ).spliceIn
      case expr: preExpr.Ident => expr
      case preExpr.Abs( v, sub ) =>
        repl( v ) match {
          case vNew @ preExpr.Ident( _, _ ) => // If repl(v) = v.
            preExpr.Abs( vNew, repl( sub ) )
          case preExpr.Lifted( Var( vNew, _ ), ty, _ ) => // If repl(v) = v'.
            preExpr.Abs( preExpr.Ident( vNew, ty ), repl( sub ) )
          case _ => // Otherwise
            throw new IllegalArgumentException( "Trying to substitute non-variable term in binding." )
        }
      case preExpr.App( a, b )  => preExpr.App( repl( a ), repl( b ) )
      case expr: preExpr.Lifted => expr
    }

    ( sc.parts.init.zipWithIndex.map { case ( s, i ) => s ++ placeholder + i }.mkString ++ sc.parts.last, repl )
  }

  private def interpolate( args: Seq[Splice[LambdaExpression]], baseAstTransformer: preExpr.Expr => preExpr.Expr ): LambdaExpression = {
    val ( combined, repl ) = interpolateHelper( args )

    def astTransformer( expr: preExpr.Expr ): preExpr.Expr = baseAstTransformer( repl( expr ) )

    BabelParser.tryParse( combined, astTransformer ) match {
      case Left( error ) => throw new IllegalArgumentException(
        s"Parse error at ${file.value}:${line.value}:\n${error.getMessage}"
      )
      case Right( expr ) => expr
    }
  }

  // Higher order parsers

  /**
   * Parses a string as a [[LambdaExpression]].
   *
   */
  def le( args: Splice[LambdaExpression]* ): LambdaExpression = interpolate( args, identity )

  /**
   * Parses a string as a [[HOLFormula]].
   *
   * @param args
   * @return
   */
  def hof( args: Splice[LambdaExpression]* ): HOLFormula = interpolate( args, preExpr.TypeAnnotation( _, preExpr.Bool ) ).asInstanceOf[HOLFormula]

  /**
   * Parses a string as a [[HOLAtom]].
   *
   * @param args
   * @return
   */
  def hoa( args: Splice[LambdaExpression]* ): HOLAtom = hof( args: _* ) match {
    case atom: HOLAtom => atom
    case expr =>
      throw new IllegalArgumentException( s"Expression $expr appears not to be a HOL atom. Parse it with hof." )
  }

  /**
   * Parses a string as a [[Var]].
   *
   * @param args
   * @return
   */
  def hov( args: Splice[LambdaExpression]* ): Var = le( args: _* ) match {
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
  def hoc( args: Splice[LambdaExpression]* ): Const = {
    import fastparse.all.Parsed._
    require( args.isEmpty )
    BabelParserCombinators.ConstAndNothingElse.parse( sc.parts.head ) match {
      case Success( c, _ ) => c
      case f @ Failure( _, _, _ ) =>
        throw new IllegalArgumentException(
          s"Cannot parse constant at ${file.value}:${line.value}:\n${ParseError( f ).getMessage}"
        )
    }
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
  def fov( args: Splice[FOLTerm]* ): FOLVar = fot( args: _* ) match {
    case v: FOLVar => v
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
  def hos( args: Splice[LambdaExpression]* ): HOLSequent = {
    val ( combined, repl ) = interpolateHelper( args )

    BabelParser.tryParseSequent( combined, e => preExpr.TypeAnnotation( repl( e ), preExpr.Bool ) ) match {
      case Left( error ) => throw new IllegalArgumentException(
        s"Parse error at ${file.value}:${line.value}:\n${error.getMessage}"
      )
      case Right( sequent ) => sequent.map( _.asInstanceOf[HOLFormula] )
    }
  }

  /** Parses a string as a [[at.logic.gapt.proofs.HOLClause]]. */
  def hcl( args: Splice[LambdaExpression]* ): HOLClause = hos( args: _* ).map( _.asInstanceOf[HOLAtom] )

  /** Parses a string as a [[at.logic.gapt.proofs.FOLSequent]]. */
  def fos( args: Splice[LambdaExpression]* ): FOLSequent = hos( args: _* ).map( _.asInstanceOf[FOLFormula] )

  /** Parses a string as a [[at.logic.gapt.proofs.FOLClause]]. */
  def fcl( args: Splice[LambdaExpression]* ): FOLClause = hos( args: _* ).map( _.asInstanceOf[FOLAtom] )

  private def placeholder = "__qq_"
}
