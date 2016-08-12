package at.logic.gapt

import at.logic.gapt.formats.babel.BabelSignature
import at.logic.gapt.proofs.{ FOLClause, FOLSequent, HOLClause, HOLSequent, Sequent }
import at.logic.gapt.utils.{ NameGenerator, Not }

import scala.annotation.implicitNotFound

package object expr extends DefaultReplaceables {

  /**
   * Trait that describes the following relation between types `S`, `T`, `U`: If a substitution of type `S` is applied
   * to an element of type `T`, the result will have type `U`.
   *
   * @tparam S A subtype of Substitution.
   * @tparam T The input type.
   * @tparam U The output type.
   */
  @implicitNotFound( "No implementation of type class Substitutable found for types ${S}, ${T}, ${U}." )
  trait Substitutable[-S <: Substitution, -T, +U] {
    /**
     * Applies a substitution to an argument.
     *
     * @param sub The substitution.
     * @param arg The argument.
     * @return The result.
     */
    def applySubstitution( sub: S, arg: T ): U
  }

  /**
   * The general method for applying substitutions to lambda expressions.
   *
   * @param sub A substitution.
   * @param t A lambda expression.
   * @return The substituted lambda expression.
   */
  private def applySub( sub: Substitution, t: LambdaExpression ): LambdaExpression = t match {
    case v: Var                               => sub.map.getOrElse( v, v )
    case c: Const                             => c
    case App( a, b )                          => App( applySub( sub, a ), applySub( sub, b ) )
    case Abs( v, s ) if sub.domain contains v => applySub( Substitution( sub.map - v ), t )
    case Abs( v, s ) if sub.range contains v =>
      // It is safe to rename the bound variable to any variable that is not in freeVariables(s).
      val newV = rename( v, freeVariables( s ) union sub.range )
      applySub( sub, Abs( newV, applySub( Substitution( v -> newV ), s ) ) )
    case Abs( v, s ) => Abs( v, applySub( sub, s ) )
  }

  // Type aliases that assert that a type `T` is closed under Substitution and FOLSubstitution, respectively.
  type ClosedUnderSub[T] = Substitutable[Substitution, T, T]
  type ClosedUnderFOLSub[T] = Substitutable[FOLSubstitution, T, T]

  /**
   * Testifies that a Set of substitutable objects is itself substitutable (by mapping over it).
   *
   * @param ev
   * @tparam S
   * @tparam T
   * @tparam U
   * @return
   */
  implicit def SubstitutableSet[S <: Substitution, T, U]( implicit ev: Substitutable[S, T, U] ): Substitutable[S, Set[T], Set[U]] = new Substitutable[S, Set[T], Set[U]] {
    override def applySubstitution( sub: S, set: Set[T] ): Set[U] = set.map( ev.applySubstitution( sub, _ ) )
  }

  /**
   * Testifies that a Seq of substitutable objects is itself substitutable (by mapping over it).
   *
   * @param ev
   * @tparam S
   * @tparam T
   * @tparam U
   * @return
   */
  implicit def SubstitutableSeq[S <: Substitution, T, U]( implicit ev: Substitutable[S, T, U] ): Substitutable[S, Seq[T], Seq[U]] = new Substitutable[S, Seq[T], Seq[U]] {
    override def applySubstitution( sub: S, seq: Seq[T] ): Seq[U] = seq.map( ev.applySubstitution( sub, _ ) )
  }

  /**
   * Testifies that an Option of substitutable objects is itself substitutable (by mapping over it).
   */
  implicit def SubstitutableOption[S <: Substitution, T, U]( implicit ev: Substitutable[S, T, U] ): Substitutable[S, Option[T], Option[U]] = new Substitutable[S, Option[T], Option[U]] {
    override def applySubstitution( sub: S, option: Option[T] ): Option[U] = option map { ev.applySubstitution( sub, _ ) }
  }

  /**
   * Testifies that a Sequent of substitutable objects is itself substitutable (by mapping over it).
   *
   * @param ev
   * @tparam S
   * @tparam T
   * @tparam U
   * @return
   */
  implicit def SubstitutableSequent[S <: Substitution, T, U]( implicit ev: Substitutable[S, T, U] ): Substitutable[S, Sequent[T], Sequent[U]] = new Substitutable[S, Sequent[T], Sequent[U]] {
    override def applySubstitution( sub: S, sequent: Sequent[T] ): Sequent[U] = sequent map { ev.applySubstitution( sub, _ ) }
  }

  /**
   * Testifies that a pair of substitutable objects is substitutable (by applying the substitution to each element).
   */
  implicit def SubstitutablePair[S <: Substitution, T1, U1, T2, U2](
    implicit
    ev1: Substitutable[S, T1, U1],
    ev2: Substitutable[S, T2, U2]
  ): Substitutable[S, ( T1, T2 ), ( U1, U2 )] = new Substitutable[S, ( T1, T2 ), ( U1, U2 )] {
    override def applySubstitution( sub: S, pair: ( T1, T2 ) ): ( U1, U2 ) = ( ev1.applySubstitution( sub, pair._1 ), ev2.applySubstitution( sub, pair._2 ) )
  }

  /**
   * Testifies that type `FOLTerm` is closed under `FOLSub`.
   *
   */
  implicit object FOLTermClosedUnderFOLSub extends ClosedUnderFOLSub[FOLTerm] {
    override def applySubstitution( sub: FOLSubstitution, x: FOLTerm ): FOLTerm = applySub( sub, x ).asInstanceOf[FOLTerm]
  }

  /**
   * Testifies that type `FOLAtom` is closed under `FOLSub`.
   *
   */
  implicit object FOLAtomClosedUnderFOLSub extends ClosedUnderFOLSub[FOLAtom] {
    override def applySubstitution( sub: FOLSubstitution, x: FOLAtom ): FOLAtom = applySub( sub, x ).asInstanceOf[FOLAtom]
  }

  /**
   * Testifies that applying a FOLSubstitution to a FOLFormula that is not an atom will result in a FOLFormula.
   *
   * @param notAnAtom Testifies that T is not a subtype of FOLAtom.
   * @tparam T
   * @return
   */
  implicit def FOLFormulaClosedUnderFOLSub[T <: FOLFormula]( implicit notAnAtom: Not[T <:< FOLAtom] ) = new Substitutable[FOLSubstitution, T, FOLFormula] {
    override def applySubstitution( sub: FOLSubstitution, x: T ): FOLFormula = applySub( sub, x ).asInstanceOf[FOLFormula]
  }

  /**
   * Testifies that applying a FOLSubstitution to a FOLExpression that is not a formula or a term will result in a FOLExpression.
   *
   * @param notATerm Testifies that T is not a subtype of FOLTerm.
   * @param notAFormula Testifies that T is not a subtype of FOLFormula.
   * @tparam T
   * @return
   */
  implicit def FOLExpressionClosedUnderFOLSub[T <: FOLExpression]( implicit notATerm: Not[T <:< FOLTerm], notAFormula: Not[T <:< FOLFormula] ) = new Substitutable[FOLSubstitution, T, FOLExpression] {
    override def applySubstitution( sub: FOLSubstitution, x: T ): FOLExpression = applySub( sub, x ).asInstanceOf[FOLExpression]
  }

  /**
   * Testifies that applying a FOLSubstitution to a HOLFormula that is not a FOLFormula will result in a HOLFormula.
   *
   * @param notAFOLFormula Testifies that T is not a subtype of FOLFormula.
   * @tparam T
   * @return
   */
  implicit def HOLFormulaClosedUnderFOLSub[T <: HOLFormula]( implicit notAFOLFormula: Not[T <:< FOLFormula] ) = new Substitutable[FOLSubstitution, T, HOLFormula] {
    override def applySubstitution( sub: FOLSubstitution, x: T ): HOLFormula = applySub( sub, x ).asInstanceOf[HOLFormula]
  }

  /**
   * Testifies that applying a non-FOL substitution to a FOLAtom results in a HOLAtom.
   * @param notAFOLSub Testifies that S is not a FOLSubstitution.
   * @tparam S
   * @return
   */
  implicit def FOLAtomSubstitutable[S <: Substitution]( implicit notAFOLSub: Not[S <:< FOLSubstitution] ) = new Substitutable[S, FOLAtom, HOLAtom] {
    override def applySubstitution( sub: S, x: FOLAtom ): HOLAtom = applySub( sub, x ).asInstanceOf[HOLAtom]
  }

  /**
   * Testifies that applying a Substitution that is not a FOLSubstitution to a HOLFormula will result in a HOLFormula.
   *
   * @param notAFOLSub Testifies that S is not a subtype of FOLSubstitution.
   * @tparam S
   * @return
   */
  implicit def HOLFormulaClosedUnderSub[S <: Substitution, T <: HOLFormula]( implicit notAFOLSub: Not[S <:< FOLSubstitution], notAFOLAtom: Not[T <:< FOLAtom] ) = new Substitutable[S, T, HOLFormula] {
    override def applySubstitution( sub: S, x: T ): HOLFormula = applySub( sub, x ).asInstanceOf[HOLFormula]
  }

  /**
   * Testifies that applying a Substitution that is not a FOLSubstitution to a FOLExpression will result in a LambdaExpression.
   *
   * @param notAFOLSub Testifies that S is not a subtype of FOLSubstitution.
   * @tparam S
   * @return
   */
  implicit def FOLExpressionSubstitutable[S <: Substitution, T <: FOLExpression]( implicit notAFOLSub: Not[S <:< FOLSubstitution], notAFOLAtom: Not[T <:< FOLAtom] ) = new Substitutable[S, T, LambdaExpression] {
    override def applySubstitution( sub: S, t: T ): LambdaExpression = applySub( sub, t )
  }

  /**
   * Testifies that applying a Substitution to a LambdaExpression that is not a FOLExpression or a HOLFormula will result in a LambdaExpression.
   *
   * @param notAFOLExpression Testifies that T is not a subtype of FOLExpression.
   * @param notAHOLFormula Testifies that T is not a subtype of HOLFormula.
   * @tparam T
   * @return
   */
  implicit def LambdaExpressionClosedUnderSub[T <: LambdaExpression]( implicit notAFOLExpression: Not[T <:< FOLExpression], notAHOLFormula: Not[T <:< HOLFormula] ) = new Substitutable[Substitution, T, LambdaExpression] {
    override def applySubstitution( sub: Substitution, t: T ): LambdaExpression = applySub( sub, t )
  }

  /**
   * Extension class that provides string interpolation functions for various expression types.
   *
   * @param sc A StringContext
   */
  implicit class ExpressionParseHelper( val sc: StringContext )( implicit file: sourcecode.File, line: sourcecode.Line, sig: BabelSignature ) {
    import at.logic.gapt.formats.babel._
    import scalaz.{ \/-, -\/ }

    private def interpolateHelper( args: Seq[LambdaExpression] ): ( String, ast.Expr => ast.Expr ) = {
      val strings = sc.parts.toList
      val expressions = args.toList

      val stringsNew = for ( ( s, i ) <- strings.init.zipWithIndex ) yield s ++ placeholder + i

      def repl( expr: ast.Expr ): ast.Expr = expr match {
        case ast.TypeAnnotation( e, ty ) => ast.TypeAnnotation( repl( e ), ty )
        case ast.Ident( name, ty ) if name startsWith placeholder =>
          val i = name.drop( placeholder.length ).toInt
          ast.LiftWhitebox( expressions( i ) )
        case expr: ast.Ident => expr
        case ast.Abs( v, sub ) =>
          repl( v ) match {
            case vNew @ ast.Ident( _, _ ) => // If repl(v) = v.
              ast.Abs( vNew, repl( sub ) )
            case ast.Lifted( Var( vNew, _ ), ty, _ ) => // If repl(v) = v'.
              ast.Abs( ast.Ident( vNew, ty ), repl( sub ) )
            case _ => // Otherwise
              throw new IllegalArgumentException( "Trying to substitute non-variable term in binding." )
          }
        case ast.App( a, b )  => ast.App( repl( a ), repl( b ) )
        case expr: ast.Lifted => expr
      }

      ( stringsNew.mkString ++ strings.last, repl )
    }

    private def interpolate( args: Seq[LambdaExpression], baseAstTransformer: ast.Expr => ast.Expr ): LambdaExpression = {
      val ( combined, repl ) = interpolateHelper( args )

      def astTransformer( expr: ast.Expr ): ast.Expr = baseAstTransformer( repl( expr ) )

      BabelParser.tryParse( combined, astTransformer ) match {
        case -\/( error ) => throw new IllegalArgumentException(
          s"Parse error at ${file.value}:${line.value}:\n${error.getMessage}"
        )
        case \/-( expr ) => expr
      }
    }

    // Higher order parsers

    /**
     * Parses a string as a [[LambdaExpression]].
     *
     */
    def le( args: LambdaExpression* ): LambdaExpression = interpolate( args, identity )

    /**
     * Parses a string as a [[HOLFormula]].
     *
     * @param args
     * @return
     */
    def hof( args: LambdaExpression* ): HOLFormula = interpolate( args, ast.TypeAnnotation( _, ast.Bool ) ).asInstanceOf[HOLFormula]

    /**
     * Parses a string as a [[HOLAtom]].
     *
     * @param args
     * @return
     */
    def hoa( args: LambdaExpression* ): HOLAtom = hof( args: _* ) match {
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
    def hov( args: LambdaExpression* ): Var = le( args: _* ) match {
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
    def hoc( args: LambdaExpression* ): Const = {
      import fastparse.core.ParseError
      import fastparse.core.Parsed._
      require( args.isEmpty )
      BabelParserCombinators.ConstAndNothingElse.parse( sc.parts.head ) match {
        case Success( c, _ ) => c
        case f: Failure =>
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
    def foe( args: FOLExpression* ): FOLExpression = le( args: _* ) match {
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
    def fof( args: FOLExpression* ): FOLFormula = hof( args: _* ) match {
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
    def foa( args: FOLExpression* ): FOLAtom = fof( args: _* ) match {
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
    def fot( args: FOLTerm* ): FOLTerm = le( args: _* ) match {
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
    def fov( args: FOLTerm* ): FOLVar = fot( args: _* ) match {
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
    def foc( args: FOLTerm* ): FOLConst = fot( args: _* ) match {
      case c: FOLConst => c
      case expr =>
        throw new IllegalArgumentException( s"Term $expr cannot be read as a FOL constant. Parse it with fot." )
    }

    /** Parses a string as a [[at.logic.gapt.proofs.HOLSequent]]. */
    def hos( args: LambdaExpression* ): HOLSequent = {
      val ( combined, repl ) = interpolateHelper( args )

      BabelParser.tryParseSequent( combined, e => ast.TypeAnnotation( repl( e ), ast.Bool ) ) match {
        case -\/( error ) => throw new IllegalArgumentException(
          s"Parse error at ${file.value}:${line.value}:\n${error.getMessage}"
        )
        case \/-( sequent ) => sequent.map( _.asInstanceOf[HOLFormula] )
      }
    }

    /** Parses a string as a [[at.logic.gapt.proofs.HOLClause]]. */
    def hcl( args: LambdaExpression* ): HOLClause = hos( args: _* ).map( _.asInstanceOf[HOLAtom] )

    /** Parses a string as a [[at.logic.gapt.proofs.FOLSequent]]. */
    def fos( args: LambdaExpression* ): FOLSequent = hos( args: _* ).map( _.asInstanceOf[FOLFormula] )

    /** Parses a string as a [[at.logic.gapt.proofs.FOLClause]]. */
    def fcl( args: LambdaExpression* ): FOLClause = hos( args: _* ).map( _.asInstanceOf[FOLAtom] )

    private def placeholder = "__qq_"
  }

  implicit class ExprNameGenerator( val nameGen: NameGenerator ) {
    def fresh( v: Var ): Var = Var( nameGen.fresh( v.name ), v.exptype )
    def fresh( v: FOLVar ): FOLVar = FOLVar( nameGen.fresh( v.name ) )
    def fresh( c: Const ): Const = Const( nameGen.fresh( c.name ), c.exptype )
    def fresh( c: FOLConst ): FOLConst = FOLConst( nameGen.fresh( c.name ) )
    def fresh( n: VarOrConst ): VarOrConst = n match {
      case v: Var   => fresh( v )
      case c: Const => fresh( c )
    }
  }
}
