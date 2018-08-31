package gapt.proofs.context.update

import gapt.expr.Abs
import gapt.expr.App
import gapt.expr.Apps
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.FunctionType
import gapt.expr.ReductionRule
import gapt.expr.TBase
import gapt.expr.TVar
import gapt.expr.Var
import gapt.expr.fol.folSubTerms
import gapt.expr.typeVariables
import gapt.proofs.context.Context
import gapt.proofs.context.Context.parseDefinitionalEquations
import gapt.proofs.context.State
import gapt.proofs.context.facet.Constants
import gapt.proofs.context.facet.Reductions
import gapt.proofs.context.facet.StructurallyInductiveTypes
import gapt.proofs.context.update.{ ConstantDeclaration => ConstDecl }
import gapt.utils.linearizeStrictPartialOrder

case class PrimitiveRecursiveFunction(
    c:         Const,
    nArgs:     Int,
    recIdx:    Int,
    equations: Vector[( Expr, Expr )] ) extends Update {

  PrimitiveRecursiveFunctionValidator.validate( this )

  private val Const( _, FunctionType( _, argTypes ), _ ) = c

  val recursionType: TBase = argTypes( recIdx ).asInstanceOf[TBase]

  /**
   * Adds this primitive recursive function definition to a context.
   *
   * @param ctx The context to which this function definition is to be added.
   * @return Returns the new context state resulting from the addition of
   * this function definition to the current state of `ctx`. An exception is
   * thrown if number of equations does not equal the number of constructors
   * of the recursion type, or if the order of the equations does not
   * correspond to the order of constructors of the recursion type.
   */
  override def apply( ctx: Context ): State = {
    val ctx_ = ctx + c
    val ctrs =
      ctx.get[StructurallyInductiveTypes].constructors( recursionType.name )
    require( equations.size == ctrs.size )
    for ( ( ( lhs @ Apps( _, lhsArgs ), rhs ), ctr ) <- equations.zip( ctrs ) ) {
      ctx_.check( lhs )
      ctx_.check( rhs )
      val Apps( Const( ctr_, _, _ ), _ ) = lhsArgs( recIdx )
      require( ctr_ == ctr.name )
    }
    ctx.state.update[Constants]( _ + c )
      .update[Reductions]( _ ++ equations.map( ReductionRule.apply ) )
  }
}

object PrimitiveRecursiveFunctionValidator {

  private type Equation = ( Expr, Expr )

  /**
   * Checks whether the given definition is syntactically well-formed.
   *
   * @param input The definition to be checked.
   * @return Returns unit if the definition is well-formed, otherwise
   *         an exception is thrown.
   */
  def validate( input: PrimitiveRecursiveFunction ): Unit = {

    val PrimitiveRecursiveFunction( c, nArgs, recIdx, equations ) = input
    val typeVars: Set[TVar] = typeVariables( c.ty )
    val Const( name, FunctionType( _, argTypes ), _ ) = c

    require( 0 <= recIdx && recIdx < nArgs && nArgs <= argTypes.size )

    def validateEquation( input: Equation ): Unit = {

      val ( lhs, rhs ) = input

      require( lhs.ty == rhs.ty )
      require( typeVariables( lhs.ty ) subsetOf typeVars )
      require( typeVariables( rhs.ty ) subsetOf typeVars )

      val Apps( `c`, lhsArgs ) = lhs
      require( lhsArgs.size == nArgs )

      val nonRecLhsArgs =
        lhsArgs.zipWithIndex.filter( _._2 != recIdx ).map( _._1 )
      val Apps( Const( _, _, _ ), ctrArgs ) = lhsArgs( recIdx )

      val matchVars = nonRecLhsArgs ++ ctrArgs

      matchVars.foreach( a => { require( a.isInstanceOf[Var] ) } )
      require( matchVars == matchVars.distinct )

      folSubTerms( rhs ).foreach {
        case Apps( fn @ Const( `name`, _, _ ), args ) =>
          require( fn == c )
          require( ctrArgs.contains( args( recIdx ) ) )
        case _ =>
      }
    }

    for ( equation <- equations ) {
      validateEquation( equation )
    }
  }
}

object PrimitiveRecursiveFunction {

  /**
   * Constructs a primitive recursive function definition.
   *
   * @param c The constant that is to be defined primitive recursively.
   * @param equations Oriented equations that define the constant c by
   * primitive recursion.
   * @param ctx The context in which the constant is to be defined.
   * @return A primitive function definition if `c` and `euqations` represent
   * a valid primitive function definition in the context `ctx`.
   */
  def apply(
    constant:  Const,
    equations: Iterable[( Expr, Expr )] )(
    implicit
    ctx: Context ): PrimitiveRecursiveFunction = {

    val ( arity, recIdx ) = equations.head._1 match {
      case Apps( _, args ) =>
        args.size -> args.indexWhere( !_.isInstanceOf[Var] )
    }

    val Const( _, FunctionType( _, argTys ), _ ) = constant
    val equationsByConst = equations.groupBy {
      case ( ( Apps( _, args ), _ ) ) =>
        val Apps( ctr, _ ) = args( recIdx )
        ctr
    }
    val Some( recCtrs ) = ctx.getConstructors( argTys( recIdx ) )

    PrimitiveRecursiveFunction(
      constant, arity, recIdx, recCtrs.map( equationsByConst( _ ).head ) )
  }

  /**
   * Constructs a primitive recursive function definition.
   *
   * @param c The constant that is to be defined primitive recursively.
   * @param equations Oriented equations that define the constant c by
   * primitive recursion.
   * @param ctx The context in which the constant is to be defined.
   * @return A primitive function definition if `c` and `euqations` represent
   * a valid primitive function definition in the context `ctx`.
   */
  def apply(
    c: Const, equations: String* )(
    implicit
    ctx: Context ): PrimitiveRecursiveFunction = {
    val temporaryContext = ctx + c
    apply( c, equations.map { parseDefinitionalEquations( c, _ )( temporaryContext ) } )
  }
}

case object PrimitiveRecursiveFunctions {

  def apply(
    rawDefinitions: Iterable[( Const, Iterable[( Expr, Expr )] )],
    dummy:          Unit                                          = Unit )(
    implicit
    ctx: Context ): Iterable[PrimitiveRecursiveFunction] = {

    val parsedDefinitions: Iterable[PrimitiveRecursiveFunction] =
      rawDefinitions.map {
        case ( const, equations ) =>
          PrimitiveRecursiveFunction( const, equations )
      }

    batch( parsedDefinitions )
  }

  def apply(
    rawDefinitions: Iterable[( Const, Seq[String] )] )(
    implicit
    ctx: Context ): Iterable[PrimitiveRecursiveFunction] = {

    val parsingContext = ctx ++ rawDefinitions.map { d => ConstDecl( d._1 ) }

    val parsedDefinitions: Iterable[PrimitiveRecursiveFunction] =
      rawDefinitions.map {
        case ( const, equations ) =>
          ( const, equations.map { parseDefinitionalEquations( const, _ )( parsingContext ) } )
      }.map {
        case ( const, equations ) =>
          PrimitiveRecursiveFunction( const, equations )
      }

    batch( parsedDefinitions )
  }

  private def batch(
    parsedDefinitions: Iterable[PrimitiveRecursiveFunction] )(
    implicit
    ctx: Context ): Iterable[PrimitiveRecursiveFunction] = {

    val ordering = sortConstants(
      parsedDefinitions.map {
        definition =>
          ( definition.c, definition.equations )
      } )

    sortDefinitions( ordering, parsedDefinitions )
  }

  private def sortDefinitions(
    ordering: Iterable[Const], definitions: Iterable[PrimitiveRecursiveFunction] ): Iterable[PrimitiveRecursiveFunction] = {
    ordering.map { constant => definitions.find( _.c == constant ).get }
  }

  private def sortConstants(
    definitions: Iterable[( Const, Seq[( Expr, Expr )] )] ): Seq[Const] = {

    val constants = definitions.map { _._1 }

    linearizeStrictPartialOrder(
      constants,
      dependencyRelation( definitions ) ) match {
        case Left( cycle ) =>
          throw new IllegalArgumentException(
            s"cyclic dependency: ${cycle.mkString( " < " )}" )
        case Right( order ) => order.reverse
      }
  }

  private def dependencyRelation(
    definitions: Iterable[( Const, Seq[( Expr, Expr )] )] ): Set[( Const, Const )] = {
    val constants = definitions.map { _._1 }.toSet
    definitions.flatMap {
      case ( constant, equations ) =>
        val dependsOn: Set[Const] =
          equations.map { _._2 }.flatMap { extractConstant }.toSet.intersect( constants ).diff( Set( constant ) )
        dependsOn.map { ( constant, _ ) }
    }.toSet
  }

  private def extractConstant( expression: Expr ): Set[Const] = {
    expression match {
      case c @ Const( _, _, _ ) =>
        Set( c )
      case App( function, argument ) =>
        extractConstant( function ) ++ extractConstant( argument )
      case Abs( _, subexpression ) =>
        extractConstant( subexpression )
      case _ => Set()
    }
  }

}
