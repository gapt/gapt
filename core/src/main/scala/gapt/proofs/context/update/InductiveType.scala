package gapt.proofs.context.update

import gapt.expr.Const
import gapt.expr.ty.FunctionType
import gapt.expr.ty.TBase
import gapt.expr.ty.TVar
import gapt.expr.ty.Ty
import gapt.expr.util.typeVariables
import gapt.proofs.context.Context
import gapt.proofs.context.State
import gapt.proofs.context.facet.BaseTypes
import gapt.proofs.context.facet.Constants
import gapt.proofs.context.facet.StructurallyInductiveTypes
import gapt.proofs.context.update.InductiveType.Constructor
import gapt.proofs.context.update.InductiveType.Constructor.Field
import gapt.proofs.context.update.InductiveType.ConstructorDefinition
import gapt.proofs.context.update.InductiveType.FieldDefinition

/** Inductive base type with constructors. */
case class InductiveType private (
    baseType:       TBase,
    constructors:   Seq[Constructor],
    typeParameters: Seq[TVar] ) extends TypeDefinition {

  val constructorConstants: Seq[Const] = constructors.map( _.constant )
  val baseCases: Seq[Constructor] =
    constructors.filter( isBaseCase )

  override val ty: TBase = baseType

  override def apply( ctx: Context ): State = {
    require( !ctx.isType( baseType ), s"Type $baseType already defined" )
    for ( c <- constructors ) {
      checkConstructor( c, ctx )
      for ( f <- c.fields ) {
        f.projector match {
          case Some( p ) =>
            require(
              ctx.constant( p.name ).isEmpty,
              s"Projector $p is already a declared constant" )
          case _ =>
        }
        if ( f.ty != baseType ) {
          ctx.check( f.ty )
        }
      }
    }
    ctx.state
      .update[BaseTypes]( _ + baseType )
      .update[Constants]( _ ++ constructors.map( _.constant ) )
      .update[Constants]( _ ++ projectors )
      .update[StructurallyInductiveTypes]( _ + ( baseType.name, constructors.map( _.constant ).toVector ) )
  }

  private def checkConstructor( c: Constructor, ctx: Context ): Unit = {
    require(
      ctx.constant( c.constant.name ).isEmpty,
      s"Constructor $c is already a declared constant" )
  }

  private def projectors: Seq[Const] =
    constructors.flatMap( _.fields.flatMap( _.projector ) )

  private def isBaseCase( constructor: Constructor ): Boolean =
    !constructor.fields.map( _.ty ).contains( baseType )
}

object InductiveType {

  case class Constructor( constant: Const, fields: Seq[Constructor.Field] )

  object Constructor {
    case class Field( projector: Option[Const], ty: Ty )
  }

  type FieldDefinition = ( Option[String], Ty )
  type ConstructorDefinition = ( String, Seq[FieldDefinition] )

  def apply( baseType: Ty, constructors: Const* ): InductiveType =
    new InductiveTypeLegacyParser( baseType, constructors ).parse

  def apply( tyName: String, constructors: Const* ): InductiveType =
    InductiveType( TBase( tyName ), constructors: _* )

  def apply( name: String, parameters: Seq[TVar], constructors: ConstructorDefinition* ): InductiveType =
    new InductiveTypeInternalParser( name, parameters, constructors ).parse
}

trait InductiveTypeParser {
  /**
   * Parses an inductive type from some data.
   */
  def parse: InductiveType
}

class InductiveTypeLegacyParser( ty: Ty, constructors: Seq[Const] ) extends InductiveTypeParser {

  private var parameters: Seq[TVar] = _
  private var baseType: TBase = _
  private var constructorDefs: Seq[ConstructorDefinition] = _

  override def parse: InductiveType = {
    parseBaseType()
    parseParameters()
    parseConstructorDefinitions()
    new InductiveTypeInternalParser( baseType.name, parameters, constructorDefs ).parse
  }

  private def parseBaseType(): Unit = {
    require(
      ty.isInstanceOf[TBase],
      s"Cannot parse inductive type: expected base type but got type ${ty}." )
    baseType = ty.asInstanceOf[TBase]
  }

  private def parseParameters(): Unit = {
    val allParametersAreVariables = baseType.params.forall( _.isInstanceOf[TVar] )
    require(
      allParametersAreVariables,
      s"Cannot parse inductive type: type parameter " +
        s"${baseType.params.find( !_.isInstanceOf[TVar] )} is not a type variable." )
    parameters = baseType.params.map( _.asInstanceOf[TVar] )
  }

  private def parseConstructorDefinitions(): Unit = {
    require(
      allConstructorsReturnBaseType,
      s"Cannot parse inductive type: constructor " +
        s"${constructorNotReturningBaseType.get} does not construct ${baseType}" )
    require(
      constructorsDoNotContainForeignParameters,
      s"Cannot parse inductive type: constructor " +
        s"${constructorWithForeignParameters} involves foreign parameters" )
    constructorDefs = constructors.map( projectorlessConstructorDefinition )
  }

  private def allConstructorsReturnBaseType: Boolean =
    constructorNotReturningBaseType.isEmpty

  private def constructorNotReturningBaseType: Option[Const] =
    constructors.find {
      c => val FunctionType( to, _ ) = c.ty; to != baseType
    }

  private def constructorsDoNotContainForeignParameters: Boolean =
    constructorWithForeignParameters.isEmpty

  private def constructorWithForeignParameters: Option[Const] =
    constructors.find {
      !typeVariables( _ ).subsetOf( parameters.toSet )
    }

  private def projectorlessConstructorDefinition( c: Const ): ConstructorDefinition = {
    val FunctionType( _, ts ) = c.ty
    c.name -> ts.map { ( None, _ ) }
  }
}

/**
 * Parses an inductive type from an intermediary representation.
 *
 * This parser can be used to parse an inductive type from an intermediary
 * representation obtained by parsing some other input source or to construct
 * an inductive type manually.
 */
class InductiveTypeInternalParser(
    name:                   String,
    typeParameters:         Seq[TVar],
    constructorDefinitions: Seq[ConstructorDefinition] ) extends InductiveTypeParser {

  private val baseType: TBase = TBase( name, typeParameters: _* )

  override def parse: InductiveType = {
    val inductiveType = assembleInductiveType
    validateInductiveType( inductiveType )
    inductiveType
  }

  private def assembleInductiveType(): InductiveType = {
    val constructors = assembleConstructors()
    InductiveType( baseType, constructors, typeParameters )
  }

  private def validateInductiveType( it: InductiveType ): Unit =
    InductiveTypeValidator.validate( it )

  private def assembleConstructors(): Seq[Constructor] =
    constructorDefinitions.map( assembleConstructor )

  private def assembleConstructor( constrDef: ConstructorDefinition ): Constructor = {
    val ( constrName, fieldDefs ) = constrDef
    val fieldTypes = fieldDefs.map { _._2 }
    Constructor(
      constructorConstant( constrName, fieldTypes ),
      fieldDefs.map( assembleField ) )
  }

  private def assembleField( fieldDef: FieldDefinition ): Field = {
    val ( projectorName, projectorType ) = fieldDef
    Field(
      projectorName.map( projectorConstant( _, projectorType ) ),
      projectorType )
  }

  private def constructorConstant( name: String, fields: Seq[Ty] ): Const =
    Const( name, FunctionType( baseType, fields ), typeParameters.toList )

  private def projectorConstant( name: String, ty: Ty ): Const =
    Const( name, baseType ->: ty, typeParameters.toList )
}

object InductiveTypeValidator {
  def validate( inductiveType: InductiveType ): Unit =
    new InductiveTypeValidator( inductiveType ).validate()
}
class InductiveTypeValidator( inductiveType: InductiveType ) {

  def validate(): Unit = {
    requireConstructorsToBeConstructorsForType()
    requireDistinctConstructorNames()
    projectorNamesShouldNotIntersectConstructorNames()
    projectorNamesShouldNotIntersectOtherProjectorNames()
    requireAtLeastOneBaseCase()
  }

  private def requireConstructorsToBeConstructorsForType(): Unit =
    for ( constr <- inductiveType.constructorConstants ) {
      constructorMustConstructInductiveType( constr )
      typeParametersMustAgreeWithInductiveType( constr )
      typeVariablesMustBeSubsetOfTypeParameters( constr )
    }

  private def constructorMustConstructInductiveType( constructor: Const ): Unit = {
    val FunctionType( ty_, _ ) = constructor.ty
    require(
      inductiveType.baseType == ty_,
      s"Base type ${inductiveType.baseType} and " +
        s"type constructor $constructor don't agree." )
  }

  private def typeParametersMustAgreeWithInductiveType( constructor: Const ): Unit =
    require( constructor.params == inductiveType.typeParameters )

  private def typeVariablesMustBeSubsetOfTypeParameters( constructor: Const ): Unit =
    require( typeVariables( constructor ) subsetOf inductiveType.typeParameters.toSet )

  private def requireDistinctConstructorNames(): Unit =
    require(
      inductiveType.constructorConstants.map( _.name ) ==
        inductiveType.constructorConstants.map( _.name ).distinct,
      s"Names of type constructors are not distinct." )

  private def projectorNamesShouldNotIntersectConstructorNames(): Unit = {
    val projectorNames: Seq[String] = inductiveType.constructors.flatMap {
      c => c.fields.flatMap( _.projector.map( _.name ) )
    }
    val constructorNames = inductiveType.constructorConstants.map( _.name )
    val intersectingNames = projectorNames.intersect( constructorNames )
    require(
      intersectingNames.isEmpty,
      s"Invalid inductive type: Symbol(s) ${intersectingNames.mkString( ", " )} occur as " +
        s"constructor and as projector" )
  }

  private def projectorNamesShouldNotIntersectOtherProjectorNames(): Unit = {
    val projectorGroups = inductiveType.constructors.flatMap {
      c => c.fields.flatMap( _.projector.map( _.name ) )
    }.groupBy( n => n )
    val nonUniqueProjectors = projectorGroups.find {
      case ( _, ns ) if ns.size != 1 => true
      case _                         => false
    }.map( _._1 )
    require(
      nonUniqueProjectors.isEmpty,
      s"Invalid inductive type: Multiple occurrences of projector " +
        s"symbol(s) ${nonUniqueProjectors.mkString( ", " )}" )
  }

  private def requireAtLeastOneBaseCase(): Unit =
    require(
      inductiveType.baseCases.nonEmpty,
      "Inductive type is empty, all of the constructors are recursive: " +
        s"${inductiveType.constructorConstants.mkString( ", " )}" )
}
