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
    for ( Const( ctr, FunctionType( _, fieldTys ), _ ) <- constructors.map( _.constant ) ) {
      require( ctx.constant( ctr ).isEmpty, s"Constructor $ctr is already a declared constant" )
      for ( fieldTy <- fieldTys ) {
        if ( fieldTy == baseType ) {
          // positive occurrence of the inductive type
        } else {
          ctx.check( fieldTy )
        }
      }
    }
    ctx.state.update[BaseTypes]( _ + baseType )
      .update[Constants]( _ ++ constructors.map( _.constant ) )
      .update[StructurallyInductiveTypes]( _ + ( baseType.name, constructors.map( _.constant ).toVector ) )
  }

  private def isBaseCase( constructor: Constructor ): Boolean =
    !constructor.fields.map( _.ty ).contains( baseType )
}

object InductiveType {

  case class Constructor( constant: Const, fields: Seq[Constructor.Field] )

  object Constructor {
    case class Field( projector: Option[Const], ty: Ty )
  }

  def apply( baseType: Ty, constructors: Const* ): InductiveType = {
    new InductiveTypeBaseTypeConstructorsParser( baseType, constructors ).parse
  }

  def apply( tyName: String, constructors: Const* ): InductiveType =
    InductiveType( TBase( tyName ), constructors: _* )
}

trait InductiveTypeParser {
  /**
   * Parses an inductive type from some data.
   */
  def parse: InductiveType
}

class InductiveTypeBaseTypeConstructorsParser(
    ty: Ty, constructors: Seq[Const] ) extends InductiveTypeParser {

  type FieldDefinition = ( Option[String], Ty )
  type ConstructorDefinition = ( String, Seq[FieldDefinition] )

  private var baseType: TBase = _
  private var typeParameters: Seq[TVar] = _
  private var constructorDefinitions: Seq[ConstructorDefinition] = _

  override def parse: InductiveType = {
    val inductiveType = parseInput
    validateInductiveType( inductiveType )
    inductiveType
  }

  private def parseInput: InductiveType = {
    parseBaseType()
    parseTypeParameters()
    parseConstructorDefinitions()
    assembleInductiveType()
  }

  private def validateInductiveType( it: InductiveType ): Unit =
    InductiveTypeValidator.validate( it )

  private def parseBaseType(): Unit =
    baseType = ty.asInstanceOf[TBase]

  private def parseTypeParameters(): Unit =
    typeParameters = baseType.params.map( _.asInstanceOf[TVar] )

  private def parseConstructorDefinitions(): Unit =
    constructorDefinitions =
      constructors.map { c =>
        val FunctionType( _, ts ) = c.ty
        c.name -> ts.map { ( None, _ ) }
      }

  private def assembleInductiveType(): InductiveType = {
    val constructors = assembleConstructors()
    InductiveType( baseType, constructors, typeParameters )
  }

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

  private def requireAtLeastOneBaseCase(): Unit =
    require(
      inductiveType.baseCases.nonEmpty,
      "Inductive type is empty, all of the constructors are recursive: " +
        s"${inductiveType.constructorConstants.mkString( ", " )}" )
}
