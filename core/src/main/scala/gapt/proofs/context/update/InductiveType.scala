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
import gapt.proofs.context.update.ParserOutput.ConstructorDefinition
import gapt.proofs.context.update.ParserOutput.FieldDefinition

/** Inductive base type with constructors. */

case class InductiveType(
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

  trait Constructor {
    val constant: Const
    val fields: Seq[Constructor.Field]
  }

  object Constructor {
    trait Field {
      val projector: Option[Const]
      val ty: Ty
    }
  }

  def apply( baseType: Ty, constructors: Const* ): InductiveType = {
    val output = InductiveTypeParser.parse( baseType, constructors )
    val inductiveType = InductiveTypeBuilder.build( output )
    InductiveTypeValidator.validate( inductiveType )
    inductiveType
  }

  def apply( tyName: String, constructors: Const* ): InductiveType =
    InductiveType( TBase( tyName ), constructors: _* )
}

object InductiveTypeParser {

  def parse( ty: Ty, constructors: Seq[Const] ): ParserOutput = {
    val baseType = ty.asInstanceOf[TBase]
    val typeParameters = baseType.params.map( _.asInstanceOf[TVar] )
    val constructorDefinitions = constructors.map { c =>
      val FunctionType( _, ts ) = c.ty
      c.name -> ts.map { ( None, _ ) }
    }
    ParserOutput( baseType.name, typeParameters, constructorDefinitions )
  }

}

object ParserOutput {
  type FieldDefinition = ( Option[String], Ty )
  type ConstructorDefinition = ( String, Seq[FieldDefinition] )
}
case class ParserOutput(
    baseTypeName:           String,
    typeParameters:         Seq[TVar],
    constructorDefinitions: Seq[ConstructorDefinition] )

object InductiveTypeBuilder {
  def build( input: ParserOutput ): InductiveType =
    new InductiveTypeBuilder(
      input.baseTypeName,
      input.typeParameters,
      input.constructorDefinitions ).build()
}
class InductiveTypeBuilder(
    private val baseTypeName:           String,
    val typeParameters:                 Seq[TVar],
    private val constructorDefinitions: Seq[ConstructorDefinition] ) {

  val baseType: TBase = buildBaseType()
  val constructors: Seq[Constructor] = buildConstructors()
  val baseCases: Seq[Constructor] = constructors.filter( isBaseConstructor )

  def build(): InductiveType =
    InductiveType(
      baseType,
      constructors,
      typeParameters )

  private def buildBaseType(): TBase =
    TBase( baseTypeName, typeParameters.toList )

  private def buildConstructors(): Seq[Constructor] =
    constructorDefinitions.map( buildConstructor )

  private def buildConstructor( definition: ConstructorDefinition ): Constructor = {
    val ( constrName, fieldDefs ) = definition
    val fieldTypes = fieldDefs.map { _._2 }
    new Constructor {
      val constant = constructorConstant( constrName, fieldTypes )
      val fields = fieldDefs.map( buildField )
    }
  }

  private def constructorConstant( name: String, fieldTypes: Seq[Ty] ): Const =
    Const(
      name,
      FunctionType( baseType, fieldTypes ),
      typeParameters.toList )

  private def buildField( definition: FieldDefinition ): Field = {
    val ( projectorName, projectorType ) = definition
    new Field {
      override val projector: Option[Const] =
        projectorName.map( projectorConstant( _, projectorType ) )
      override val ty: Ty = projectorType
    }
  }

  private def projectorConstant( name: String, ty: Ty ): Const =
    Const( name, baseType ->: ty, typeParameters.toList )

  private def isBaseConstructor( constructor: Constructor ): Boolean = {
    !constructor.fields.map( _.ty ).contains( baseType )
  }
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
