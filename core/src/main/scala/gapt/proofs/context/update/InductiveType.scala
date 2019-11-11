package gapt.proofs.context.update

import gapt.expr.Const
import gapt.expr.ty.FunctionType
import gapt.expr.ty.TBase
import gapt.expr.ty.TVar
import gapt.expr.ty.Ty
import gapt.expr.util.typeVariables
import gapt.proofs.context.Context
import gapt.proofs.context.facet.Constants
import gapt.proofs.context.facet.StructurallyInductiveTypes
import gapt.proofs.context.State
import gapt.proofs.context.facet.BaseTypes

/** Inductive base type with constructors. */
case class InductiveType(
    baseTypeName:   String,
    typeParameters: Seq[TVar],
    constructors:   Vector[Const] ) extends TypeDefinition {

  val baseType: TBase = TBase( baseTypeName, typeParameters.toList )
  val ty: TBase = baseType
  val baseCases: Seq[Const] = constructors.filter( isBaseConstructor )

  override def apply( ctx: Context ): State = {
    require( !ctx.isType( baseType ), s"Type $baseType already defined" )
    for ( Const( ctr, FunctionType( _, fieldTys ), _ ) <- constructors ) {
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
      .update[Constants]( _ ++ constructors )
      .update[StructurallyInductiveTypes]( _ + ( baseType.name, constructors.toVector ) )
  }

  private def isBaseConstructor( constructor: Const ): Boolean = {
    val FunctionType( _, argTys ) = constructor.ty
    !argTys.contains( baseType )
  }
}

class InductiveTypeValidator( inductiveType: InductiveType ) {

  def validate(): Unit = {
    requireConstructorsToBeConstructorsForType()
    requireDistinctConstructorNames()
    requireAtLeastOneBaseCase()
  }

  private def requireConstructorsToBeConstructorsForType(): Unit =
    for ( constr <- inductiveType.constructors ) {
      constructorMustConstructInductiveType( constr )
      typeParametersMustAgreeWithInductiveType( constr )
      typeVariablesMustBeSubsetOfTypeParameters( constr )
    }

  private def constructorMustConstructInductiveType( constructor: Const ): Unit = {
    val FunctionType( ty_, _ ) = constructor.ty
    require(
      inductiveType.baseType == ty_,
      s"Base type ${inductiveType.baseType} and type constructor $constructor don't agree." )
  }

  private def typeParametersMustAgreeWithInductiveType( constructor: Const ): Unit =
    require( constructor.params == inductiveType.typeParameters )

  private def typeVariablesMustBeSubsetOfTypeParameters( constructor: Const ): Unit =
    require( typeVariables( constructor ) subsetOf inductiveType.typeParameters.toSet )

  private def requireDistinctConstructorNames(): Unit =
    require(
      inductiveType.constructors.map( _.name ) == inductiveType.constructors.map( _.name ).distinct,
      s"Names of type constructors are not distinct." )

  private def requireAtLeastOneBaseCase(): Unit =
    require(
      inductiveType.baseCases.nonEmpty,
      s"Inductive type is empty, all of the constructors are recursive: ${inductiveType.constructors.mkString( ", " )}" )
}

object InductiveType {

  def apply( ty: Ty, constructors: Const* ): InductiveType = {
    val inductiveType = buildInductiveType( ty, constructors: _* )
    validate( inductiveType )
    inductiveType
  }

  def apply( tyName: String, constructors: Const* ): InductiveType =
    InductiveType( TBase( tyName ), constructors: _* )

  private def buildInductiveType( ty: Ty, constructors: Const* ): InductiveType = {
    val baseType = ty.asInstanceOf[TBase]
    val typeParameters = baseType.params.map( _.asInstanceOf[TVar] )
    InductiveType( baseType.name, typeParameters, constructors.toVector )
  }

  private def validate( inductiveType: InductiveType ): Unit =
    new InductiveTypeValidator( inductiveType ).validate()
}