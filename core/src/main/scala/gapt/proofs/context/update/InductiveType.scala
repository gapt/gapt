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
import gapt.proofs.context.update.InductiveType.Constructor
import gapt.proofs.context.update.InductiveType.Constructor.Field

/** Inductive base type with constructors. */
case class InductiveType(
    private val baseTypeName:           String,
    typeParameters:                     Seq[TVar],
    private val constructorDefinitions: Seq[( String, Seq[( Option[String], Ty )] )] ) extends TypeDefinition {

  val baseType: TBase = TBase( baseTypeName, typeParameters.toList )
  val ty: TBase = baseType

  val constructors: Seq[Constructor] =
    constructorDefinitions.map {
      case ( constrName, fieldDefs ) =>
        new Constructor {
          val constant = Const(
            constrName,
            FunctionType( baseType, fieldDefs.map { _._2 } ),
            typeParameters.toList )
          val fields = fieldDefs.map {
            case ( maybeProj, t ) => new Field {
              override val projector: Option[Const] =
                maybeProj.map( Const( _, baseType ->: t, typeParameters.toList ) )
              override val ty: Ty = t
            }
          }
        }
    }

  val baseCases: Seq[Constructor] = constructors.filter( isBaseConstructor )

  private val constructorConstants = constructors.map( _.constant )

  override def apply( ctx: Context ): State = {
    require( !ctx.isType( baseType ), s"Type $baseType already defined" )
    for ( Const( ctr, FunctionType( _, fieldTys ), _ ) <- constructorConstants ) {
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
      .update[Constants]( _ ++ constructorConstants )
      .update[StructurallyInductiveTypes]( _ + ( baseType.name, constructorConstants.toVector ) )
  }

  private def isBaseConstructor( constructor: Constructor ): Boolean = {
    !constructor.fields.map( _.ty ).contains( baseType )
  }
}

class InductiveTypeInputValidator( ty: Ty, constructors: Seq[Const] ) {

  private val baseType: TBase = ty.asInstanceOf[TBase]
  private val typeParameters = baseType.params.map( _.asInstanceOf[TVar] )
  private val baseCases = constructors.filter( isBaseCase )

  def validate(): Unit = {
    requireConstructorsToBeConstructorsForType()
    requireDistinctConstructorNames()
    requireAtLeastOneBaseCase()
  }

  private def requireConstructorsToBeConstructorsForType(): Unit =
    for ( constr <- constructors ) {
      constructorMustConstructInductiveType( constr )
      typeParametersMustAgreeWithInductiveType( constr )
      typeVariablesMustBeSubsetOfTypeParameters( constr )
    }

  private def constructorMustConstructInductiveType( constructor: Const ): Unit = {
    val FunctionType( ty_, _ ) = constructor.ty
    require(
      baseType == ty_,
      s"Base type ${baseType} and type constructor $constructor don't agree." )
  }

  private def typeParametersMustAgreeWithInductiveType( constructor: Const ): Unit =
    require( constructor.params == typeParameters )

  private def typeVariablesMustBeSubsetOfTypeParameters( constructor: Const ): Unit =
    require( typeVariables( constructor ) subsetOf typeParameters.toSet )

  private def requireDistinctConstructorNames(): Unit =
    require(
      constructors.map( _.name ) == constructors.map( _.name ).distinct,
      s"Names of type constructors are not distinct." )

  private def requireAtLeastOneBaseCase(): Unit =
    require(
      baseCases.nonEmpty,
      s"Inductive type is empty, all of the constructors are recursive: ${constructors.mkString( ", " )}" )

  private def isBaseCase( constructor: Const ): Boolean = {
    val FunctionType( _, ts ) = constructor.ty
    !ts.contains( baseType )
  }
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

  def apply( ty: Ty, constructors: Const* ): InductiveType = {
    val inductiveType = buildInductiveType( ty, constructors: _* )
    validate( ty, constructors )
    inductiveType
  }

  def apply( tyName: String, constructors: Const* ): InductiveType =
    InductiveType( TBase( tyName ), constructors: _* )

  private def buildInductiveType( ty: Ty, constructors: Const* ): InductiveType = {
    val baseType = ty.asInstanceOf[TBase]
    val typeParameters = baseType.params.map( _.asInstanceOf[TVar] )
    val constructorDefinitions = constructors.map { c =>
      val FunctionType( _, ts ) = c.ty
      c.name -> ts.map { ( None, _ ) }
    }
    InductiveType( baseType.name, typeParameters, constructorDefinitions )
  }

  private def validate( ty: Ty, constructors: Seq[Const] ): Unit =
    new InductiveTypeInputValidator( ty, constructors ).validate()
}