package at.logic.gapt.proofs

import at.logic.gapt.expr.{ Bottom, Const, FunctionType, LambdaExpression, TBase, Ti, To, Top, baseTypes, constants, freeVariables }
import at.logic.gapt.formats.babel
import at.logic.gapt.formats.babel.BabelSignature
import Context._

import scala.collection.mutable

trait Context extends BabelSignature {
  def constant( name: String ): Option[Const]
  def typeDef( name: String ): Option[TypeDef]
  def definition( const: Const ): Option[LambdaExpression]

  override def apply( s: String ): babel.VarConst =
    constant( s ) match {
      case Some( c ) => babel.IsConst( babel.ast.liftType( c.exptype ) )
      case None      => babel.IsVar( babel.ast.freshTypeVar() )
    }
}

case class FiniteContext(
    constants:   Set[Const],
    definitions: Map[Const, LambdaExpression] = Map(),
    typeDefs:    Set[Context.TypeDef]         = Set( Context.iTypeDef, Context.oTypeDef )
) extends Context {
  val constantsMap = constants.map { c => c.name -> c }.toMap
  val typeDefsMap = typeDefs.map { td => td.ty.name -> td }.toMap
  for ( ( c, d ) <- definitions ) require( c.exptype == d.exptype )

  def constant( name: String ) = constantsMap get name
  def definition( const: Const ) = definitions get const
  def typeDef( name: String ) = typeDefsMap get name
}

class MutableContext extends Context {
  private val constantsMap = mutable.Map[String, Const]()
  private val typeDefsMap = mutable.Map[String, TypeDef]()
  private val definitionMap = mutable.Map[Const, LambdaExpression]()

  def constant( name: String ) = constantsMap get name
  def definition( const: Const ) = definitionMap get const
  def typeDef( name: String ) = typeDefsMap get name

  def +=( const: Const ): Unit = declareConst( const, unsafe = false )
  def +=( typeDef: TypeDef ): Unit = declareTypeDef( typeDef, unsafe = false )
  def +=( definition: ( Const, LambdaExpression ) ): Unit = declareDefinition( definition._1, definition._2 )

  def declareConst( const: Const, unsafe: Boolean ) =
    constantsMap get const.name match {
      case Some( const_ ) => if ( const != const_ ) throw new IllegalArgumentException
      case None =>
        if ( !unsafe )
          for ( t <- baseTypes( const.exptype ) )
            require( typeDef( t.name ).isDefined )
        constantsMap( const.name ) = const
    }

  def declareTypeDef( typeDef: TypeDef, unsafe: Boolean ) =
    typeDefsMap get typeDef.ty.name match {
      case Some( typeDef_ ) => if ( typeDef != typeDef_ ) throw new IllegalArgumentException
      case None =>
        typeDefsMap( typeDef.ty.name ) = typeDef
        typeDef match {
          case InductiveType( _, constructors ) =>
            for ( c <- constructors ) declareConst( c, unsafe )
          case Sort( _ ) =>
        }
    }

  def declareDefinition( what: Const, by: LambdaExpression ) =
    definitionMap get what match {
      case Some( by_ ) => if ( by != by_ ) throw new IllegalArgumentException
      case None =>
        require( constant( what.name ).isEmpty )
        require( what.exptype == by.exptype )
        this += what
        require( freeVariables( by ).isEmpty )
        constants( by ) foreach +=
    }
}

object Context {
  sealed trait TypeDef { def ty: TBase }
  case class Sort( ty: TBase ) extends TypeDef
  case class InductiveType( ty: TBase, constructors: Seq[Const] ) extends TypeDef {
    for ( constr <- constructors ) {
      val FunctionType( ty_, _ ) = constr.exptype
      require( ty == ty_ )
    }
  }

  object Sort {
    def apply( tyName: String ): Sort = Sort( TBase( tyName ) )
  }
  object InductiveType {
    def apply( tyName: String, constructors: Const* ): InductiveType =
      InductiveType( TBase( tyName ), constructors )
  }

  val oTypeDef = Context.InductiveType( "o", Top(), Bottom() )
  val iTypeDef = Context.Sort( "i" )
}
