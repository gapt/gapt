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
    constants:   Set[Const]                   = Set(),
    definitions: Map[Const, LambdaExpression] = Map(),
    typeDefs:    Set[Context.TypeDef]         = Set( Context.oTypeDef )
) extends Context {
  val constantsMap = constants.map { c => c.name -> c }.toMap
  val typeDefsMap = typeDefs.map { td => td.ty.name -> td }.toMap
  for ( ( c, d ) <- definitions ) require( c.exptype == d.exptype )

  def constant( name: String ) = constantsMap get name
  def definition( const: Const ) = definitions get const
  def typeDef( name: String ) = typeDefsMap get name

  def +( const: Const ): FiniteContext = {
    require( !( constantsMap get const.name exists { _ != const } ) )
    copy( constants = constants + const )
  }
  def ++( consts: Iterable[Const] ): FiniteContext =
    consts.foldLeft( this )( _ + _ )

  def +( typeDef: TypeDef ): FiniteContext = {
    require( !( typeDefsMap get typeDef.ty.name exists { _ != typeDef } ) )
    typeDef match {
      case Sort( _ ) => copy( typeDefs = typeDefs + typeDef )
      case InductiveType( _, constructors ) =>
        require( constructors.map { _.toString } == constructors.map { _.toString }.distinct )
        for ( const <- constructors )
          require( !( constantsMap get const.name exists { _ != const } ) )
        copy( typeDefs = typeDefs + typeDef, constants = constants ++ constructors )
    }
  }

  def +( what: Const, by: LambdaExpression ): FiniteContext = {
    require( !definitions.contains( what ) )
    require( freeVariables( by ).isEmpty )
    require( constant( what.name ).isEmpty )
    for ( c <- at.logic.gapt.expr.constants( by ) ) require( constant( c.name ) contains c )
    copy( constants = constants + what, definitions = definitions + ( what -> by ) )
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
