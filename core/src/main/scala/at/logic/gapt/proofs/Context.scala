package at.logic.gapt.proofs

import at.logic.gapt.expr.{ Bottom, Const, LambdaExpression, TBase, Ti, To, Top }
import at.logic.gapt.formats.babel
import Context._

trait Context extends babel.Signature {
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

object Context {
  sealed trait TypeDef { def ty: TBase }
  case class Sort( ty: TBase ) extends TypeDef
  case class InductiveType( ty: TBase, constructors: Seq[Const] ) extends TypeDef

  val oTypeDef = Context.InductiveType( To, Seq( Top(), Bottom() ) )
  val iTypeDef = Context.Sort( Ti )
}
