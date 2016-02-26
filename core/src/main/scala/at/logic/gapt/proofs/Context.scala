package at.logic.gapt.proofs

import at.logic.gapt.expr._
import at.logic.gapt.formats.babel
import at.logic.gapt.formats.babel.BabelSignature
import Context._

trait Context extends BabelSignature {
  def constant( name: String ): Option[Const]
  def typeDef( name: String ): Option[TypeDef]
  def definition( name: String ): Option[LambdaExpression]

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
  val definitionMap = definitions map { case ( w, b ) => w.name -> b }
  for ( ( c, d ) <- definitions ) require( c.exptype == d.exptype )

  def constant( name: String ) = constantsMap get name
  def definition( name: String ) = definitionMap get name
  def typeDef( name: String ) = typeDefsMap get name

  def +( const: Const ): FiniteContext = {
    require( !( constantsMap get const.name exists { _ != const } ) )
    for ( t <- baseTypes( const.exptype ) ) require( typeDef( t.name ).isDefined )
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

  def +( defn: ( String, LambdaExpression ) ): FiniteContext = {
    val ( name, by ) = defn
    val what = Const( name, by.exptype )
    require( definition( name ).isEmpty )
    require( constant( name ).isEmpty )
    require( freeVariables( by ).isEmpty, s"In definition $name -> $by: contains free variables ${freeVariables( by )}" )
    for ( c <- at.logic.gapt.expr.constants( by ) if EqC.unapply( c ).isEmpty )
      require( constant( c.name ) contains c, s"In definition $name -> $by: constant $c not defined yet" )
    copy( constants = constants + what, definitions = definitions + ( what -> by ) )
  }

  def +( equation: HOLFormula ): FiniteContext = equation match {
    case Eq( Apps( Var( definedConstName, _ ), arguments ), definition ) =>
      this + ( definedConstName -> Abs( arguments map { _.asInstanceOf[Var] }, definition ) )
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
