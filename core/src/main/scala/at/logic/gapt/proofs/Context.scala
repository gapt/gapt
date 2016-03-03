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
    require(
      !( constantsMap get const.name exists { _ != const } ),
      s"Constant ${const.name} is already defined as ${constantsMap get const.name get}."
    )

    for ( t <- baseTypes( const.exptype ) ) require(
      typeDef( t.name ).isDefined,
      s"Constant definition contains undeclared type ${t.name}."
    )

    copy( constants = constants + const )
  }
  def ++( consts: Iterable[Const] ): FiniteContext =
    consts.foldLeft( this )( _ + _ )

  def +( typeDef: TypeDef ): FiniteContext = {
    require(
      !( typeDefsMap get typeDef.ty.name exists { _ != typeDef } ),
      s"Type ${typeDef.ty.name} is already defined as ${typeDefsMap get typeDef.ty.name get}."
    )
    typeDef match {
      case Sort( _ ) => copy( typeDefs = typeDefs + typeDef )
      case InductiveType( _, constructors ) =>
        require(
          constructors.map { _.toString } == constructors.map { _.toString }.distinct,
          s"Names of type constructors are not distinct."
        )
        for ( const <- constructors )
          require(
            !( constantsMap get const.name exists { _ != const } ),
            s"Constant ${const.name} is already defined as ${constantsMap get const.name get}."
          )
        copy( typeDefs = typeDefs + typeDef, constants = constants ++ constructors )
    }
  }
  def ++( typeDefs: Iterable[TypeDef] )( implicit dummyImplicit: DummyImplicit ): FiniteContext =
    typeDefs.foldLeft( this )( _ + _ )

  def +( defn: ( String, LambdaExpression ) ): FiniteContext = {
    val ( name, by ) = defn
    val what = Const( name, by.exptype )
    require(
      definition( name ).isEmpty,
      s"In definition $name -> $by: $name is already defined as ${definition( name ).get}."
    )

    require(
      constant( name ).isEmpty,
      s"In definition $name -> $by: Constant $name is already defined as ${constantsMap get name get}."
    )

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
      require(
        ty == ty_,
        s"Base type $ty and type constructor $constr don't agree."
      )
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
