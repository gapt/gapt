package at.logic.gapt.proofs

import at.logic.gapt.expr._
import at.logic.gapt.formats.babel
import at.logic.gapt.formats.babel.BabelSignature
import Context._
import at.logic.gapt.proofs.lk.DefinitionElimination

/**
 * Captures constants, types, definitions, and background theory used in a proof.
 *
 * There are several inferences in our LK proofs for which it is not enough that are
 * syntactically valid:  An induction inference might follow the syntactical scheme of
 * an induction inference and satisfy the eigenvariable criterion, however if it excludes
 * a constructor of the inductive type, then it still allows us to prove non-theorems.
 * The same is also true for definition rules and theory axioms.
 *
 * Hence we store all information necessary to validate these inferences inside a
 * [[Context]] object.  For completeness, it also includes the collection of constant symbols.
 *
 * Having this information available is also important for a second reason: it allows
 * us make decisions based on the current context:
 *
 *  - The induction tactic uses the information about inductive types to create the necessary subgoals.
 *  - The Babel parser uses the information about constants to decide whether a free identifier
 *    is a variable or a constant, and if it is a constant, what type it should have.
 *  - The unfold tactic uses the information about definitions to unfold them.
 *  - The inductive prover can automatically generate random instances for base types.
 *  - [[at.logic.gapt.proofs.expansion.ExpansionProofToLK]] uses the information about the background theory
 *    to produce LK proofs modulo the background theory.
 */
class Context private ( val elements: Vector[Element] ) extends BabelSignature {
  val constants = elements.flatMap( _.consts )
  private val constantsMap = constants.map( c => c.name -> c ).toMap
  private val typeDefsMap = elements.flatMap( el => el.tys.map( _.name -> el ) ).toMap
  val definitions = elements.flatMap( _.defs )
  private val definitionMap = definitions.map { case ( c, d ) => c.name -> d }.toMap
  val axioms = elements.flatMap( _.axioms )

  /** Returns Some(const) if name is a constant. */
  def constant( name: String ): Option[Const] = constantsMap.get( name )
  /** Returns Some(typeDef) if name is a base type. */
  def typeDef( name: String ): Option[Element] = typeDefsMap.get( name )
  /** Returns Some(expandedDefinition) if name is a defined constant. */
  def definition( name: String ): Option[LambdaExpression] = definitionMap.get( name )

  def typeDef( ty: TBase ): Option[Element] = typeDef( ty.name )

  def skolemDef( skSym: Const ): Option[LambdaExpression] =
    elements.collect { case SkolemFun( `skSym`, defn ) => defn }.headOption

  def +( element: Element ): Context = {
    check( element )
    new Context( elements :+ element )
  }

  def normalize( expression: LambdaExpression ): LambdaExpression =
    BetaReduction.betaNormalize( DefinitionElimination( definitions.toMap )( expression ) )

  override def apply( s: String ): babel.VarConst =
    constant( s ) match {
      case Some( c ) => babel.IsConst( Some( c.exptype ) )
      case None      => babel.IsVar( None )
    }

  def check[T: Checkable]( t: T ): Unit =
    implicitly[Checkable[T]].check( this, t )

  def ++( elements: Traversable[Element] ): Context =
    elements.foldLeft( this )( _ + _ )

  override def toString = elements.mkString( "\n" )
}

object Context {
  val empty: Context = new Context( Vector() )
  def apply(): Context = default
  def apply( elements: Traversable[Element] ): Context =
    empty ++ elements

  val withoutEquality = empty ++ Seq(
    InductiveType( "o", Top(), Bottom() ),
    ConstDecl( NegC() ), ConstDecl( AndC() ), ConstDecl( OrC() ), ConstDecl( ImpC() ),
    ConstDecl( ForallC( TVar( "x" ) ) ), ConstDecl( ExistsC( TVar( "x" ) ) )
  )
  val default = withoutEquality + ConstDecl( EqC( TVar( "x" ) ) )

  trait Element {
    def checkAdmissibility( ctx: Context ): Unit

    def tys: Vector[TBase] = Vector()
    def consts: Vector[Const] = Vector()
    def defs: Vector[( Const, LambdaExpression )] = Vector()
    def axioms: Vector[HOLSequent] = Vector()
  }
  object Element {
    implicit def fromSort( ty: TBase ): Element = Sort( ty )
    implicit def fromConst( const: Const ): Element = ConstDecl( const )
    implicit def fromDefn( defn: ( String, LambdaExpression ) ): Element =
      Definition( Const( defn._1, defn._2.exptype ), defn._2 )
    implicit def fromDefnEq( eq: HOLFormula ): Element = eq match {
      case Eq( Apps( VarOrConst( name, ty ), vars ), by ) =>
        Definition( Const( name, ty ), Abs.Block( vars.map( _.asInstanceOf[Var] ), by ) )
    }
    implicit def fromAxiom( axiom: HOLSequent ): Element = Axiom( axiom )
  }

  /** Definition of a base type.  Either [[Sort]] or [[InductiveType]]. */
  sealed trait TypeDef extends Element {
    def ty: TBase
    override def tys = Vector( ty )
  }
  /** Uninterpreted base type. */
  case class Sort( ty: TBase ) extends TypeDef {
    def checkAdmissibility( ctx: Context ) = {
      require( ctx.typeDef( ty ).isEmpty, s"Type ${ty.name} is already defined as ${ctx.typeDef( ty ).get}." )
    }
  }
  /** Inductive base type with constructors. */
  case class InductiveType( ty: TBase, constructors: Vector[Const] ) extends TypeDef {
    for ( constr <- constructors ) {
      val FunctionType( ty_, _ ) = constr.exptype
      require(
        ty == ty_,
        s"Base type $ty and type constructor $constr don't agree."
      )
    }

    override def consts = constructors

    def checkAdmissibility( ctx: Context ) = {
      require(
        constructors.map( _.name ) == constructors.map( _.name ).distinct,
        s"Names of type constructors are not distinct."
      )
      ctx + Sort( ty ) ++ constructors.map( ConstDecl )
    }
  }

  object Sort {
    def apply( tyName: String ): Sort = Sort( TBase( tyName ) )
  }
  object InductiveType {
    def apply( ty: TBase, constructors: Seq[Const] ): InductiveType =
      InductiveType( ty, constructors.toVector )
    def apply( tyName: String, constructors: Const* ): InductiveType =
      InductiveType( TBase( tyName ), constructors )
  }

  case class ConstDecl( const: Const ) extends Element {
    override def consts = Vector( const )
    def checkAdmissibility( ctx: Context ) = {
      require(
        ctx.constant( const.name ).isEmpty,
        s"Constant $const is already defined as ${ctx.constant( const.name ).get}."
      )
      ctx.check( const.exptype )
    }
  }

  case class Definition( what: Const, by: LambdaExpression ) extends Element {
    val Const( name, ty ) = what
    require( ty == by.exptype )
    require( freeVariables( by ).isEmpty, s"$this: contains free variables ${freeVariables( by )}" )

    override def consts = Vector( what )
    override def defs = Vector( what -> by )

    def checkAdmissibility( ctx: Context ) = {
      ctx.check( ConstDecl( what ) )
      ctx.check( by )
    }
  }

  case class Axiom( sequent: HOLSequent ) extends Element {
    override def axioms = Vector( sequent )

    def checkAdmissibility( ctx: Context ) =
      sequent.foreach( ctx.check( _ ) )
  }

  case class SkolemFun( sym: Const, defn: LambdaExpression ) extends Element {
    val Abs.Block( argumentVariables, strongQuantifier @ Quant( boundVariable, matrix, isForall ) ) = defn
    require( sym.exptype == FunctionType( boundVariable.exptype, argumentVariables.map( _.exptype ) ) )
    require( freeVariables( defn ).isEmpty )

    override def consts = Vector( sym )

    def checkAdmissibility( ctx: Context ) = {
      ctx.check( ConstDecl( sym ) )
      ctx.check( defn )
    }
  }

  val iTypeDef = Sort( "i" )
}
