package at.logic.gapt.proofs

import at.logic.gapt.expr.{ Expr, Definition => EDefinition, _ }
import at.logic.gapt.formats.babel.BabelSignature
import Context._
import at.logic.gapt.expr.hol.SkolemFunctions
import at.logic.gapt.proofs.lk.LKProof

import scala.reflect.ClassTag

/**
 * Captures constants, types, definitions, and background theory used in a proof.
 *
 * Each of these different kinds of information is stored in a separate [[Facet]]
 * of the context.  Each modification or addition to the context is recorded as
 * an [[Update]].  Adding information is only possible by adding it as an [[Update]].
 * (Basically a Context is an extensible LCF-style kernel.)
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
class Context private ( val state: State, val updates: List[Update] ) extends BabelSignature {
  /** Gets a facet of this context, initializing it if it is not present yet. */
  def get[T: Facet]: T = state.get[T]

  def constants: Iterable[Const] = get[Constants].constants.values
  def definitions: Map[Const, Expr] =
    for {
      ( what, by ) <- get[Definitions].definitions
      whatC <- constant( what )
    } yield whatC -> by
  def axioms: Set[HOLSequent] = get[Axioms].axioms

  /** Returns Some(const) if name is a constant. */
  def constant( name: String ): Option[Const] = get[Constants].constants.get( name )

  /** Returns Some(ctrs) if name is an inductive type with constructors ctrs. */
  def getConstructors( ty: TBase ): Option[Vector[Const]] =
    for {
      declT <- get[BaseTypes].baseTypes.get( ty.name )
      ctrs <- get[StructurallyInductiveTypes].constructors.get( ty.name )
      subst <- syntacticMatching( declT, ty )
    } yield ctrs.map( subst( _ ).asInstanceOf[Const] )

  /** Returns true iff ty is a defined base type. */
  def isType( ty: TBase ): Boolean = (
    for {
      declT <- get[BaseTypes].baseTypes.get( ty.name )
      _ <- syntacticMatching( declT, ty )
    } yield ()
  ).isDefined

  /** Returns Some(expandedDefinition) if c is a defined constant. */
  def definition( c: Const ): Option[Expr] =
    for {
      defC <- get[Constants].constants.get( c.name )
      subst <- syntacticMatching( defC, c )
      defn <- get[Definitions].definitions.get( c.name )
    } yield subst( defn )

  /** Returns a collection of all (expression-level) reduction rules of this context. */
  def reductionRules: Iterable[ReductionRule] = state.getAll[ReductionRule]

  /** Returns true iff the context contains the definition defn (the definitional expansion has to match as well). */
  def contains( defn: EDefinition ): Boolean =
    definition( defn.what ).contains( defn.by )

  /** Returns the Skolem definition of skSym.  See [[at.logic.gapt.expr.hol.SkolemFunctions]]. */
  def skolemDef( skSym: Const ): Option[Expr] =
    get[SkolemFunctions].skolemDefs.get( skSym )

  /**
   * Adds an element to the context.
   *
   * If this is not a valid addition, then an exception is thrown.
   */
  def +( update: Update ): Context =
    new Context( update( this ), update :: updates )

  def normalizer = {
    val redRules = reductionRules.toVector
    new Normalizer( if ( redRules.isEmpty ) BetaReduction else ReductionRule( BetaReduction +: redRules ) )
  }

  /** Normalizes an expression with the reduction rules stored in this context. */
  def normalize( expression: Expr ): Expr =
    normalizer.normalize( expression )

  def isDefEq( a: Expr, b: Expr ): Boolean =
    normalizer.isDefEq( a, b )

  def signatureLookup( s: String ): BabelSignature.VarConst =
    constant( s ) match {
      case Some( c ) => BabelSignature.IsConst( c.ty )
      case None      => BabelSignature.IsVar
    }

  def check[T: Checkable]( t: T ): Unit =
    implicitly[Checkable[T]].check( this, t )

  def ++( updates: Traversable[Update] ): Context =
    updates.foldLeft( this )( _ + _ )

  override def toString =
    s"${state}Updates:\n${updates.view.reverse.map( x => s"  $x\n" ).mkString}"
}

object Context {
  /** Type class for a facet of a context. */
  trait Facet[T] {
    def clazz: Class[T]
    def initial: T
  }
  object Facet {
    def apply[T: ClassTag]( initialValue: T ): Facet[T] = {
      val clazz_ = implicitly[ClassTag[T]].runtimeClass.asInstanceOf[Class[T]]
      new Facet[T] {
        def initial = initialValue
        def clazz = clazz_
        override def toString = clazz.getSimpleName
      }
    }
  }

  /**
   * The state of a context.
   *
   * A context remembers both its history (what elements were added to it),
   * as well as their effect: the current state (the values of the facets).
   *
   * State is basically a Cartesian product of all possible facets, where all except
   * finitely many facets still have their initial value.  The [[get]] method returns
   * the value of a facet, the [[update]] method changes the value.
   */
  class State private ( private val facets: Map[Facet[_], Any] ) {
    def update[T: Facet]( f: T => T ): State =
      new State( facets.updated( implicitly[Facet[T]], f( get[T] ) ) )

    def get[T: Facet]: T =
      facets.getOrElse( implicitly[Facet[T]], implicitly[Facet[T]].initial ).asInstanceOf[T]

    def getAll[T: ClassTag]: Iterable[T] =
      facets.values.collect { case t: T => t }

    override def toString: String = {
      val s = new StringBuilder
      for ( ( f, d ) <- facets.toSeq.sortBy( _._1.toString ) ) {
        s ++= s"$f:"
        val dStr = d.toString
        if ( dStr.contains( "\n" ) ) {
          s.append( "\n  " ).append( dStr.replace( "\n", "\n  " ) )
        } else {
          s.append( " " ).append( dStr )
        }
        s ++= "\n\n"
      }
      s.result()
    }
  }
  object State {
    def apply(): State = new State( Map() )
  }

  /** Base types, including inductive types. */
  case class BaseTypes( baseTypes: Map[String, TBase] ) {
    def +( ty: TBase ): BaseTypes = {
      require( ty.params.forall( _.isInstanceOf[TVar] ) && ty.params == ty.params.distinct )
      require(
        !baseTypes.contains( ty.name ),
        s"Base type $ty already defined."
      )
      copy( baseTypes + ( ty.name -> ty ) )
    }
    override def toString = baseTypes.toSeq.sortBy( _._1 ).map( _._2 ).mkString( ", " )
  }
  implicit val baseTypesFacet: Facet[BaseTypes] = Facet( BaseTypes( Map() ) )

  /** Constant symbols, including defined constants, constructors, etc. */
  case class Constants( constants: Map[String, Const] ) {
    def +( const: Const ): Constants = {
      require(
        !constants.contains( const.name ),
        s"Constant $const is already defined as ${constants( const.name )}."
      )
      copy( constants + ( const.name -> const ) )
    }

    def ++( consts: Traversable[Const] ): Constants =
      consts.foldLeft( this )( _ + _ )

    override def toString = constants.values.map( c => s"${c.name}: ${c.ty}" ).mkString( "\n" )
  }
  implicit val constsFacet: Facet[Constants] = Facet( Constants( Map() ) )

  /** Definitions that define a constant by an expression of the same type. */
  case class Definitions( definitions: Map[String, Expr] ) extends ReductionRule {
    def +( defn: EDefinition ) = {
      require( !definitions.contains( defn.what.name ) )
      copy( definitions + ( defn.what.name -> defn.by ) )
    }

    override def reduce( normalizer: Normalizer, head: Expr, args: List[Expr] ): Option[( Expr, List[Expr] )] =
      head match {
        case Const( n, t ) if definitions.contains( n ) =>
          val by = definitions( n )
          val Some( subst ) = syntacticMatching( by.ty, t )
          Some( subst( by ) -> args )
        case _ => None
      }

    override def toString = definitions.toSeq.sortBy( _._1 ).
      map { case ( w, b ) => s"$w -> $b" }.mkString( "\n" )

    def filter( p: ( ( String, Expr ) ) => Boolean ): Definitions =
      copy( definitions.filter( p ) )
  }
  implicit val defsFacet: Facet[Definitions] = Facet( Definitions( Map() ) )

  /** Theory axioms for LK proofs. */
  case class Axioms( axioms: Set[HOLSequent] ) {
    def +( ax: HOLSequent ) = copy( axioms + ax )
    override def toString = axioms.mkString( "\n" )
  }
  implicit val axiomsFacet: Facet[Axioms] = Facet( Axioms( Set[HOLSequent]() ) )

  /** Inductive types, for each type we store its list of constructors. */
  case class StructurallyInductiveTypes( constructors: Map[String, Vector[Const]] ) {
    def +( ty: String, ctrs: Vector[Const] ) =
      copy( constructors + ( ty -> ctrs ) )

    override def toString: String = constructors.toSeq.sortBy( _._1 ).
      map { case ( t, cs ) => s"$t: ${cs.mkString( ", " )}" }.mkString( "\n" )
  }
  implicit val structIndTysFacet: Facet[StructurallyInductiveTypes] = Facet( StructurallyInductiveTypes( Map() ) )

  val empty: Context = new Context( State(), List() )
  def apply(): Context = default
  def apply( updates: Traversable[Update] ): Context =
    empty ++ updates

  val withoutEquality = empty ++ Seq(
    InductiveType( "o", Top(), Bottom() ),
    ConstDecl( NegC() ), ConstDecl( AndC() ), ConstDecl( OrC() ), ConstDecl( ImpC() ),
    ConstDecl( ForallC( TVar( "x" ) ) ), ConstDecl( ExistsC( TVar( "x" ) ) )
  )
  val default = withoutEquality + ConstDecl( EqC( TVar( "x" ) ) )

  case class ProofNames( names: Map[String, ( Expr, HOLSequent )] ) {
    def +( name: String, referencedExpression: Expr, referencedSequent: HOLSequent ) = copy( names + ( ( name, ( referencedExpression, referencedSequent ) ) ) )
  }

  implicit val ProofsFacet: Facet[ProofNames] = Facet( ProofNames( Map[String, ( Expr, HOLSequent )]() ) )

  case class ProofDefinitions( components: Map[String, Set[( Expr, LKProof )]] ) {
    def +( name: String, referencedExpression: Expr, referencedProof: LKProof ) =
      copy( components + ( ( name, ( components.getOrElse( name, Set() ) + ( ( referencedExpression, referencedProof ) ) ) ) ) )

  }
  implicit val ProofDefinitionsFacet: Facet[ProofDefinitions] = Facet( ProofDefinitions( Map[String, Set[( Expr, LKProof )]]() ) )

  /**
   * Update of a context.
   *
   * An update stores (potentially multiple) modifications to a [[Context]].
   * It is represented by a function that takes a [[Context]], and returns the modified [[State]].
   */
  trait Update {
    /**
     * Applies the modifications of this update to ctx.
     *
     * Throws an exception if the modifications are invalid (for example if we would redefine a constant).
     */
    def apply( ctx: Context ): State
  }
  object Update {
    implicit def fromSort( ty: TBase ): Update = Sort( ty )
    implicit def fromConst( const: Const ): Update = ConstDecl( const )
    implicit def fromDefn( defn: ( String, Expr ) ): Update =
      Definition( EDefinition( Const( defn._1, defn._2.ty ), defn._2 ) )
    implicit def fromDefnEq( eq: Formula ): Update = eq match {
      case Eq( Apps( VarOrConst( name, ty ), vars ), by ) =>
        Definition( EDefinition( Const( name, ty ), Abs.Block( vars.map( _.asInstanceOf[Var] ), by ) ) )
    }
    implicit def fromAxiom( axiom: HOLSequent ): Update = Axiom( axiom )
  }

  /** Definition of a base type.  Either [[Sort]] or [[InductiveType]]. */
  sealed trait TypeDef extends Update {
    def ty: TBase
  }
  /** Uninterpreted base type. */
  case class Sort( ty: TBase ) extends TypeDef {
    override def apply( ctx: Context ): State =
      ctx.state.update[BaseTypes]( _ + ty )
  }
  /** Inductive base type with constructors. */
  case class InductiveType( ty: TBase, constructors: Vector[Const] ) extends TypeDef {
    for ( constr <- constructors ) {
      val FunctionType( ty_, _ ) = constr.ty
      require(
        ty == ty_,
        s"Base type $ty and type constructor $constr don't agree."
      )
      require( typeVariables( constr ) subsetOf typeVariables( ty ) )
    }
    require(
      constructors.map( _.name ) == constructors.map( _.name ).distinct,
      s"Names of type constructors are not distinct."
    )

    override def apply( ctx: Context ): State = {
      require( !ctx.isType( ty ), s"Type $ty already defined" )
      for ( Const( ctr, FunctionType( _, fieldTys ) ) <- constructors ) {
        require( ctx.constant( ctr ).isEmpty, s"Constructor $ctr is already a declared constant" )
        for ( fieldTy <- fieldTys ) {
          if ( fieldTy == ty ) {
            // positive occurrence of the inductive type
          } else {
            ctx.check( fieldTy )
          }
        }
      }
      ctx.state.update[BaseTypes]( _ + ty )
        .update[Constants]( _ ++ constructors )
        .update[StructurallyInductiveTypes]( _ + ( ty.name, constructors ) )
    }
  }

  object Sort {
    def apply( tyName: String ): Sort = Sort( TBase( tyName ) )
  }
  object InductiveType {
    def apply( ty: Ty, constructors: Const* ): InductiveType =
      InductiveType( ty.asInstanceOf[TBase], constructors.toVector )
    def apply( tyName: String, constructors: Const* ): InductiveType =
      InductiveType( TBase( tyName ), constructors: _* )
  }

  case class ConstDecl( const: Const ) extends Update {
    override def apply( ctx: Context ): State = {
      ctx.check( const.ty )
      ctx.state.update[Constants]( _ + const )
    }
  }

  case class Definition( definition: EDefinition ) extends Update {
    override def apply( ctx: Context ): State = {
      ctx.check( definition.what.ty )
      ctx.check( definition.by )
      ctx.state.update[Constants]( _ + definition.what )
        .update[Definitions]( _ + definition )
    }
  }

  case class Axiom( sequent: HOLSequent ) extends Update {
    override def apply( ctx: Context ): State = {
      sequent.foreach( ctx.check( _ ) )
      ctx.state.update[Axioms]( _ + sequent )
    }
  }

  implicit val skolemFunsFacet: Facet[SkolemFunctions] = Facet[SkolemFunctions]( SkolemFunctions( None ) )

  case class SkolemFun( sym: Const, defn: Expr ) extends Update {
    val Abs.Block( argumentVariables, strongQuantifier @ Quant( boundVariable, matrix, isForall ) ) = defn
    require( sym.ty == FunctionType( boundVariable.ty, argumentVariables.map( _.ty ) ) )
    require( freeVariables( defn ).isEmpty )

    override def apply( ctx: Context ): State = {
      ctx.check( sym.ty )
      ctx.check( defn )
      ctx.state.update[Constants]( _ + sym )
        .update[SkolemFunctions]( _ + ( sym, defn ) )
    }
  }

  case class ProofNameDeclaration( lhs: Expr, endSequent: HOLSequent ) extends Update {
    override def apply( ctx: Context ): State = {
      endSequent.foreach( ctx.check( _ ) )
      val Apps( Const( c, _ ), vs ) = lhs
      require( !ctx.get[ProofNames].names.keySet.contains( c ) )
      require( vs == vs.distinct )
      require( vs.forall( _.isInstanceOf[Var] ) )
      require( freeVariables( endSequent ) == vs.toSet )
      ctx.state.update[ProofNames]( _ + ( c, lhs, endSequent ) )
    }
  }

  case class ProofDefinitionDeclaration( lhs: Expr, referencedProof: LKProof ) extends Update {
    override def apply( ctx: Context ): State = {
      referencedProof.endSequent.foreach( ctx.check( _ ) )
      val Apps( at.logic.gapt.expr.Const( c, t ), vs ) = lhs
      vs.foreach( ctx.check( _ ) )
      require( ctx.get[ProofNames].names.values.exists {
        case ( name, _ ) => syntacticMatching( name, lhs ).isDefined
      } )
      ctx.state.update[ProofDefinitions]( _ + ( c, lhs, referencedProof ) )
    }
  }
}
