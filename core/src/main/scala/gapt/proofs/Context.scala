package gapt.proofs

import gapt.expr._
import gapt.expr.fol.folSubTerms
import gapt.expr.hol.SkolemFunctions
import gapt.formats.babel.BabelParser
import gapt.formats.babel.BabelSignature
import gapt.formats.babel.Notation
import gapt.formats.babel.Notations
import gapt.formats.babel.Precedence
import gapt.proofs.Context.BaseTypes
import gapt.proofs.Context.Constants
import gapt.proofs.Context.Definitions
import gapt.proofs.Context.Facet
import gapt.proofs.Context.Reductions
import gapt.proofs.Context.SkolemFun
import gapt.proofs.Context.Sort
import gapt.proofs.Context.State
import gapt.proofs.Context.StructurallyInductiveTypes
import gapt.proofs.Context.Update
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.ProofLink
import gapt.proofs.resolution.ResolutionProof
import gapt.utils.NameGenerator
import gapt.utils.linearizeStrictPartialOrder

import scala.reflect.ClassTag

/**
 * Captures constants, types, definitions, and background theory used in a proof.
 *
 * Each of these different kinds of information is stored in a separate [[Context.Facet]]
 * of the context.  Each modification or addition to the context is recorded as
 * an [[Context.Update]].  Adding information is only possible by adding it as an [[Context.Update]].
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
 *  - [[gapt.proofs.expansion.ExpansionProofToLK]] uses the information about the background theory
 *    to produce LK proofs modulo the background theory.
 */
sealed trait Context extends BabelSignature {
  def state: State
  def updates: List[Update]
  def toImmutable: ImmutableContext

  def newMutable: MutableContext = new MutableContext( toImmutable )
  def toReadonly: ReadonlyMutableContext = new ReadonlyMutableContext( toImmutable )

  /** Gets a facet of this context, initializing it if it is not present yet. */
  def get[T: Facet]: T = state.get[T]

  def constants: Iterable[Const] = get[Constants].constants.values
  def definitions: Map[Const, Expr] =
    for {
      ( what, by ) <- get[Definitions].definitions
      whatC <- constant( what )
    } yield whatC -> by

  /** Returns Some(const) if name is a constant. */
  def constant( name: String ): Option[Const] = get[Constants].constants.get( name )

  /** Returns Some(const) if (name,params) defines a constant. */
  def constant( name: String, params: List[Ty] ): Option[Const] =
    get[Constants].lookup( name, params )

  /** Returns Some(ctrs) if name is an inductive type with constructors ctrs. */
  def getConstructors( ty: Ty ): Option[Vector[Const]] =
    ty match {
      case ty @ TBase( _, _ ) => getConstructors( ty )
      case _                  => None
    }

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
    } yield () ).isDefined

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
  def contains( defn: Definition ): Boolean =
    definition( defn.what ).contains( defn.by )

  /** Returns the Skolem definition of skSym.  See [[gapt.expr.hol.SkolemFunctions]]. */
  def skolemDef( skSym: Const ): Option[Expr] =
    get[SkolemFunctions].skolemDefs.get( skSym )

  /**
   * Adds an element to the context.
   *
   * If this is not a valid addition, then an exception is thrown.
   */
  def +( update: Update ): ImmutableContext =
    toImmutable + update

  def normalizer = get[Reductions].normalizer

  /** Normalizes an expression with the reduction rules stored in this context. */
  def normalize( expression: Expr ): Expr =
    normalizer.normalize( expression )

  def whnf( expression: Expr ): Expr =
    normalizer.whnf( expression )

  def isDefEq( a: Expr, b: Expr ): Boolean =
    normalizer.isDefEq( a, b )

  def signatureLookup( s: String ): BabelSignature.VarConst =
    constant( s ) match {
      case Some( c ) => BabelSignature.IsConst( c )
      case None      => BabelSignature.IsVar
    }
  def notationsForToken( token: Notation.Token ): Option[Notation] = get[Notations].byToken.get( token )
  def notationsForConst( const: Notation.ConstName ): List[Notation] = get[Notations].byConst( const )
  def defaultTypeToI: Boolean = false

  def check[T: Checkable]( t: T ): Unit =
    implicitly[Checkable[T]].check( t )( this )

  def ++( updates: Traversable[Update] ): ImmutableContext =
    updates.foldLeft( toImmutable )( _ + _ )

  def names: Iterable[String] = constants.map( _.name ) ++ get[BaseTypes].baseTypes.keySet
  def newNameGenerator: NameGenerator = new NameGenerator( names )

  override def toString =
    s"${state}Updates:\n${updates.view.reverse.map( x => s"  $x\n" ).mkString}"
}

class ImmutableContext private ( val state: State, val updates: List[Update] ) extends Context {
  def toImmutable: ImmutableContext = this

  /**
   * Adds an element to the context.
   *
   * If this is not a valid addition, then an exception is thrown.
   */
  override def +( update: Update ): ImmutableContext =
    new ImmutableContext( update( this ), update :: updates )
}
object ImmutableContext {
  val empty = new ImmutableContext( State(), Nil )
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
        s"Base type $ty already defined." )
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
        s"Constant $const is already defined as ${constants( const.name )}." )
      copy( constants + ( const.name -> const ) )
    }

    def ++( consts: Traversable[Const] ): Constants =
      consts.foldLeft( this )( _ + _ )

    def lookup( name: String, params: List[Ty] ): Option[Const] =
      constants.get( name ).flatMap {
        case c @ Const( _, _, Nil ) if params.isEmpty => Some( c )
        case Const( _, ty, declPs ) if declPs.size == params.size =>
          val subst = Substitution( Nil, declPs.asInstanceOf[List[TVar]] zip params )
          Some( Const( name, subst( ty ), params ) )
        case _ => None
      }

    override def toString = constants.values.toSeq.sortBy( _.name ).
      map( c => s"${c.name}${if ( c.params.isEmpty ) "" else c.params.mkString( "{", " ", "}" )}: ${c.ty}" ).mkString( "\n" )
  }
  implicit val constsFacet: Facet[Constants] = Facet( Constants( Map() ) )

  /** Definitional reductions. */
  case class Reductions( normalizer: Normalizer ) {
    def ++( rules: Vector[ReductionRule] ): Reductions =
      copy( Normalizer( normalizer.rules ++ rules ) )

    def +( reductionRule: ReductionRule ): Reductions =
      copy( normalizer + reductionRule )

    override def toString: String =
      normalizer.rules.map { case ReductionRule( lhs, rhs ) => s"$lhs -> $rhs" }.mkString( "\n" )
  }
  implicit val reductionsFacet: Facet[Reductions] = Facet( Reductions( Normalizer( Set() ) ) )

  /** Definitions that define a constant by an expression of the same type. */
  case class Definitions( definitions: Map[String, Expr] ) {
    def +( defn: Definition ) = {
      require( !definitions.contains( defn.what.name ) )
      copy( definitions + ( defn.what.name -> defn.by ) )
    }

    override def toString = definitions.toSeq.sortBy( _._1 ).
      map { case ( w, b ) => s"$w -> $b" }.mkString( "\n" )

    def filter( p: ( ( String, Expr ) ) => Boolean ): Definitions =
      copy( definitions.filter( p ) )
  }
  implicit val defsFacet: Facet[Definitions] = Facet( Definitions( Map() ) )

  /** Inductive types, for each type we store its list of constructors. */
  case class StructurallyInductiveTypes( constructors: Map[String, Vector[Const]] ) {
    def +( ty: String, ctrs: Vector[Const] ) =
      copy( constructors + ( ty -> ctrs ) )

    override def toString: String = constructors.toSeq.sortBy( _._1 ).
      map { case ( t, cs ) => s"$t: ${cs.mkString( ", " )}" }.mkString( "\n" )
  }
  implicit val structIndTysFacet: Facet[StructurallyInductiveTypes] = Facet( StructurallyInductiveTypes( Map() ) )

  val empty: ImmutableContext = ImmutableContext.empty
  def apply(): ImmutableContext = default
  def apply( updates: Traversable[Update] ): ImmutableContext =
    empty ++ updates

  val default = empty ++ Seq(
    InductiveType( To, Top(), Bottom() ),
    Notation.Alias( "true", TopC ), Notation.Alias( "⊤", TopC ),
    Notation.Alias( "false", BottomC ), Notation.Alias( "⊥", BottomC ),
    ConstDecl( NegC() ),
    Notation.Prefix( "-", NegC, Precedence.neg ),
    Notation.Prefix( "~", NegC, Precedence.neg ),
    Notation.Prefix( "¬", NegC, Precedence.neg ),
    ConstDecl( AndC() ),
    Notation.Infix( "&", AndC, Precedence.conj ),
    Notation.Infix( "∧", AndC, Precedence.conj ),
    ConstDecl( OrC() ),
    Notation.Infix( "|", OrC, Precedence.disj ),
    Notation.Infix( "∨", OrC, Precedence.disj ),
    ConstDecl( ImpC() ),
    Notation.Infix( "->", ImpC, Precedence.impl, leftAssociative = false ),
    Notation.Infix( "⊃", ImpC, Precedence.impl, leftAssociative = false ),
    Notation.Infix( "→", ImpC, Precedence.impl, leftAssociative = false ),
    Notation.Infix( Notation.Token( "<->" ), Notation.IffName, Precedence.iff ),
    Notation.Infix( Notation.Token( "↔" ), Notation.IffName, Precedence.iff ),
    ConstDecl( ForallC( TVar( "x" ) ) ),
    Notation.Quantifier( Notation.Token( "!" ), ForallC, Precedence.quant ),
    Notation.Quantifier( Notation.Token( "∀" ), ForallC, Precedence.quant ),
    ConstDecl( ExistsC( TVar( "x" ) ) ),
    Notation.Quantifier( Notation.Token( "?" ), ExistsC, Precedence.quant ),
    Notation.Quantifier( Notation.Token( "∃" ), ExistsC, Precedence.quant ),
    ConstDecl( EqC( TVar( "x" ) ) ),
    Notation.Infix( "=", EqC, Precedence.infixRel ),
    Notation.Infix( "!=", Notation.NeqName, Precedence.infixRel ) )

  case class ProofNames( names: Map[String, ( Expr, HOLSequent )] ) {
    def +( name: String, referencedExpression: Expr, referencedSequent: HOLSequent ) = copy( names + ( ( name, ( referencedExpression, referencedSequent ) ) ) )

    def sequents: Iterable[HOLSequent] =
      for ( ( _, ( _, seq ) ) <- names ) yield seq

    def lookup( name: Expr ): Option[HOLSequent] =
      ( for {
        ( declName, declSeq ) <- names.values
        subst <- syntacticMatching( declName, name )
      } yield subst( declSeq ) ).headOption

    def link( name: Expr ): Option[ProofLink] =
      for ( sequent <- lookup( name ) ) yield ProofLink( name, sequent )

    def find( seq: HOLSequent ): Option[Expr] =
      ( for {
        ( declName, declSeq ) <- names.values
        subst <- clauseSubsumption( declSeq, seq, multisetSubsumption = true )
      } yield subst( declName ) ).headOption

    override def toString: String =
      names.toSeq.sortBy( _._1 ).
        map { case ( _, ( lhs, sequent ) ) => s"$lhs: $sequent" }.
        mkString( "\n" )
  }

  implicit val ProofsFacet: Facet[ProofNames] = Facet( ProofNames( Map[String, ( Expr, HOLSequent )]() ) )

  case class ProofDefinition( proofNameTerm: Expr, connector: SequentConnector, proof: LKProof ) {
    val Apps( Const( proofName, _, _ ), _ ) = proofNameTerm
  }

  case class ProofDefinitions( components: Map[String, Set[ProofDefinition]] ) {
    def +( defn: ProofDefinition ) =
      copy( components.updated(
        defn.proofName,
        components.getOrElse( defn.proofName, Set() ) + defn ) )

    def findWithConnector( name: Expr ): Iterable[( SequentConnector, Substitution, LKProof )] =
      for {
        defs <- components.values
        defn <- defs
        subst <- syntacticMatching( defn.proofNameTerm, name )
      } yield ( defn.connector, subst, defn.proof )

    def find( name: Expr ): Iterable[( LKProof, Substitution )] =
      for ( ( _, subst, proof ) <- findWithConnector( name ) ) yield ( proof, subst )
    override def toString: String =
      components.map { case ( n, dfs ) => dfs.map( _.proofNameTerm ).mkString( ", " ) }.mkString( "\n" )
  }
  implicit val ProofDefinitionsFacet: Facet[ProofDefinitions] = Facet( ProofDefinitions( Map() ) )

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
      Definition( Const( defn._1, defn._2.ty ), defn._2 )
    implicit def fromDefnEq( eq: Formula ): Update = eq match {
      case Eq( Apps( VarOrConst( name, ty, ps ), vars ), by ) =>
        Definition( Const( name, ty, ps ), Abs.Block( vars.map( _.asInstanceOf[Var] ), by ) )
    }
    implicit def fromAxiom( axiom: ( String, HOLSequent ) ): Update = {
      val fvs = freeVariables( axiom._2 ).toVector.sortBy( _.toString )
      val name = Const( axiom._1, FunctionType( Ti, fvs.map( _.ty ) ) )( fvs )
      ProofNameDeclaration( name, axiom._2 )
    }
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
    val params: List[TVar] = ty.params.map( _.asInstanceOf[TVar] )
    for ( constr <- constructors ) {
      val FunctionType( ty_, _ ) = constr.ty
      require(
        ty == ty_,
        s"Base type $ty and type constructor $constr don't agree." )
      require( constr.params == params )
      require( typeVariables( constr ) subsetOf params.toSet )
    }
    require(
      constructors.map( _.name ) == constructors.map( _.name ).distinct,
      s"Names of type constructors are not distinct." )

    val baseCases = constructors.find { case Const( _, FunctionType( _, argTys ), _ ) => !argTys.contains( ty ) }
    require(
      baseCases.nonEmpty,
      s"Inductive type is empty, all of the constructors are recursive: ${constructors.mkString( ", " )}" )

    override def apply( ctx: Context ): State = {
      require( !ctx.isType( ty ), s"Type $ty already defined" )
      for ( Const( ctr, FunctionType( _, fieldTys ), ctrPs ) <- constructors ) {
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
      for ( p <- const.params ) require( p.isInstanceOf[TVar] )
      require( typeVariables( const ).toSet subsetOf const.params.toSet )
      ctx.state.update[Constants]( _ + const )
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

  case class PrimRecFun(
      c:         Const,
      nArgs:     Int,
      recIdx:    Int,
      equations: Vector[( Expr, Expr )] ) extends Update {

    PrimitiveRecursiveFunctionValidator.validate( this )

    private val Const( _, FunctionType( _, argTypes ), _ ) = c

    val recursionType: TBase = argTypes( recIdx ).asInstanceOf[TBase]

    /**
     * Adds this primitive recursive function definition to a context.
     *
     * @param ctx The context to which this function definition is to be added.
     * @return Returns the new context state resulting from the addition of
     * this function definition to the current state of `ctx`. An exception is
     * thrown if number of equations does not equal the number of constructors
     * of the recursion type, or if the order of the equations does not
     * correspond to the order of constructors of the recursion type.
     */
    override def apply( ctx: Context ): State = {
      val ctx_ = ctx + c
      val ctrs =
        ctx.get[StructurallyInductiveTypes].constructors( recursionType.name )
      require( equations.size == ctrs.size )
      for ( ( ( lhs @ Apps( _, lhsArgs ), rhs ), ctr ) <- equations.zip( ctrs ) ) {
        ctx_.check( lhs )
        ctx_.check( rhs )
        val Apps( Const( ctr_, _, _ ), _ ) = lhsArgs( recIdx )
        require( ctr_ == ctr.name )
      }
      ctx.state.update[Constants]( _ + c )
        .update[Reductions]( _ ++ equations.map( ReductionRule.apply ) )
    }
  }

  object PrimitiveRecursiveFunctionValidator {

    private type Equation = ( Expr, Expr )

    /**
     * Checks whether the given definition is syntactically well-formed.
     *
     * @param input The definition to be checked.
     * @return Returns unit if the definition is well-formed, otherwise
     *         an exception is thrown.
     */
    def validate( input: PrimRecFun ): Unit = {

      val PrimRecFun( c, nArgs, recIdx, equations ) = input
      val typeVars: Set[TVar] = typeVariables( c.ty )
      val Const( name, FunctionType( _, argTypes ), _ ) = c

      require( 0 <= recIdx && recIdx < nArgs && nArgs <= argTypes.size )

      def validateEquation( input: Equation ): Unit = {

        val ( lhs, rhs ) = input

        require( lhs.ty == rhs.ty )
        require( typeVariables( lhs.ty ) subsetOf typeVars )
        require( typeVariables( rhs.ty ) subsetOf typeVars )

        val Apps( `c`, lhsArgs ) = lhs
        require( lhsArgs.size == nArgs )

        val nonRecLhsArgs =
          lhsArgs.zipWithIndex.filter( _._2 != recIdx ).map( _._1 )
        val Apps( Const( _, _, _ ), ctrArgs ) = lhsArgs( recIdx )

        val matchVars = nonRecLhsArgs ++ ctrArgs

        matchVars.foreach( a => { require( a.isInstanceOf[Var] ) } )
        require( matchVars == matchVars.distinct )

        folSubTerms( rhs ).foreach {
          case Apps( fn @ Const( `name`, _, _ ), args ) =>
            require( fn == c )
            require( ctrArgs.contains( args( recIdx ) ) )
          case _ =>
        }
      }

      for ( equation <- equations ) {
        validateEquation( equation )
      }
    }
  }

  object PrimRecFun {

    /**
     * Constructs a primitive recursive function definition.
     *
     * @param c The constant that is to be defined primitive recursively.
     * @param equations Oriented equations that define the constant c by
     * primitive recursion.
     * @param ctx The context in which the constant is to be defined.
     * @return A primitive function definition if `c` and `euqations` represent
     * a valid primitive function definition in the context `ctx`.
     */
    def apply(
      constant:  Const,
      equations: Iterable[( Expr, Expr )] )(
      implicit
      ctx: Context ): PrimRecFun = {

      val ( arity, recIdx ) = equations.head._1 match {
        case Apps( _, args ) =>
          args.size -> args.indexWhere( !_.isInstanceOf[Var] )
      }

      val Const( _, FunctionType( _, argTys ), _ ) = constant
      val equationsByConst = equations.groupBy {
        case ( ( Apps( _, args ), _ ) ) =>
          val Apps( ctr, _ ) = args( recIdx )
          ctr
      }
      val Some( recCtrs ) = ctx.getConstructors( argTys( recIdx ) )

      PrimRecFun(
        constant, arity, recIdx, recCtrs.map( equationsByConst( _ ).head ) )
    }

    /**
     * Constructs a primitive recursive function definition.
     *
     * @param c The constant that is to be defined primitive recursively.
     * @param equations Oriented equations that define the constant c by
     * primitive recursion.
     * @param ctx The context in which the constant is to be defined.
     * @return A primitive function definition if `c` and `euqations` represent
     * a valid primitive function definition in the context `ctx`.
     */
    def apply(
      c: Const, equations: String* )(
      implicit
      ctx: Context ): PrimRecFun = {
      val temporaryContext = ctx + c
      apply( c, equations.map { parseEquation( c, _ )( temporaryContext ) } )
    }
  }

  private object parseEquation {

    def apply(
      c: Const, equation: String )( implicit ctx: Context ): ( Expr, Expr ) = {
      BabelParser.tryParse(
        equation,
        p => preExpr.TypeAnnotation( p, preExpr.Bool ) )
        .fold( throw _, identity ) match {
          case Eq( lhs @ Apps( c_, _ ), rhs ) =>
            syntacticMatching( c_, c ).get( lhs -> rhs )
        }
    }

  }

  case object PrimitiveRecursiveFunctions {

    def apply(
      rawDefinitions: Iterable[( Const, Iterable[( Expr, Expr )] )],
      dummy:          Unit                                          = Unit )(
      implicit
      ctx: Context ): Iterable[PrimRecFun] = {

      val parsedDefinitions: Iterable[PrimRecFun] =
        rawDefinitions.map {
          case ( const, equations ) =>
            PrimRecFun( const, equations )
        }

      batch( parsedDefinitions )
    }

    def apply(
      rawDefinitions: Iterable[( Const, Seq[String] )] )(
      implicit
      ctx: Context ): Iterable[PrimRecFun] = {

      val parsingContext = ctx ++ rawDefinitions.map { d => ConstDecl( d._1 ) }

      val parsedDefinitions: Iterable[PrimRecFun] =
        rawDefinitions.map {
          case ( const, equations ) =>
            ( const, equations.map { parseEquation( const, _ )( parsingContext ) } )
        }.map {
          case ( const, equations ) =>
            PrimRecFun( const, equations )
        }

      batch( parsedDefinitions )
    }

    private def batch(
      parsedDefinitions: Iterable[PrimRecFun] )(
      implicit
      ctx: Context ): Iterable[PrimRecFun] = {

      val ordering = sortConstants(
        parsedDefinitions.map {
          definition =>
            ( definition.c, definition.equations )
        } )

      sortDefinitions( ordering, parsedDefinitions )
    }

    private def sortDefinitions(
      ordering: Iterable[Const], definitions: Iterable[PrimRecFun] ): Iterable[PrimRecFun] = {
      ordering.map { constant => definitions.find( _.c == constant ).get }
    }

    private def sortConstants(
      definitions: Iterable[( Const, Seq[( Expr, Expr )] )] ): Seq[Const] = {

      val constants = definitions.map { _._1 }

      linearizeStrictPartialOrder(
        constants,
        dependencyRelation( definitions ) ) match {
          case Left( cycle ) =>
            throw new IllegalArgumentException(
              s"cyclic dependency: ${cycle.mkString( " < " )}" )
          case Right( order ) => order.reverse
        }
    }

    private def dependencyRelation(
      definitions: Iterable[( Const, Seq[( Expr, Expr )] )] ): Set[( Const, Const )] = {
      val constants = definitions.map { _._1 }.toSet
      definitions.flatMap {
        case ( constant, equations ) =>
          val dependsOn: Set[Const] =
            equations.map { _._2 }.flatMap { extractConstant }.toSet.intersect( constants ).diff( Set( constant ) )
          dependsOn.map { ( constant, _ ) }
      }.toSet
    }

    private def extractConstant( expression: Expr ): Set[Const] = {
      expression match {
        case c @ Const( _, _, _ ) =>
          Set( c )
        case App( function, argument ) =>
          extractConstant( function ) ++ extractConstant( argument )
        case Abs( _, subexpression ) =>
          extractConstant( subexpression )
        case _ => Set()
      }
    }

  }

  case class ProofNameDeclaration( lhs: Expr, endSequent: HOLSequent ) extends Update {
    override def apply( ctx: Context ): State = {
      endSequent.foreach( ctx.check( _ ) )
      val Apps( Const( c, _, ps ), vs ) = lhs
      require( !ctx.get[ProofNames].names.keySet.contains( c ), s"proof already defined: $lhs" )
      require( vs == vs.distinct )
      require( vs.forall( _.isInstanceOf[Var] ) )
      require( ps.forall( _.isInstanceOf[TVar] ) )
      for ( fv <- freeVariables( endSequent ) )
        require( vs.contains( fv ) )
      for ( tv <- typeVariables( endSequent.toImplication ) )
        require( ps.contains( tv ) )
      ctx.state.update[ProofNames]( _ + ( c, lhs, endSequent ) )
    }
  }

  case class ProofDefinitionDeclaration( lhs: Expr, referencedProof: LKProof ) extends Update {
    override def apply( ctx: Context ): State = {
      ctx.check( referencedProof )
      val Apps( c: Const, vs ) = lhs
      vs.foreach( ctx.check( _ ) )
      val declSeq = ctx.get[ProofNames].lookup( lhs )
        .getOrElse( throw new IllegalArgumentException( s"Proof name ${lhs.toSigRelativeString( ctx )} is not defined" ) )
      require(
        referencedProof.conclusion.isSubMultisetOf( declSeq ),
        "End-sequent of proof definition does not match declaration.\n" +
          "Given sequent: " + referencedProof.endSequent.toSigRelativeString( ctx ) + "\n" +
          "Expected sequent: " + declSeq.toSigRelativeString( ctx ) + "\n" +
          "Extraneous formulas: " +
          referencedProof.endSequent.diff( declSeq ).toSigRelativeString( ctx ) )
      val conn = SequentConnector.guessInjection( fromLower = referencedProof.conclusion, toUpper = declSeq )
      val defn = ProofDefinition( lhs, conn, referencedProof )
      ctx.state.update[ProofDefinitions]( _ + defn )
    }
  }

  case class ProofDeclaration( lhs: Expr, proof: LKProof ) extends Update {
    override def apply( ctx: Context ): State =
      ctx + ProofNameDeclaration( lhs, proof.endSequent ) + ProofDefinitionDeclaration( lhs, proof ) state

    override def toString: String =
      s"ProofDeclaration($lhs, ${proof.endSequent})"
  }

  def guess( exprs: Traversable[Expr] ): ImmutableContext = {
    val names = exprs.view.flatMap( containedNames( _ ) ).toSet
    val tys = names.flatMap( c => baseTypes( c.ty ) )
    var ctx = default
    for ( ty @ TBase( n, ps ) <- tys if !ctx.isType( ty ) )
      ctx += Sort( TBase( n, ps.indices.map( i => TVar( s"a$i" ) ).toList ) )
    val consts = names.collect { case c: Const => c }
    for ( ( n, cs ) <- consts.groupBy( _.name ) if ctx.constant( n ).isEmpty )
      ctx += ConstDecl( if ( cs.size == 1 ) cs.head else Const( n, TVar( "a" ), List( TVar( "a" ) ) ) )
    ctx
  }
}

class MutableContext( private var ctx_ :ImmutableContext ) extends Context {
  override def state: State = ctx.state
  override def updates: List[Update] = ctx.updates
  override def toImmutable: ImmutableContext = ctx

  override def toString: String = ctx.toString

  def ctx: ImmutableContext = ctx_
  def ctx_=( newCtx: ImmutableContext ): Unit = ctx_ = newCtx

  def +=( update: Update ): Unit = ctx += update
  def ++=( updates: Iterable[Update] ): Unit = ctx ++= updates

  def addDefinition( by: Expr, name: => String = newNameGenerator.freshWithIndex( "D" ), reuse: Boolean = true ): Const = {
    if ( reuse ) {
      for ( ( d, _ ) <- get[Definitions].definitions.find( _._2 == by ) ) {
        return Const( d, by.ty )
      }
    }
    val what = Const( name, by.ty, typeVariables( by ).toList )
    this += Definition( what, by )
    what
  }

  def addSkolemSym( defn: Expr, name: => String = newNameGenerator.freshWithIndex( "s" ), reuse: Boolean = true ): Const = {
    if ( reuse ) {
      for ( ( d, _ ) <- get[SkolemFunctions].skolemDefs.find( _._2 == defn ) ) {
        return d
      }
    }
    val Abs.Block( vs, Quant( v, _, _ ) ) = defn
    val sym = Const( name, FunctionType( v.ty, vs.map( _.ty ) ) )
    this += SkolemFun( sym, defn )
    sym
  }
}
object MutableContext {
  def default(): MutableContext = Context.default.newMutable
  def guess( exprs: Traversable[Expr] ): MutableContext = Context.guess( exprs ).newMutable
  def guess( exprs: Expr* ): MutableContext = guess( exprs )
  def guess( seq: Sequent[Expr] ): MutableContext = guess( seq.elements )
  def guess( cnf: Traversable[Sequent[Expr]] )( implicit dummyImplicit: DummyImplicit ): MutableContext = guess( cnf.view.flatMap( _.elements ) )
  def guess[R, S]( rs: Traversable[R] )( implicit ev: Replaceable[R, S] ): MutableContext =
    guess( rs.view.flatMap( ev.names ) )
  def guess( p: LKProof ): MutableContext =
    guess( containedNames( p ) ) // TODO: add (Skolem) definitions

  def guess( p: ResolutionProof ): MutableContext = {
    val ctx = default()

    val cs = containedNames( p )

    val tys = cs.flatMap( c => baseTypes( c.ty ) )
    for ( ty <- tys if !ctx.isType( ty ) )
      ctx += Sort( ty )

    val defs: Map[Const, Expr] = p.definitions.toMap
    def add( c: Const ): Unit =
      if ( ctx.constant( c.name ).isEmpty ) defs.get( c ) match {
        case Some( d ) =>
          constants( d ).foreach( add )
          ctx += Definition( c, d )
        case None =>
          ctx += c
      }
    cs.foreach { case c: Const => add( c ) case _ => }

    ctx
  }
}

class ReadonlyMutableContext( ctx: ImmutableContext ) extends MutableContext( ctx ) {
  override def ctx_=( newCtx: ImmutableContext ): Unit = throw new UnsupportedOperationException
}

