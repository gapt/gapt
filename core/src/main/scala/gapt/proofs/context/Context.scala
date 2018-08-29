package gapt.proofs.context

import gapt.expr._
import gapt.expr.hol.SkolemFunctions
import gapt.formats.babel.BabelParser
import gapt.formats.babel.BabelSignature
import gapt.formats.babel.Notation
import gapt.formats.babel.Notations
import gapt.formats.babel.Precedence
import gapt.proofs.Checkable
import gapt.proofs.HOLSequent
import gapt.proofs.SequentConnector
import gapt.proofs.context.Context.BaseTypes
import gapt.proofs.context.Context.Constants
import gapt.proofs.context.Context.Definitions
import gapt.proofs.context.Context.Facet
import gapt.proofs.context.Context.Reductions
import gapt.proofs.context.Context.StructurallyInductiveTypes
import gapt.proofs.context.update.ConstDecl
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.Sort
import gapt.proofs.context.update.Update
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.ProofLink
import gapt.utils.NameGenerator

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
trait Context extends BabelSignature {
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

  implicit val skolemFunsFacet: Facet[SkolemFunctions] = Facet[SkolemFunctions]( SkolemFunctions( None ) )

  object parseEquation {

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

  def guess( exprs: Traversable[Expr] ): ImmutableContext = {
    val names = exprs.view.flatMap( containedNames( _ ) ).toSet
    val tys = names.flatMap( c => baseTypes( c.ty ) )
    var ctx = default
    for ( ty <- tys if !ctx.isType( ty ) )
      ctx += Sort( ty )
    val consts = names.collect { case c: Const => c }
    for ( ( n, cs ) <- consts.groupBy( _.name ) if ctx.constant( n ).isEmpty )
      ctx += ConstDecl( if ( cs.size == 1 ) cs.head else Const( n, TVar( "a" ), List( TVar( "a" ) ) ) )
    ctx
  }
}
