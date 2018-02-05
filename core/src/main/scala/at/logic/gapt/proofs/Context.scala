package at.logic.gapt.proofs

import at.logic.gapt.expr._
import at.logic.gapt.formats.babel._
import Context._
import at.logic.gapt.expr.fol.folSubTerms
import at.logic.gapt.expr.hol.SkolemFunctions
import at.logic.gapt.proofs.lk.{ LKProof, ProofLink }
import at.logic.gapt.proofs.resolution.ResolutionProof
import at.logic.gapt.utils.NameGenerator

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
 *  - [[at.logic.gapt.proofs.expansion.ExpansionProofToLK]] uses the information about the background theory
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

  /** Returns the Skolem definition of skSym.  See [[at.logic.gapt.expr.hol.SkolemFunctions]]. */
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
  def notationsForToken( token: String ): Option[Notation] = get[Notations].byToken.get( token )
  def notationsForConst( const: String ): List[Notation] = get[Notations].byConst( const )
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
    Notation.Alias( "true", TopC.name ), Notation.Alias( "⊤", TopC.name ),
    Notation.Alias( "false", BottomC.name ), Notation.Alias( "⊥", BottomC.name ),
    ConstDecl( NegC() ),
    Notation.Prefix( "-", NegC.name, Precedence.neg ),
    Notation.Prefix( "~", NegC.name, Precedence.neg ),
    Notation.Prefix( "¬", NegC.name, Precedence.neg ),
    ConstDecl( AndC() ),
    Notation.Infix( "&", AndC.name, Precedence.conj ),
    Notation.Infix( "∧", AndC.name, Precedence.conj ),
    ConstDecl( OrC() ),
    Notation.Infix( "|", OrC.name, Precedence.disj ),
    Notation.Infix( "∨", OrC.name, Precedence.disj ),
    ConstDecl( ImpC() ),
    Notation.Infix( "->", ImpC.name, Precedence.impl, leftAssociative = false ),
    Notation.Infix( "⊃", ImpC.name, Precedence.impl, leftAssociative = false ),
    Notation.Infix( "→", ImpC.name, Precedence.impl, leftAssociative = false ),
    Notation.Infix( "<->", Notation.fakeIffConst, Precedence.iff ),
    Notation.Infix( "↔", Notation.fakeIffConst, Precedence.iff ),
    ConstDecl( ForallC( TVar( "x" ) ) ),
    Notation.Quantifier( "!", ForallC.name, Precedence.quant ),
    Notation.Quantifier( "∀", ForallC.name, Precedence.quant ),
    ConstDecl( ExistsC( TVar( "x" ) ) ),
    Notation.Quantifier( "?", ExistsC.name, Precedence.quant ),
    Notation.Quantifier( "∃", ExistsC.name, Precedence.quant ),
    ConstDecl( EqC( TVar( "x" ) ) ),
    Notation.Infix( "=", EqC.name, Precedence.infixRel ),
    Notation.Infix( "!=", Notation.fakeNeqConst, Precedence.infixRel ) )

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
      names.map { case ( _, ( lhs, sequent ) ) => s"$lhs: $sequent" }.mkString( "\n" )
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

  case class PrimRecFunBatch( prfDefinitions: Seq[( Const, Int, Int, Vector[( Expr, Expr )] )] ) extends Update {

    for ( ( const, nArgs, recIdx, eqs ) <- prfDefinitions ) {
      validatePrimRecFunDef( const, nArgs, recIdx, eqs )
    }

    val recTypes: Map[Const, TBase] = (
      for ( ( constant, _, recIdx, _ ) <- prfDefinitions ) yield {
        val Const( _, FunctionType( _, argTypes ), _ ) = constant
        ( constant, argTypes( recIdx ).asInstanceOf[TBase] )
      } ).toMap

    def apply( ctx: Context ): State = {
      val constants = prfDefinitions map { _._1 }
      val ctx_ = ctx ++ constants.map { ConstDecl }
      for ( ( constant, _, recIdx, equations ) <- prfDefinitions ) {
        validateEquations( ctx, ctx_, recIdx, constant, equations )
      }
      val reductions = prfDefinitions.flatMap { _._4 }.map { ReductionRule.apply }.toVector
      ctx.state.update[Constants]( _ ++ constants ).update[Reductions]( _ ++ reductions )
    }

    private def validateEquations(
      ctx: Context, ctx_ : Context, recIdx: Int, constant: Const, equations: Vector[( Expr, Expr )] ) {
      val ctrs = ctx.get[StructurallyInductiveTypes].constructors( recTypes( constant ).name )
      require( equations.size == ctrs.size )
      for ( ( ( lhs @ Apps( _, lhsArgs ), rhs ), ctr ) <- equations.zip( ctrs ) ) {
        ctx_.check( lhs )
        ctx_.check( rhs )
        val Apps( Const( ctr_, _, _ ), _ ) = lhsArgs( recIdx )
        require( ctr_ == ctr.name )
      }
    }

    private def validatePrimRecFunDef( c: Const, nArgs: Int, recIdx: Int, equations: Vector[( Expr, Expr )] ): Unit = {
      val Const( name, FunctionType( _, argTypes ), _ ) = c
      val typeVars: Set[TVar] = typeVariables( c.ty )
      require( 0 <= recIdx && recIdx < nArgs && nArgs <= argTypes.size )

      for ( ( lhs, rhs ) <- equations ) {
        require( lhs.ty == rhs.ty )
        require( typeVariables( lhs.ty ) subsetOf typeVars )
        require( typeVariables( rhs.ty ) subsetOf typeVars )

        val Apps( `c`, lhsArgs ) = lhs
        require( lhsArgs.size == nArgs )

        val nonRecLhsArgs = lhsArgs.zipWithIndex.filter( _._2 != recIdx ).map( _._1 )
        val Apps( _: Const, ctrArgs ) = lhsArgs( recIdx )

        val matchVars = nonRecLhsArgs ++ ctrArgs
        matchVars.foreach( a => require( a.isInstanceOf[Var] ) )
        require( matchVars == matchVars.distinct )
        folSubTerms( rhs ).foreach {
          case Apps( fn @ Const( `name`, _, _ ), args ) =>
            require( fn == c )
            require( ctrArgs.contains( args( recIdx ) ) )
          case _ =>
        }
      }
    }
  }

  object PrimRecFun {

    private def parseEqn( c: Const, eqn: String )( implicit ctx: Context ): ( Expr, Expr ) = {
      BabelParser.tryParse( eqn, p => preExpr.TypeAnnotation( p, preExpr.Bool ) ).
        fold( throw _, identity ) match {
          case Eq( lhs @ Apps( c_, _ ), rhs ) =>
            syntacticMatching( c_, c ).get( lhs -> rhs )
        }
    }

    def apply( c: Const, equations: String* )( implicit ctx: Context ): PrimRecFunBatch = {
      apply( ( c, equations ) )
    }

    def toPrimRecFunDefinition( constant: Const, equations: String* )( implicit ctx: Context ): ( Const, Int, Int, Vector[( Expr, Expr )] ) =
      toPrimRecFunDefinition( constant, equations map { parseEqn( constant, _ )( ctx ) } )

    def toPrimRecFunDefinition( constant: Const, equations: Traversable[( Expr, Expr )] )( implicit ctx: Context ): ( Const, Int, Int, Vector[( Expr, Expr )] ) = {
      val ( nArgs, recIdx ) = equations.head._1 match {
        case Apps( _, args ) => args.size -> args.indexWhere( !_.isInstanceOf[Var] )
      }
      val Const( _, FunctionType( _, argTys ), _ ) = constant
      val equationsByConst = equations.groupBy {
        case ( ( Apps( _, args ), _ ) ) =>
          val Apps( ctr, _ ) = args( recIdx )
          ctr
      }
      val Some( recCtrs ) = ctx.getConstructors( argTys( recIdx ) )
      ( constant, nArgs, recIdx, recCtrs.map( equationsByConst( _ ).head ) )
    }

    def apply( prfDefinitions: Iterable[( Const, Iterable[( Expr, Expr )] )] )( implicit ctx: Context ): PrimRecFunBatch =
      PrimRecFunBatch( prfDefinitions.view.map { case ( c, eqns ) => toPrimRecFunDefinition( c, eqns ) }.toVector )

    def apply( prfDefinitions: ( Const, Seq[String] )* )( implicit ctx: Context ): PrimRecFunBatch = {
      val constants = prfDefinitions map { _._1 }
      val ctx_ = ctx ++ constants.map { ConstDecl( _ ) }
      val batch =
        for ( ( constant, equations ) <- prfDefinitions ) yield {
          toPrimRecFunDefinition( constant, equations: _* )( ctx_ )
        }
      PrimRecFunBatch( batch )
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
    for ( ty <- tys if !ctx.isType( ty ) )
      ctx += Sort( ty )
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

