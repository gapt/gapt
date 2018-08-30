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
import gapt.proofs.context.facet.Constants
import gapt.proofs.context.facet.Definitions
import gapt.proofs.context.facet.Reductions
import gapt.proofs.context.facet.StructurallyInductiveTypes
import gapt.proofs.context.facet.BaseTypes
import gapt.proofs.context.facet.Facet
import gapt.proofs.context.update.ConstDecl
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.Sort
import gapt.proofs.context.update.Update
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.ProofLink
import gapt.utils.NameGenerator

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
