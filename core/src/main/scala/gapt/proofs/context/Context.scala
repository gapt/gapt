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
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.mutable.ReadonlyMutableContext
import gapt.proofs.context.update.{ ConstantDeclaration => ConstDecl }
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

  /**
   * Retrieves the context's current state.
   *
   * @return The context's current state.
   */
  def state: State

  /**
   * Retrieves the updates that have been applied to this context.
   *
   * @return A list of updates with newer updates occurring before older ones.
   */
  def updates: List[Update]

  /**
   * Converts this context into an immutable context.
   *
   * @return A new immutable context that equals this context at the time of
   * calling this method.
   */
  def toImmutable: ImmutableContext

  /**
   * Converts this context into a mutable context.
   *
   * @return A new mutable context that equals this context at the time of
   * calling this method.
   */
  def newMutable: MutableContext = new MutableContext( toImmutable )

  /**
   * Converts this context to a read-only context.
   *
   * @return A new read-only context that is equal to this context at the time
   * of invoking this method.
   */
  def toReadonly: ReadonlyMutableContext = new ReadonlyMutableContext( toImmutable )

  /**
   * Retrieves a facet of this context.
   *
   * @tparam T The facet's type.
   * @return Returns the facet associated with the given type. If this facet
   * is not present yet, it is initialized and its initial value is returned.
   */
  def get[T: Facet]: T = state.get[T]

  /**
   * Retrieves all the constants defined in this context.
   *
   * @return A list of all the constants that are currently defined in this
   * context.
   */
  def constants: Iterable[Const] = get[Constants].constants.values

  /**
   * Retrieves all the definitions of this context.
   *
   * @return The current definitions saved by this context i.e. a map
   * associating constants with expressions.
   */
  def definitions: Map[Const, Expr] =
    for {
      ( what, by ) <- get[Definitions].definitions
      whatC <- constant( what )
    } yield whatC -> by

  /**
   * Retrieves constants by name.
   *
   * @param name The name for which a constant is to be looked up.
   * @return Returns `Some( c )` where `c.name` equals `name` if the context
   * currently contains such a constant `c`, otherwise `None` is retured.
   */
  def constant( name: String ): Option[Const] = get[Constants].constants.get( name )

  /**
   * Retrieves constants by name and type parameters.
   *
   * @param name The name for which a constant is to be looked up.
   * @param params The type parameters for which a constant is to be looked up.
   * @return Returns `Some ( c )` if the context currently contains a constant
   * `c` with name `name` and type parameters `params`. Otherwise `None` is
   * returned.
   */
  def constant( name: String, params: List[Ty] ): Option[Const] =
    get[Constants].lookup( name, params )

  /**
   * Retrieves inductive type constructors for a given type.
   *
   * @param ty The type whose inductive type constructors are to be looked up.
   * @return Returns `Some( ctrs )` if `ty` is an inductive type having
   * constructors `ctrs`, otherwise `None` is returned.
   */
  def getConstructors( ty: Ty ): Option[Vector[Const]] =
    ty match {
      case ty @ TBase( _, _ ) => getConstructors( ty )
      case _                  => None
    }

  /**
   * Looks up inductive type constructors for a given base type.
   *
   * @param ty The base type whose type constructors are to be looked up.
   * @return Returns `Some( ctrs )` if `ty` is an inductive type having
   * constructors `ctrs`, otherwise `None` is returned.
   */
  def getConstructors( ty: TBase ): Option[Vector[Const]] =
    for {
      declT <- get[BaseTypes].baseTypes.get( ty.name )
      ctrs <- get[StructurallyInductiveTypes].constructors.get( ty.name )
      subst <- syntacticMatching( declT, ty )
    } yield ctrs.map( subst( _ ).asInstanceOf[Const] )

  /**
   * Checks whether the given base type is defined in this context.
   *
   * @param ty The base type that is to be checked.
   * @return `true` if `ty` is defined in this context, `false` otherwise.
   */
  def isType( ty: TBase ): Boolean = (
    for {
      declT <- get[BaseTypes].baseTypes.get( ty.name )
      _ <- syntacticMatching( declT, ty )
    } yield () ).isDefined

  /**
   * Looks up the definition of a constant.
   *
   * @param c The constant with type arguments `args` whose definition is to
   * be looked up.
   * @return If the constant `c` has a definition, then `Some( definition )`
   * is returned where `definition` is obtained from the definition of `c` by
   * instantiating the type variables according to args.
   */
  def definition( c: Const ): Option[Expr] =
    for {
      defC <- get[Constants].constants.get( c.name )
      subst <- syntacticMatching( defC, c )
      defn <- get[Definitions].definitions.get( c.name )
    } yield subst( defn )

  /**
   * Retrieves all expression-level reduction rules.
   *
   * @return Returns all the expression-level reduction rules currently stored
   * in this context.
   */
  def reductionRules: Iterable[ReductionRule] = state.getAll[ReductionRule]

  /**
   * Checks whether the context contains a given definition.
   *
   * @param defn The definition that is to be checked.
   * @return Returns `true` if the given definition is an instance of a
   * definition stored in this context.
   */
  def contains( defn: Definition ): Boolean =
    definition( defn.what ).contains( defn.by )

  /**
   * Retrieves the skolem definition of a constant.
   *
   * @param skSym The constant whose definition is to be looked up.
   * @return Returns `Some(definition)` if the constant `skSym` is a skolem
   * function with definition `definition`.
   */
  def skolemDef( skSym: Const ): Option[Expr] =
    get[SkolemFunctions].skolemDefs.get( skSym )

  /**
   * Applies an update to this context.
   *
   * @param update The update to be applied to this context.
   * @return An immutable context obtained by converting this context to an
   * immutable context and by applying the update to that context.
   */
  def +( update: Update ): ImmutableContext =
    toImmutable + update

  /**
   * The context's normalizer.
   *
   * @return The context's normalizer.
   */
  def normalizer = get[Reductions].normalizer

  /**
   * Normalizes an expression.
   *
   * @param expression The expression to be normalized.
   * @return An expression obtained by normalizing `expression` according to
   * the reduction rules currently stored in this context.
   */
  def normalize( expression: Expr ): Expr =
    normalizer.normalize( expression )

  /**
   * Reduces an expression to WHNF.
   *
   * @param expression The expression to be reduced to WHNF.
   * @return An expression reduced to WHNF according to the reduction rules
   * currently stored in this context.
   */
  def whnf( expression: Expr ): Expr =
    normalizer.whnf( expression )

  /**
   * Checks if two expressions normalize to the same expression.
   *
   * @param a An expression to be checked.
   * @param b An expression to be checked.
   * @return Returns `true` if and only if `a` and `b` normalize to the same
   * expression in this context.
   */
  def isDefEq( a: Expr, b: Expr ): Boolean =
    normalizer.isDefEq( a, b )

  /**
   * Checks an object with respect to this context.
   *
   * This method checks whether a given object is correctly constructed
   * according to this context. For example for a type to check against a
   * context the base types occurring in that type must all be declared in the
   * context.
   *
   * @param t The object to be checked.
   * @tparam T The type of object to be checked.
   */
  def check[T: Checkable]( t: T ): Unit =
    implicitly[Checkable[T]].check( t )( this )

  /**
   * Applies several updates to the context.
   *
   * @param updates The updates to be applied to the context.
   * @return An immutable context obtained by applying iteratively applying
   * the updates from left to right.
   */
  def ++( updates: Traversable[Update] ): ImmutableContext =
    updates.foldLeft( toImmutable )( _ + _ )

  /**
   * Retrieves all the names declared in this context.
   *
   * @return All the names currently declared in this context.
   */
  def names: Iterable[String] = constants.map( _.name ) ++ get[BaseTypes].baseTypes.keySet

  /**
   * Creates a new name generator for this context.
   *
   * @return A new name generator that avoids all the names currently defined
   * in the context.
   */
  def newNameGenerator: NameGenerator = new NameGenerator( names )

  def signatureLookup( s: String ): BabelSignature.VarConst =
    constant( s ) match {
      case Some( c ) => BabelSignature.IsConst( c )
      case None      => BabelSignature.IsVar
    }

  def notationsForToken( token: Notation.Token ): Option[Notation] = get[Notations].byToken.get( token )
  def notationsForConst( const: Notation.ConstName ): List[Notation] = get[Notations].byConst( const )
  def defaultTypeToI: Boolean = false

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
