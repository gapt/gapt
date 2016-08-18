package at.logic.gapt.proofs

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ CNFp, isPrenex, containsWeakQuantifier }
import at.logic.gapt.formats.babel
import at.logic.gapt.formats.babel.BabelSignature
import Context._
import at.logic.gapt.proofs.lk.{ LKProof, TheoryAxiom }
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.provers.escargot.Escargot

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
 * TODO: implement validation
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
trait Context extends BabelSignature {
  /** Returns Some(const) if name is a constant. */
  def constant( name: String ): Option[Const]
  /** Returns Some(typeDef) if name is a base type. */
  def typeDef( name: String ): Option[TypeDef]
  /** Returns Some(expandedDefinition) if name is a defined constant. */
  def definition( name: String ): Option[LambdaExpression]
  /**
   * Returns Some(lkProof) if clause is valid modulo the background theory.
   *
   * lkProof should end in a minimal sub-sequent of clause that is still valid.
   */
  def theory( clause: HOLClause ): Option[LKProof]

  def typeDef( ty: TBase ): Option[TypeDef] = typeDef( ty.name )

  override def apply( s: String ): babel.VarConst =
    constant( s ) match {
      case Some( c ) => babel.IsConst( babel.ast.liftType( c.exptype ) )
      case None      => babel.IsVar( babel.ast.freshTypeVar() )
    }
}

/**
 * Represents the background theory of a proof.
 */
trait BackgroundTheory {
  def solve( atomicSeq: HOLClause ): Option[LKProof]
}

/** Background theory that only validates clauses that are subsumed by axioms. */
case class SubsumptionTheory( axioms: HOLFormula* ) extends BackgroundTheory {
  private val cnf = CNFp( And( axioms ) )

  def solve( atomicSeq: HOLClause ): Option[LKProof] =
    ( for {
      clause <- cnf
      sub <- clauseSubsumption( clause, atomicSeq )
    } yield TheoryAxiom( sub( clause ).map( _.asInstanceOf[HOLAtom] ) ) ).headOption
}

/**
 * Background theory that validates clauses which are first-order consequences of the axioms.
 *
 * The consequence is checked using a first-order prover.
 */
case class FOTheory( solver: ResolutionProver, axioms: HOLFormula* ) extends BackgroundTheory {
  require( freeVariables( axioms ).isEmpty )

  def solve( atomicSeq: HOLClause ): Option[LKProof] =
    solver getLKProof ( axioms ++: atomicSeq, addWeakenings = false ) map { p =>
      TheoryAxiom( p.conclusion intersect atomicSeq map { _.asInstanceOf[HOLAtom] } )
    }
}

object FOTheory {
  def apply( axioms: HOLFormula* ): FOTheory = FOTheory( Escargot, axioms: _* )
}

/** A finite [[Context]]. */
case class FiniteContext(
    constants:        Set[Const]                   = Set(),
    definitions:      Map[Const, LambdaExpression] = Map(),
    typeDefs:         Set[Context.TypeDef]         = Set( Context.oTypeDef ),
    backgroundTheory: BackgroundTheory             = FOTheory()
) extends Context {
  val constantsMap = constants.map { c => c.name -> c }.toMap
  val typeDefsMap = typeDefs.map { td => td.ty.name -> td }.toMap
  val definitionMap = definitions map { case ( w, b ) => w.name -> b }
  for ( ( c, d ) <- definitions ) require( c.exptype == d.exptype )

  def constant( name: String ) = constantsMap get name
  def definition( name: String ) = definitionMap get name
  def typeDef( name: String ) = typeDefsMap get name

  def theory( atomicSeq: HOLClause ): Option[LKProof] = backgroundTheory.solve( atomicSeq )

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
    case Eq( Apps( VarOrConst( definedConstName, _ ), arguments ), definition ) =>
      this + ( definedConstName -> Abs( arguments map { _.asInstanceOf[Var] }, definition ) )
  }

  def +( newTheory: BackgroundTheory ): FiniteContext =
    copy( backgroundTheory = newTheory )
}

object Context {
  /** Definition of a base type.  Either [[Sort]] or [[InductiveType]]. */
  sealed trait TypeDef { def ty: TBase }
  /** Uninterpreted base type. */
  case class Sort( ty: TBase ) extends TypeDef
  /** Inductive base type with constructors. */
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
