/* Utility functions for gaptic proofs */

package at.logic.gapt.proofs.gaptic

import at.logic.gapt.expr.{ Const => Con }
import at.logic.gapt.proofs.{ Context, Sequent }

import scalaz._
import Scalaz._
import Validation.FlatMap._
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.universalClosure
import at.logic.gapt.proofs.expansion.ExpansionProofToLK
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.provers.escargot.Escargot

trait InductionStrategy {
  type ThrowsError[T] = ValidationNel[String, T]
  def inductionAxioms( f: HOLFormula, vs: List[Var] )( implicit ctx: Context ): ThrowsError[List[HOLFormula]]
}
object proveWithInductionAxioms {

  type ThrowsError[T] = ValidationNel[String, T]

  /**
   * Tries to prove a sequent with induction axioms for a formula.
   *
   * @param sequent The sequent to prove.
   * @param label The label designating the formula for which the induction axioms are generated
   * @param variables The variables for which an induction is to be carried out.
   * @param context The context defining types, constants, etc.
   * @param strategy The strategy used for the generation of the induction axioms.
   * @return An LK proof of the given sequent if a proof exists, otherwise if there is no proof this method
   *         may either not terminate or return None.
   * @throws Exception If a the label does not uniquely determine a formula in the sequent, or if one of the variables
   *                   is not of inductive type.
   */
  def apply(
    sequent:   Sequent[( String, HOLFormula )],
    label:     String,
    variables: List[Var],
    strategy:  InductionStrategy
  )( implicit context: Context ): Option[LKProof] = {
    prepareSequent( sequent, label, variables, strategy ) match {
      case Success( inductiveSequent ) => Escargot.getExpansionProof( inductiveSequent map { case ( _, f ) => f } ) map { ExpansionProofToLK( _ ).toOption.get }
      case Failure( es )               => throw new Exception( es.tail.foldLeft( es.head ) { _ ++ "\n" ++ _ } )
    }
  }

  /**
   * Adds induction axioms for a formula to a given sequent.
   *
   * @param sequent The sequent to which the induction axioms are added.
   * @param label The label which designates a formula in the sequent.
   * @param variables The variables for which induction axioms are generated.
   * @param strategy The strategy which is used to generate the induction axioms.
   * @param ctx The context which defines types, constants, etc.
   * @return A sequent with induction axioms for the specified formula and variables if label designates a formula
   *         in the given sequent and all of the given variables are of inductive type (w.r.t. the given context).
   *         Otherwise a string describing the error is returned.
   */
  def prepareSequent(
    sequent:   Sequent[( String, HOLFormula )],
    label:     String,
    variables: List[Var],
    strategy:  InductionStrategy
  )( implicit ctx: Context ): ThrowsError[Sequent[( String, HOLFormula )]] = {
    for {
      formula <- findFormula( sequent, label )
      axioms <- strategy.inductionAxioms( formula, variables )
    } yield {
      ( axioms zip variables ).foldLeft( sequent )( { labelInductionAxiom( label, _, _ ) } )
    }
  }

  /**
   * Adds a labelled induction axiom to the sequent.
   * @param label The label of the formula to which the induction axiom belongs.
   * @param sequent The sequent to which the labelled axiom is added.
   * @param axvar A pair containing the induction axiom and its associated variable.
   * @return The initial sequent with the labelled induction axiom in its left side.
   */
  private def labelInductionAxiom(
    label:   String,
    sequent: Sequent[( String, HOLFormula )],
    axvar:   ( HOLFormula, Var )
  ): Sequent[( String, HOLFormula )] = {
    axvar match {
      case ( axiom, variable ) => ( NewLabels( sequent, s"IA/$label/${variable.name}/" )( 0 ) -> axiom ) +: sequent
    }
  }
}

object independentInductionAxioms extends InductionStrategy {

  /**
   * Computes the induction axioms for the given formula and variables.
   *
   * @param formula The formula for which the induction axioms are generated.
   * @param variables The variables for which an induction axiom is generated.
   * @return Either a list of induction axioms, or an error message if one of
   * the axioms could not be created.
   */
  def inductionAxioms( formula: HOLFormula, variables: List[Var] )( implicit ctx: Context ): ThrowsError[List[HOLFormula]] =
    {
      val All.Block( _, formula1 ) = formula
      makeInductionAxioms( formula1, variables )
    }

  /**
   * Computes the list of induction axioms for a given formula and variables.
   *
   * @param formula The formula for which the induction axioms are generated.
   * @param variables The variables for which an induction axiom is generated.
   * @return A list of either induction axioms or errors. A an error message is
   * in the list if the corresponding axiom could not be created.
   */
  private def makeInductionAxioms( formula: HOLFormula, variables: List[Var] )( implicit ctx: Context ): ThrowsError[List[HOLFormula]] =
    variables.traverse( v => makeAxiom( formula, v ) )

  /**
   * Computes an induction axiom for the given formula and the given variable.
   *
   * @param formula The formula subject to the induction axiom.
   * @param variable The induction variable.
   * @return Either a formula of the form:
   * ∀x,,1,,,...,x,,k-1,,,x,,k+1,,,...,x,,n,,( <IC(F,c,,1,,,x,,k,,)> ∧...∧ <IC(F,c,,m,,,x,,k,,)> -> ∀x,,k,, F ),
   * given a formula F, a variable x,,k,, such that
   * - F has free variables x,,1,,,...,x,,n,,
   * - x,,k,, is inductive and has constructors c,,1,,,...,c,,m,,
   * - IC(F,c,,i,,,x,,k,,), with i = {1,...,m} symbolises the i-th inductive case;
   * or an error message if one of the above conditions is violated.
   */
  private def makeAxiom( formula: HOLFormula, variable: Var )( implicit ctx: Context ): ThrowsError[HOLFormula] =
    for {
      constructors <- getConstructors( baseType( variable ), ctx )
    } yield {
      val ics = constructors map { c => inductiveCase( formula, c, variable ) }
      val concl = All( variable, formula )
      val fvs = freeVariables( formula ).toList
      All.Block( fvs filter { _ != variable }, And( ics ) --> concl )
    }

  /**
   * Returns a formula expressing the inductive case for a given constructor, formula
   * and variable.
   *
   * @param formula The formula to be used for the inductive case.
   * @param constructor The constructor corresponding to the returned inductive case.
   * @param variable The induction variable.
   * @return Returns a formula of the form:
   *     ∀y,,1,,',...,∀y,,n,,'((F[y,,1,,'/x] ∧ ... ∧ F[y,,n,,'/x])
   *                      -> ∀z,,1,,',...,∀z,,l,,' F[c(y,,1,,',...y,,n,,',z,,1,,',...,z,,l,,')/x]),
   * for a given variable x, a constructor c and a formula F such that
   * - x is of inductive type with constructor c
   * - x is a free variable of F
   * - c has free variables y,,1,,,...,y,,n,,,z,,1,,,...,z,,l,,
   * - the variables y,,1,,,...,y,,n,, are of the same type as x
   * - variables z,,1,,,...,z,,l,, are not of the same type as x
   * - variables y,,1,,',...,y,,n,,',z,,1,,',...,z,,l,,' are fresh variables for F.
   */
  private def inductiveCase(
    formula:     HOLFormula,
    constructor: Con,
    variable:    Var
  )( implicit ctx: Context ): HOLFormula =
    {
      val FunctionType( _, argumentTypes ) = constructor.exptype
      val nameGenerator = rename.awayFrom( freeVariables( formula ) )
      val evs = argumentTypes map {
        at => nameGenerator.fresh( if ( at == variable.exptype ) variable else Var( "x", at ) )
      }
      val ivs = evs filter { _.exptype == variable.exptype }
      val ovs = evs filter { _.exptype != variable.exptype }
      val hyps = ivs map { iv => Substitution( variable -> iv )( formula ) }
      val concl = Substitution( variable -> constructor( evs: _* ) )( formula )

      All.Block(
        ivs, And( hyps ) --> All.Block( ovs, concl )
      )
    }
}

object sequentialInductionAxioms extends InductionStrategy {

  /**
   * Computes a sequence of induction axioms for the given formula and variables.
   *
   * @param f The formula for which the induction axioms are generated.
   * @param vs The variables on which the induction is carried out.
   * @param ctx The context defining types, constants, etc.
   * @return Failure if the one of the given variables is not of inductive type.
   * Otherwise a list of induction axioms of the form:
   * ∀A∀{X < x}( IC(x,c,,1,,) ∧ ... ∧ IC(x,c,,l,,) -> ∀x∀{X > x}∀{X'}F ),
   * where
   * the input variables are X
   * the input formula is of the form F' = ∀{X U X'}F
   * FV(F') = A
   * x in X
   * {X < x} and {X > x} are subsets of X containing all variables with index smaller/greater than the index of x.
   */
  def inductionAxioms( f: HOLFormula, vs: List[Var] )( implicit ctx: Context ): ThrowsError[List[HOLFormula]] = {
    val fvs = freeVariables( f ).toList
    val All.Block( _, f1 ) = f
    val xvs = freeVariables( f1 ).toList.diff( fvs ).diff( vs )
    val f2 = All.Block( xvs, f1 )
    vs.traverse {
      v => inductionAxiom( f2, vs, v )
    }
  }

  /**
   * Computes an induction axiom for the given formula and variable.
   *
   * @param f The formula for which the induction axiom is generated.
   * @param vs The list of variables equal to {X < v} ++ [v] ++ {X > v}.
   * @param v The variable for which the induction axiom is generated.
   * @param ctx The context defining types, constants, etc.
   * @return An induction axiom if v is of inductive type, an error message otherwise.
   */
  private def inductionAxiom( f: HOLFormula, vs: List[Var], v: Var )( implicit ctx: Context ): ThrowsError[HOLFormula] = {
    for {
      cs <- getConstructors( baseType( v ), ctx )
    } yield {
      val ( lvs, _ :: gvs ) = vs.span( _ != v )
      val inductiveCases = cs map { c => inductiveCase( f, vs, v, c ) }
      val conclusion = All( v, All.Block( gvs, f ) )
      universalClosure( All.Block( lvs, And( inductiveCases ) --> conclusion ) )
    }
  }

  /**
   * Generates the inductive case of the given formula, variable and constructor.
   *
   * @param f The formula for which the inductive case is generated.
   * @param vs The list of variables equal to {X < v} ++ [v] ++ {X > v}.
   * @param v The variable for which the inductive case is generated.
   * @param c The constructor of this inductive case.
   * @return The formula representing the inductive case.
   */
  private def inductiveCase( f: HOLFormula, vs: List[Var], v: Var, c: Con ): HOLFormula = {
    val ( _, _ :: gvs ) = vs.span( _ != v )
    val FunctionType( _, ats ) = c.exptype
    val nameGenerator = rename.awayFrom( freeVariables( f ) )
    val evs = ats map {
      at => nameGenerator.fresh( if ( at == v.exptype ) v else Var( "x", at ) )
    }
    val yvs = evs filter { _.exptype == v.exptype }
    val zvs = evs filter { _.exptype != v.exptype }
    val hyps = yvs map {
      yv => All.Block( gvs, Substitution( v -> yv )( f ) )
    }
    val concl = All.Block( zvs ++ gvs, Substitution( v -> c( evs: _* ) )( f ) )

    All.Block(
      yvs,
      And( hyps ) --> concl
    )
  }
}

object getConstructors {
  /**
   * Reads the constructors of type `typ` from the context.
   *
   * @param typ A base type.
   * @return Either a list containing the constructors of `typ` or a TacticalFailure.
   */
  def apply(
    typ: TBase, ctx: Context
  ): ValidationNel[String, List[Con]] =
    ctx.typeDef( typ.name ) match {
      case Some( Context.InductiveType( _, constructors ) ) => constructors.toList.success
      case Some( typeDef ) => s"Type $typ is not inductively defined: $typeDef".failureNel
      case None => s"Type $typ is not defined".failureNel
    }
}

object baseType {
  /**
   * Retrieves the base type of a variable.
   *
   * @param variable A variable.
   * @return The variable's base type.
   */
  def apply( variable: Var ): TBase = variable.exptype.asInstanceOf[TBase]
}

object findFormula {
  /**
   * Finds a formula by label in a labelled sequent.
   *
   * @param sequent The sequent in which to search for the given label.
   * @param label The formula's label.
   * @return The formula designated by the given label or an error message if the formula
   *         is not be uniquely determined by the label.
   */
  def apply( sequent: Sequent[( String, HOLFormula )], label: String ): ValidationNel[String, HOLFormula] = {
    sequent.succedent filter { case ( l, f ) => l == label } match {
      case lf :: Nil => lf._2.success
      case lf :: _   => "Formula could not be uniquely determined" failureNel
      case _         => s"Label $label not found" failureNel
    }
  }
}
