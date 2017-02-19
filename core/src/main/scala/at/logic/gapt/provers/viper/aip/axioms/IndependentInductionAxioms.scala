package at.logic.gapt.provers.viper.aip.axioms

import at.logic.gapt.expr.{ All, And, Const => Con, FunctionType, HOLFormula, Substitution, Var, freeVariables, rename }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.provers.viper.aip._

import cats.syntax.all._, cats.instances.all._

/**
 * Generates independent induction axioms.
 *
 * @param vsel The variables for which induction axioms are generated.
 * @param fsel The formula of a sequent for which axioms are generated.
 */
case class IndependentInductionAxioms(
    vsel: VariableSelector = allVariablesSelector( _ )( _ ),
    fsel: FormulaSelector  = firstFormulaSelector( _ )
) extends AxiomFactory {

  def forAllVariables = copy( vsel = allVariablesSelector( _ )( _ ) )

  def forVariables( variables: List[Var] ) = copy( vsel = ( _, _ ) => variables )

  def forVariables( variables: Var* ) = copy( vsel = ( _, _) => variables.toList )

  def forLabel( label: String ) = copy( fsel = findFormula( _, label ) )

  /**
   * Generates independent induction axioms for the given sequent.
   *
   * @param sequent The sequent for which the induction axioms are generated.
   * @return Either a list of induction axioms, or a list of error-messages if the axioms could not be created
   */
  override def apply( sequent: Sequent[( String, HOLFormula )] )( implicit ctx: Context ): ThrowsError[List[Axiom]] = {
    for {
      formula <- fsel( sequent )
      inductionVariables = vsel( formula, ctx )
      freeVars = freeVariables( formula ).toList
      All.Block( _, formula1 ) = formula
      variablesToBeClosed = freeVariables( formula1 ).toList.diff( inductionVariables ).diff( freeVars )
      formula2 = All.Block( variablesToBeClosed, formula1 )
      axioms <- makeInductionAxioms( formula2, inductionVariables )
    } yield axioms
  }

  /**
   * Computes the list of induction axioms for a given formula and variables.
   *
   * @param formula   The formula for which the induction axioms are generated.
   * @param variables The variables for which an induction axiom is generated.
   * @return A list of either induction axioms or errors. A an error message is
   *         in the list if the corresponding axiom could not be created.
   */
  private def makeInductionAxioms(
    formula: HOLFormula, variables: List[Var]
  )( implicit ctx: Context ): ThrowsError[List[Axiom]] =
    variables.traverse[ThrowsError, Axiom]( v => makeAxiom( formula, v, variables ) )

  /**
   * Computes an induction axiom for the given formula and the given variable.
   *
   * @param formula  The formula subject to the induction axiom.
   * @param variable The induction variable.
   * @return Either a formula of the form:
   *         ∀x,,1,,,...,x,,k-1,,,x,,k+1,,,...,x,,n,,( <IC(F,c,,1,,,x,,k,,)> ∧...∧ <IC(F,c,,m,,,x,,k,,)> -> ∀x,,k,, F ),
   *         given a formula F, a variable x,,k,, such that
   *         - F has free variables x,,1,,,...,x,,n,,
   *         - x,,k,, is inductive and has constructors c,,1,,,...,c,,m,,
   *         - IC(F,c,,i,,,x,,k,,), with i = {1,...,m} symbolises the i-th inductive case;
   *         or an error message if one of the above conditions is violated.
   */
  private def makeAxiom(
    formula: HOLFormula, variable: Var, variables: List[Var]
  )( implicit ctx: Context ): ThrowsError[Axiom] =
    for {
      constructors <- getConstructors( baseType( variable ), ctx )
    } yield {
      val ics = constructors map { c => inductiveCase( formula, c, variable ) }
      val concl = All( variable, formula )
      val fvs = freeVariables( formula ).toList
      new Axiom {
        val formula = All.Block( variables filter { _ != variable }, And( ics ) --> concl )
        val proof = proveAxiom( formula, variable )
      }
    }

  /**
   * Computes a proof for an independent induction axiom.
   *
   * @param axiom    The induction axiom to be proved.
   * @param variable The variable for which the axiom describes an induction.
   * @param ctx      The context which specifies constants, types, etc.
   * @return A proof of the given induction axiom.
   */
  private def proveAxiom( axiom: HOLFormula, variable: Var )( implicit ctx: Context ): LKProof =
    ( ProofState( Sequent() :+ ( "" -> axiom ) ) + axiomProof( variable ) ).result

  /**
   * Tactical for independent induction axioms.
   *
   * @param variable The variable associated with the induction axiom.
   * @param ctx      The context defining constants, types, etc.
   * @return A tactical which can be used to create a proof of the induction axiom associated with the
   *         variable.
   */
  private def axiomProof( variable: Var )( implicit ctx: Context ): Tactical[Unit] =
    for {
      _ <- repeat( allR )
      _ <- impR
      _ <- allR( variable )
      _ <- induction( variable )
      _ <- decompose.onAllSubGoals
      _ <- repeat( escargot )
    } yield ()

  /**
   * Returns a formula expressing the inductive case for a given constructor, formula
   * and variable.
   *
   * @param formula     The formula to be used for the inductive case.
   * @param constructor The constructor corresponding to the returned inductive case.
   * @param variable    The induction variable.
   * @return Returns a formula of the form:
   *         ∀y,,1,,',...,∀y,,n,,'((F[y,,1,,'/x] ∧ ... ∧ F[y,,n,,'/x])
   *         -> ∀z,,1,,',...,∀z,,l,,' F[c(y,,1,,',...y,,n,,',z,,1,,',...,z,,l,,')/x]),
   *         for a given variable x, a constructor c and a formula F such that
   *         - x is of inductive type with constructor c
   *         - x is a free variable of F
   *         - c has free variables y,,1,,,...,y,,n,,,z,,1,,,...,z,,l,,
   *         - the variables y,,1,,,...,y,,n,, are of the same type as x
   *         - variables z,,1,,,...,z,,l,, are not of the same type as x
   *         - variables y,,1,,',...,y,,n,,',z,,1,,',...,z,,l,,' are fresh variables for F.
   */
  private def inductiveCase(
    formula:     HOLFormula,
    constructor: Con,
    variable:    Var
  )( implicit ctx: Context ): HOLFormula = {
    val FunctionType( _, argumentTypes ) = constructor.exptype
    val nameGenerator = rename.awayFrom( freeVariables( formula ) )
    val evs = argumentTypes map {
      at => nameGenerator.fresh( if ( at == variable.exptype ) variable else Var( "x", at ) )
    }
    val ivs = evs filter {
      _.exptype == variable.exptype
    }
    val ovs = evs filter {
      _.exptype != variable.exptype
    }
    val hyps = ivs map { iv => Substitution( variable -> iv )( formula ) }
    val concl = Substitution( variable -> constructor( evs: _* ) )( formula )

    All.Block(
      ivs, And( hyps ) --> All.Block( ovs, concl )
    )
  }
}
