package at.logic.gapt.provers.viper.aip.axioms

import at.logic.gapt.expr.{ All, And, FunctionType, HOLFormula, Substitution, Var, freeVariables, rename, Const => Con }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.provers.viper.aip.{ ThrowsError, baseType, findFormula, getConstructors }
import cats.instances.all._
import cats.syntax.all._

/**
 * Generates sequential induction axioms.
 *
 * @param vsel The variables for which an induction axiom is generated.
 * @param fsel The formula of a sequent for which induction axioms are generated.
 */
case class SequentialInductionAxioms(
    vsel: VariableSelector = allVariablesSelector( _ )( _ ),
    fsel: FormulaSelector  = firstFormulaSelector( _ )
) extends AxiomFactory {

  def forAllVariables = copy( vsel = allVariablesSelector( _ )( _ ) )

  def forVariables( variables: List[Var] ) = copy( vsel = ( _, _ ) => variables )

  def forVariables( variables: Var* ) = copy( vsel = ( _, _ ) => variables.toList )

  def forLabel( label: String ) = copy( fsel = findFormula( _, label ) )

  def forFormula( formula: HOLFormula ) = copy( fsel = _ => Right( formula ) )

  /**
   * Computes sequential induction axioms for a sequent.
   *
   * @param sequent The sequent for which the axioms are generated.
   * @param ctx     The context defining types, constants, etc.
   * @return Failure if the one of the given variables is not of inductive type.
   *         Otherwise a list of induction axioms of the form:
   *         ∀A∀{X < x}( IC(x,c,,1,,) ∧ ... ∧ IC(x,c,,l,,) -> ∀x∀{X > x}∀{X'}F ),
   *         where
   *         the input variables are X
   *         the input formula is of the form F' = ∀{X U X'}F
   *         FV(F') = A
   *         x in X
   *         {X < x} and {X > x} are subsets of X containing all variables with index smaller/greater than the index of x.
   */
  override def apply( sequent: Sequent[( String, HOLFormula )] )( implicit ctx: Context ): ThrowsError[List[Axiom]] = {
    for {
      f <- fsel( sequent )
      vs = vsel( f, ctx )
      fvs = freeVariables( f ).toList
      All.Block( _, f1 ) = f
      xvs = freeVariables( f1 ).toList.diff( fvs ).diff( vs )
      f2 = All.Block( xvs, f1 )
      axioms <- vs.traverse[ThrowsError, Axiom] {
        v => inductionAxiom( f2, vs, v )
      }
    } yield axioms
  }

  /**
   * Computes an induction axiom for the given formula and variable.
   *
   * @param f   The formula for which the induction axiom is generated.
   * @param vs  The list of variables equal to {X < v} ++ [v] ++ {X > v}.
   * @param v   The variable for which the induction axiom is generated.
   * @param ctx The context defining types, constants, etc.
   * @return An induction axiom if v is of inductive type, an error message otherwise.
   */
  private def inductionAxiom( f: HOLFormula, vs: List[Var], v: Var )( implicit ctx: Context ): ThrowsError[Axiom] = {
    for {
      cs <- getConstructors( baseType( v ), ctx )
    } yield {
      val ( lvs, _ :: gvs ) = vs.span( _ != v )
      val inductiveCases = cs map { c => inductiveCase( f, vs, v, c ) }
      val conclusion = All( v, All.Block( gvs, f ) )
      new Axiom {
        private val inductionFormula = All.Block( gvs, f )
        val formula = All.Block( lvs, And( inductiveCases ) --> conclusion )

        /**
         * @return An inductive proof of the axiom.
         */
        def proof = {
          val inductiveCaseProofs = cs map { inductiveCaseProof( _ ) }
          var proofState = ProofState(
            Sequent( Nil, formula :: Nil )
          )
          proofState += repeat( allR )
          proofState += impR
          proofState += allR( v )
          proofState += induction( v )
          proofState += repeat( andL ).onAllSubGoals
          inductiveCaseProofs foreach {
            proofState += insert( _ )
          }
          proofState.result
        }

        /**
         * Computes proof of the inductive case corresponding to a given constructor.
         * @param constructor The constructor whose associated inductive case is proved.
         * @return A proof of the inductive case associated with the constructor.
         */
        private def inductiveCaseProof( constructor: Con ): LKProof = {
          val inductiveCaseFormula = inductiveCase( f, vs, v, constructor )
          val ( primaryVariables, secondaryVariables, inductionCaseConclusion ) =
            insertConstructor( v, constructor, inductionFormula )
          val inductionHypotheses = primaryVariables map {
            primaryVariable => Substitution( v -> primaryVariable )( inductionFormula )
          }
          var proofState = ProofState(
            Sequent(
              "icf" -> inductiveCaseFormula ::
                inductionHypotheses.zipWithIndex.map( { case ( hyp, index ) => s"ih$index" -> hyp } ),
              "goal" -> inductionCaseConclusion :: Nil
            )
          )
          proofState += allL( "icf", primaryVariables: _* ) orElse skip
          proofState += impL
          if ( primaryVariables.isEmpty )
            proofState += trivial
          else
            primaryVariables foreach {
              _ => proofState += andR andThen trivial orElse trivial
            }
          proofState += allL( secondaryVariables: _* ) orElse skip
          proofState += trivial

          proofState.result
        }
      }
    }
  }

  /**
   * Generates the inductive case of the given formula, variable and constructor.
   *
   * @param f  The formula for which the inductive case is generated.
   * @param vs The list of variables equal to {X < v} ++ [v] ++ {X > v}.
   * @param v  The variable for which the inductive case is generated.
   * @param c  The constructor of this inductive case.
   * @return The formula representing the inductive case.
   */
  private def inductiveCase( f: HOLFormula, vs: List[Var], v: Var, c: Con ): HOLFormula = {
    val ( _, _ :: gvs ) = vs.span( _ != v )
    val FunctionType( _, ats ) = c.exptype
    val nameGenerator = rename.awayFrom( freeVariables( f ) )
    val evs = ats map {
      at => nameGenerator.fresh( if ( at == v.exptype ) v else Var( "x", at ) )
    }
    val yvs = evs filter {
      _.exptype == v.exptype
    }
    val zvs = evs filter {
      _.exptype != v.exptype
    }
    val hyps = yvs map {
      yv => All.Block( gvs, Substitution( v -> yv )( f ) )
    }
    val concl = All.Block( zvs ++ gvs, Substitution( v -> c( evs: _* ) )( f ) )

    All.Block(
      yvs,
      And( hyps ) --> concl
    )
  }

  /**
   * Substitutes the a free variable by a constructor.
   *
   * @param freeVariable The free variable which is to be replaced by the given constructor.
   * @param constructor The constructor to be inserted at all occurrences of the specified freeVariable.
   * @param formula The formula in which the substitution is to be carried out.
   * @return A three tuple whose first component contains a list of all newly introduced free variables that
   *         are of the same type as the type to which the constructor belongs, the second component contains
   *         a list of all newly introduced variables that are of a different type than the constructor's type,
   *         the third component contains the result of the substitution.
   */
  private def insertConstructor(
    freeVariable: Var, constructor: Con, formula: HOLFormula
  ): ( List[Var], List[Var], HOLFormula ) = {
    val FunctionType( _, argumentTypes ) = constructor.exptype
    val nameGenerator = rename.awayFrom( freeVariables( formula ) )
    val newVariables = argumentTypes map {
      argumentType =>
        nameGenerator.fresh(
          if ( argumentType == freeVariable.exptype )
            freeVariable
          else
            Var( "x", argumentType )
        )
    }
    val ( primaryVariables, secondaryVariables ) = newVariables partition {
      _.exptype == freeVariable.exptype
    }
    ( primaryVariables, secondaryVariables, Substitution( freeVariable -> constructor( newVariables: _* ) )( formula ) )
  }
}
