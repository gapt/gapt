/* Utility functions for gaptic proofs */

package at.logic.gapt.proofs.gaptic

import at.logic.gapt.expr.{ Const => Con }
import at.logic.gapt.proofs.{ Context, Sequent }

import scalaz._
import Scalaz._
import Validation.FlatMap._
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.proofs.expansion.ExpansionProofToLK
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.provers.escargot.Escargot

trait InductionStrategy {
  def inductionAxioms( f: HOLFormula, vs: Seq[Var] )( implicit ctx: Context ): ValidationNel[String, Seq[HOLFormula]]
}
object proveWithInductionAxioms {

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
  )( implicit ctx: Context ): ValidationNel[String, Sequent[( String, HOLFormula )]] = {
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
  def inductionAxioms( formula: HOLFormula, variables: Seq[Var] )( implicit ctx: Context ): ValidationNel[String, Seq[HOLFormula]] =
    {
      val axs = makeInductionAxioms( removeUniversalQuantifierPrefix( formula ), variables )
      axs filter { _.isFailure } match {
        case failure :: _ => for { _ <- failure } yield { List() }
        case _            => ( axs map { _ | Top() } ).success
      }
    }

  /**
   * Computes the list of induction axioms for a given formula and variables.
   *
   * @param formula The formula for which the induction axioms are generated.
   * @param variables The variables for which an induction axiom is generated.
   * @return A list of either induction axioms or errors. A an error message is
   * in the list if the corresponding axiom could not be created.
   */
  private def makeInductionAxioms( formula: HOLFormula, variables: Seq[Var] )( implicit ctx: Context ): Seq[ValidationNel[String, HOLFormula]] =
    variables map { v => makeAxiom( formula, v ) }

  /**
   * Computes an induction axiom for the given formula and the given variable.
   *
   * @param formula The formula subject to the induction axiom.
   * @param variable The induction variable.
   * @return Either a formula of the form:
   * !x_1,...,x_{k-1},x_{k+1},...,x_n( <IC(F,c_1,x_k)> ^...^ <IC(F,c_m,x_k)> -> !x_k F ),
   * given a formula F, a variable x_k such that
   * - F has free variables x_1,...,x_n
   * - x_k is inductive and has constructors c_1,...,c_m
   * - IC(F,c_i,x_k), with i = {1,...,m} symbolises the i-th inductive case;
   * or an error message if one of the above conditions is violated.
   */
  private def makeAxiom( formula: HOLFormula, variable: Var )( implicit ctx: Context ): ValidationNel[String, HOLFormula] =
    for {
      constructors <- getConstructors( baseType( variable ), ctx )
    } yield {
      val ics = constructors map { c => inductiveCase( formula, c, variable ) }
      val concl = All( variable, formula )
      val fvs = freeVariables( formula ).toSeq
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
   *     !y_1',...,!y_n'((F[y_1'/x] ^ ... ^ F[y_n'/x])
   *                      -> !z_1',...,!z_l' F[c(y_1',...y_n',z_1',...,z_l')/x]),
   * for a given variable x, a constructor c and a formula F such that
   * - x is of inductive type with constructor c
   * - x is a free variable of F
   * - c has free variables y_1,...,y_n,z_1,...,z_l
   * - the variables y_1,...,y_n are of the same type as x
   * - variables z_1,...,z_l are not of the same type as x
   * - variables y_1',...,y_n',z_1',...,z_l' are fresh variables for F.
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

object removeUniversalQuantifierPrefix {
  /**
   * Removes all leading universal quantifiers from the given formula.
   * @param f The formula from which the leading universal quantifiers are to be removed.
   * @return The formula f without leading universal quantifiers.
   */
  def apply( f: HOLFormula ): HOLFormula = f match {
    case HOLAtom( _, _ )
      | Top()
      | Bottom()
      | Imp( _, _ )
      | And( _, _ )
      | Or( _, _ )
      | Neg( _ )
      | Ex( _, _ ) => f
    case All( _, f0 ) => removeUniversalQuantifierPrefix( f0 )
    case _            => throw new Exception( "ERROR: Unexpected case while removing outermost universal quantifiers from a formula" )
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
   * !A!{X<x}( IC(x,c1) ^ ... ^ IC(x,cl) -> !x!{X>x}!{X'}F ),
   * where
   * the input variables are X
   * the input formula is of the form F' = !{X U X'}F
   * FV(F') = A
   * x in X
   * {X<x} and {X>x} are subsets of X containing all variables with index smaller/greater than the index of x.
   */
  def inductionAxioms( f: HOLFormula, vs: Seq[Var] )( implicit ctx: Context ): ValidationNel[String, Seq[HOLFormula]] = {
    val validations = makeInductionAxioms( f, vs )
    validations filter { _.isFailure } match {
      case e :: _ => for ( _ <- e ) yield List()
      case _      => validations map { _ | Top() } success
    }
  }

  /**
   * Computes a sequence of induction axioms for the given formula and variables.
   *
   * @param f The formula for which to compute induction axioms.
   * @param vs The variables for which induction axioms are generated.
   * @param ctx The context defining types, constants etc.
   * @return A list of validations containing either an axiom or an error message. The form of the axioms is as
   *         described for the inductionAxioms method.
   */
  private def makeInductionAxioms( f: HOLFormula, vs: Seq[Var] )( implicit ctx: Context ): Seq[ValidationNel[String, HOLFormula]] = {
    val fvs = freeVariables( f ).toSeq
    val f1 = removeUniversalQuantifierPrefix( f )
    val xvs = freeVariables( f1 ).toSeq.diff( fvs ).diff( vs )
    val f2 = All.Block( xvs, f1 )
    vs map {
      v => inductionAxiom( f2, vs, v )
    }
  }

  /**
   * Computes an induction axiom for the given formula and variable.
   *
   * @param f The formula for which the induction axiom is generated.
   * @param vs The list of variables equal to {X<v} ++ [v] ++ {X>v}.
   * @param v The variable for which the induction axiom is generated.
   * @param ctx The context defining types, constants, etc.
   * @return An induction axiom if v is of inductive type, an error message otherwise.
   */
  private def inductionAxiom( f: HOLFormula, vs: Seq[Var], v: Var )( implicit ctx: Context ): ValidationNel[String, HOLFormula] = {
    for {
      cs <- getConstructors( baseType( v ), ctx )
    } yield {
      val ( lvs, gvs ) = splitVarsAt( vs, v )
      val inductiveCases = cs map { c => inductiveCase( f, vs, v, c ) }
      val conclusion = All( v, All.Block( gvs, f ) )
      univclosure( All.Block( lvs, And( inductiveCases ) --> conclusion ) )
    }
  }

  /**
   * Generates the inductive case of the given formula, variable and constructor.
   *
   * @param f The formula for which the inductive case is generated.
   * @param vs The list of variables equal to {X<v} ++ [v] ++ {X>v}.
   * @param v The variable for which the inductive case is generated.
   * @param c The constructor of this inductive case.
   * @return The formula representing the inductive case.
   */
  private def inductiveCase( f: HOLFormula, vs: Seq[Var], v: Var, c: Con ): HOLFormula = {
    val ( _, gvs ) = splitVarsAt( vs, v )
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

  /**
   * Splits a list of variables at the given variable.
   *
   * @param vs The list of variables to be split.
   * @param v The variable around which the list is to be split
   * @return Given a variable xk and a list x1,...,xn such that xk occurs in the list and
   * the variables in the list are pairwise distinct, the result is (x1,...,x{k-1}; x{k+1},...xn).
   */
  private def splitVarsAt( vs: Seq[Var], v: Var ): ( Seq[Var], Seq[Var] ) = {
    val i = vs.indexOf( v )
    ( vs.take( i ), vs.drop( i + 1 ) )
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
  ): ValidationNel[String, Seq[Con]] =
    ctx.typeDef( typ.name ) match {
      case Some( Context.InductiveType( _, constructors ) ) => constructors.success
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
