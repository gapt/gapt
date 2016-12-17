package at.logic.gapt.provers.viper

import at.logic.gapt.expr.hol._
import at.logic.gapt.expr.{ All, And, FunctionType, HOLFormula, Substitution, TBase, Var, freeVariables, rename, Const => Con }
import at.logic.gapt.formats.tip.{ TipProblem, TipSmtParser }
import at.logic.gapt.proofs.expansion.ExpansionProof
import at.logic.gapt.proofs.gaptic.NewLabels
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.reduction._
import at.logic.gapt.proofs.resolution.{ ResolutionProof, eliminateSplitting }
import at.logic.gapt.proofs.{ Ant, Context, HOLSequent, Sequent }
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.provers.eprover.EProver
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.spass.SPASS
import at.logic.gapt.provers.vampire.Vampire
import better.files._

import scalaz.Scalaz._
import scalaz.Validation.FlatMap.ValidationFlatMapRequested
import scalaz.ValidationNel

trait InductionStrategy {
  type ThrowsError[T] = ValidationNel[String, T]

  /**
   * Computes induction axioms for a formula and variables.
   * @param f The formula for which induction axioms are to be generated.
   * @param vs The variables for which induction axioms are to be generated.
   * @param ctx Defines inductive types etc.
   * @return Either a list of induction axioms or a non empty list of strings describing the why induction axioms
   *         could not be generated.
   */
  def inductionAxioms( f: HOLFormula, vs: List[Var] )( implicit ctx: Context ): ThrowsError[List[HOLFormula]]
}

object prover9 extends ManySortedProver( Prover9 )
object eprover extends ManySortedProver( EProver )
object escargot extends InternalProver( Escargot )
object vampire extends ManySortedProver( Vampire )
object spass extends ManySortedProver( SPASS )

class InternalProver( prover: ResolutionProver ) {
  /**
   * Checks a sequent for validity.
   * @param sequent The sequent to check for validity.
   * @return true if the sequent is valid, else false or the method does not terminate.
   */
  def isValid( sequent: HOLSequent ): Boolean = prover.isValid( sequent )

  /**
   * Tries to compute a resolution proof for a sequent.
   * @param sequent The sequent to prove.
   * @return A resolution proof if the sequent is provable, otherwise None or the method does not terminate.
   */
  def resolutionProof( sequent: HOLSequent ): Option[ResolutionProof] = prover.getResolutionProof( sequent )

  /**
   * Tries to compute an expansion proof for a sequent.
   * @param sequent The sequent to prove.
   * @return An expansion proof if the sequent is provable, otherwise None or the method does not terminate.
   */
  def expansionProof( sequent: HOLSequent ): Option[ExpansionProof] = prover.getExpansionProof( sequent )

  /**
   * Tries to compute a LK proof for a sequent.
   * @param sequent The sequent to prove.
   * @return A LK proof if the sequent is provable, otherwise None or the method does not terminate.
   */
  def lkProof( sequent: HOLSequent ): Option[LKProof] = prover.getLKProof( sequent )
}

class ManySortedProver( prover: ResolutionProver ) extends InternalProver( prover ) {
  override def isValid( sequent: HOLSequent ): Boolean = {
    val reduction = CNFReductionLKRes |> PredicateReductionCNF |> ErasureReductionCNF
    val ( folProblem, _ ) = reduction forward sequent
    prover.getResolutionProof( folProblem ).isDefined
  }
  override def expansionProof( sequent: HOLSequent ): Option[ExpansionProof] = {
    val reduction = PredicateReductionET |> ErasureReductionET
    val ( folProblem, back ) = reduction forward sequent
    prover.getExpansionProof( folProblem ).map( back )
  }

  override def resolutionProof( sequent: HOLSequent ): Option[ResolutionProof] = {
    val reduction = CNFReductionResRes |> PredicateReductionCNF |> ErasureReductionCNF
    val ( folProblem, back ) = reduction forward sequent
    prover.getResolutionProof( folProblem ).map( back )
  }

  override def lkProof( sequent: HOLSequent ): Option[LKProof] = {
    val reduction = CNFReductionLKRes |> PredicateReductionCNF |> ErasureReductionCNF
    val ( folProblem, back ) = reduction forward sequent
    prover.getResolutionProof( folProblem ).map( proof => back( eliminateSplitting( proof ) ) )
  }
}

case class ProverOptions(
  prover:    InternalProver    = new InternalProver( Escargot ),
  axiomType: InductionStrategy = sequentialInductionAxioms
)
case class AipOptions(
  printSummary: Boolean = false,
  printWitness: Boolean = false,
  printHelp:    Boolean = false,
  witness:      String  = "existential",
  prover:       String  = "escargot",
  axioms:       String  = "sequential",
  infile:       String  = null
)

class AnalyticInductionProver( options: ProverOptions ) {

  type ThrowsError[T] = ValidationNel[String, T]

  private implicit def labeledSequentToHOLSequent( sequent: Sequent[( String, HOLFormula )] ) =
    sequent map { case ( _, f ) => f }

  /**
   * Tries to prove a sequent by using analytic induction.
   * @param sequent The sequent to prove.
   * @param label The label of the formula for which induction axioms are added.
   * @param ctx Defines inductive types etc.
   * @return true if the sequent is provable with analytic induction, otherwise either false or the method does
   *         not terminate.
   */
  def isValid( sequent: Sequent[( String, HOLFormula )], label: String )( implicit ctx: Context ) =
    options.prover.isValid( inductiveSequent( sequent, label ) )

  /**
   * Tries to compute a LK proof for a sequent by using analytic induction.
   * @param sequent The sequent to prove.
   * @param label The label of the formula for which induction axioms are added.
   * @param variables The variables for which induction axioms are added.
   * @param ctx Defines inductive types etc.
   * @return An LK proof if the sequent is provable with analytic induction, otherwise either None or the method does
   *         not terminate.
   */
  def lkProof(
    sequent:   Sequent[( String, HOLFormula )],
    label:     String,
    variables: List[Var]
  )( implicit ctx: Context ) = options.prover.lkProof( inductiveSequent( sequent, label ) )

  /**
   * Tries to compute a LK proof for a sequent by using analytic induction.
   * @param sequent The sequent to prove.
   * @param label The label of the formula for which induction axioms are added.
   * @param ctx Defines inductive types etc.
   * @return An LK proof if the sequent is provable with analytic induction, otherwise either None or the method does
   *         not terminate.
   */
  def lkProof( sequent: Sequent[( String, HOLFormula )], label: String )( implicit ctx: Context ) =
    options.prover.lkProof( inductiveSequent( sequent, label ) )

  /**
   * Tries to compute a resolution proof for a sequent by using analytic induction.
   * @param sequent The sequent to prove.
   * @param label The label of the formula for which induction axioms are added.
   * @param ctx Defines inductive types etc.
   * @return A resolution proof if the sequent is provable with analytic induction, otherwise either None or the
   *         method does not terminate.
   */
  def resolutionProof( sequent: Sequent[( String, HOLFormula )], label: String )( implicit ctx: Context ) =
    options.prover.resolutionProof( inductiveSequent( sequent, label ) )

  /**
   * Tries to compute an expansion proof for a sequent by using analytic induction.
   * @param sequent The sequent to prove.
   * @param label The label of the formula for which induction axioms are added.
   * @param ctx Defines inductive types etc.
   * @return An expansion proof if the sequent is provable with analytic induction, otherwise either None or the
   *         method does not terminate.
   */
  def expansionProof( sequent: Sequent[( String, HOLFormula )], label: String )( implicit ctx: Context ) =
    options.prover.expansionProof( inductiveSequent( sequent, label ) )

  /**
   * Extracts the inductive sequent from a validation value.
   * @param validation The validation value from which the sequent is extracted.
   * @return A sequent.
   * @throws Exception If the validation value represents a validation failure.
   */
  private def validate( validation: ThrowsError[Sequent[( String, HOLFormula )]] ): Sequent[( String, HOLFormula )] =
    validation.valueOr( es => throw new Exception( es.tail.foldLeft( es.head ) { _ ++ "\n" ++ _ } ) )

  /**
   * Computes a sequent enriched by induction axioms.
   * @param sequent The sequent to which induction axioms are added.
   * @param label The formula for which induction axioms are to be generated.
   * @param variables The variables for which induction axioms are to be generated.
   * @param ctx Defines inductive types etc.
   * @return The original sequent enriched by induction axioms.
   */
  private def inductiveSequent(
    sequent:   Sequent[( String, HOLFormula )],
    label:     String,
    variables: List[Var]
  )( implicit ctx: Context ): Sequent[( String, HOLFormula )] =
    validate( prepareSequent( sequent, label, variables ) )

  /**
   * Computes a sequent enriched by induction axioms.
   * @param sequent The sequent to which induction axioms are added.
   * @param label The formula for which induction axioms are to be generated.
   * @param ctx Defines inductive types etc.
   * @return The original sequent enriched by induction axioms for all free variables and all outer-most universally
   *         quantified variables.
   */
  private def inductiveSequent(
    sequent: Sequent[( String, HOLFormula )],
    label:   String
  )( implicit ctx: Context ): Sequent[( String, HOLFormula )] =
    validate( prepareSequent( sequent, label ) )

  /**
   * Adds induction axioms for a formula to a given sequent.
   *
   * @param sequent The sequent to which the induction axioms are added.
   * @param label The label which designates a formula in the sequent.
   * @param variables The variables for which induction axioms are generated.
   * @param ctx The context which defines types, constants, etc.
   * @return A sequent with induction axioms for the specified formula and variables if label designates a formula
   *         in the given sequent and all of the given variables are of inductive type (w.r.t. the given context).
   *         Otherwise a string describing the error is returned.
   */
  private def prepareSequent(
    sequent:   Sequent[( String, HOLFormula )],
    label:     String,
    variables: List[Var]
  )( implicit ctx: Context ): ThrowsError[Sequent[( String, HOLFormula )]] = {
    for {
      formula <- findFormula( sequent, label )
      axioms <- options.axiomType.inductionAxioms( formula, variables )
    } yield {
      ( axioms zip variables ).foldLeft( sequent )( { labelInductionAxiom( label, _, _ ) } )
    }
  }

  /**
   * Adds induction axioms for a formula to a given sequent.
   *
   * @param sequent The sequent to which the induction axioms are added.
   * @param label The label which designates a formula in the sequent.
   * @param ctx The context which defines types, constants, etc.
   * @return A sequent with induction axioms for the formula designated by the given label. The returned sequent
   *         contains one axioms for every free variable and every universally quantified in the universal quantifier
   *         prefix of the formula.
   */
  private def prepareSequent(
    sequent: Sequent[( String, HOLFormula )],
    label:   String
  )( implicit ctx: Context ): ThrowsError[Sequent[( String, HOLFormula )]] = {
    for {
      formula <- findFormula( sequent, label )
      All.Block( _, f ) = formula
      variables = freeVariables( f ).filter( { hasInductiveType( _ ) } ).toList
      axioms <- options.axiomType.inductionAxioms( formula, variables )
    } yield {
      ( axioms zip variables ).foldLeft( sequent )( { labelInductionAxiom( label, _, _ ) } )
    }
  }

  /**
   * Checks whether the given variable has is of inductive type in the given context.
   *
   * @param v The variable for which to check the type.
   * @param ctx The context w.r.t. to which the variable's type is checked.
   * @return Returns true if the variable v is of inductive type in the context ctx, false otherwise.
   */
  private def hasInductiveType( v: Var )( implicit ctx: Context ): Boolean =
    ctx.getConstructors( baseType( v ) ).isDefined

  /**
   * Adds a labelled induction axiom to the sequent.
   *
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
    ( ctx.isType( typ ), ctx.getConstructors( typ ) ) match {
      case ( true, Some( constructors ) ) => constructors.toList.success
      case ( true, None )                 => s"Type $typ is not inductively defined".failureNel
      case ( false, _ )                   => s"Type $typ is not defined".failureNel
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

trait Witness {
  def isPositive: Boolean
}

object aip {

  implicit def bool2Witness( b: Boolean ): Witness = new Witness {
    override def isPositive: Boolean = b
    override def toString(): String = if ( isPositive ) b.toString else "There is no proof"
  }
  implicit def opt2Witness[T]( opt: Option[T] ): Witness = new Witness {
    override def isPositive: Boolean = opt.isDefined
    override def toString(): String = if ( isPositive ) opt.get.toString else "There is no proof"
  }

  case class ValidationException( message: String ) extends Exception( message )

  type AipInvokation[P, W] = ( AnalyticInductionProver, P ) => W

  val axioms = Map[String, InductionStrategy](
    "sequential" -> sequentialInductionAxioms,
    "independent" -> independentInductionAxioms
  )

  val provers = Map[String, InternalProver](
    "prover9" -> prover9,
    "eprover" -> eprover,
    "escargot" -> escargot,
    "spass" -> spass,
    "vampire" -> vampire
  )

  val witnessAipInvokers = Map[String, AipInvokation[TipProblem, Witness]](
    "existential" -> ( ( aip, p ) => {
      val ( sequent, label, ctx ) = tipProblem2Aip( p )
      aip.isValid( sequent, label )( ctx )
    } ),
    "lkproof" -> ( ( aip, p ) => {
      val ( sequent, label, ctx ) = tipProblem2Aip( p )
      aip.lkProof( sequent, label )( ctx )
    } ),
    "expansionproof" -> ( ( aip, p ) => {
      val ( sequent, label, ctx ) = tipProblem2Aip( p )
      aip.expansionProof( sequent, label )( ctx )
    } ),
    "resolutionproof" -> ( ( aip, p ) => {
      val ( sequent, label, ctx ) = tipProblem2Aip( p )
      aip.resolutionProof( sequent, label )( ctx )
    } )
  )

  val cmdOptRegex = """--([a-zA-Z0-9-]+)(?:=(\S*))?""".r

  def main( args: Array[String] ): Unit = {
    try {
      val options = parseArguments( args.toList )
      if ( options.printHelp ) {
        println( helpMessage )
        System exit 0
      }
      try {
        val aip = new AnalyticInductionProver( compileProverOptions( options ) )
        val problem = TipSmtParser fixupAndParse options.infile.toFile
        val ( witness, t ) = time {
          witnessAipInvokers.get( options.witness ).get( aip, problem )
        }
        val status = if ( witness.isPositive ) "success" else "failure"
        if ( options.printSummary )
          println( summary( options, status, t ) )
        if ( options.printWitness )
          println( witness )
      } catch {
        case e: Exception => {
          val errorMessage = summary( options, "error", -1 )
          System.out.println( errorMessage )
          System.err.print( errorMessage + " : " )
          e.printStackTrace( System.err )
        }
      }
    } catch {
      case ValidationException( message ) => println( message )
    }
  }

  private def summary( options: AipOptions, status: String, time: Long ) = {
    val t =
      if ( time >= 0 )
        "%.2f".format( nanoSeconds2Seconds( time ) )
      else
        "-1"
    "%s %s %s %s %s".format( options.prover, options.axioms, options.infile, status, t )
  }
  private def nanoSeconds2Seconds( ns: Long ): Double = ns.toDouble / 1000000000

  private def time[R]( block: => R ): ( R, Long ) = {
    val t0 = System.nanoTime
    val r = block
    val t1 = System.nanoTime
    ( r, t1 - t0 )
  }

  private def tipProblem2Aip( problem: TipProblem ): ( Sequent[( String, HOLFormula )], String, Context ) = {
    val sequent = problem.toSequent.zipWithIndex.map {
      case ( f, Ant( i ) ) => s"h$i" -> f
      case ( f, _ )        => "goal" -> f
    }
    ( sequent, "goal", problem.context )
  }

  private def usage: String = "usage: aip [OPTIONS] FILE"

  def parseArguments( args: List[String] ): AipOptions = parseArguments( Map(), args )

  def parseArguments( options: Map[String, String], args: List[String] ): AipOptions = {
    args match {
      case cmdOptRegex( k, v ) :: remainder => parseArguments( options + ( k -> v ), remainder )
      case infile :: Nil                    => parseOptions( options, infile )
      case Nil                              => throw new ValidationException( usage )
      case _                                => throw new ValidationException( "Illegal command line arguments" )
    }
  }

  private def parseOptions( options: Map[String, String], infile: String ) = {
    options.foldRight( AipOptions( infile = infile ) )( ( opts_, opts ) => parseAndApply( opts_._1, opts_._2, opts ) )
  }

  private def parseAndApply( option: String, value: String, options: AipOptions ): AipOptions =
    option match {
      case "prover" =>
        provers.get( value ) match {
          case None => throw new ValidationException( invalidArgument( option, value ) )
          case _    => options.copy( prover = value )
        }
      case "witness" =>
        witnessAipInvokers.get( value ) match {
          case None => throw new ValidationException( invalidArgument( option, value ) )
          case _    => options.copy( witness = value )
        }
      case "axioms" =>
        axioms.get( value ) match {
          case None => throw new ValidationException( invalidArgument( option, value ) )
          case _    => options.copy( axioms = value )
        }
      case "print-summary" =>
        if ( value == null )
          options.copy( printSummary = true )
        else
          throw new ValidationException( noArgumentAllowed( option ) )
      case "print-witness" =>
        if ( value == null )
          options.copy( printWitness = true )
        else
          throw new ValidationException( noArgumentAllowed( option ) )
      case "help" =>
        if ( value == null )
          options.copy( printHelp = true )
        else
          throw new ValidationException( noArgumentAllowed( option ) )
      case _ => throw new ValidationException( badOption( option ) )
    }

  private def invalidArgument( option: String, value: String ): String =
    s"Invalid argument `$value' to option '--$option'"

  private def noArgumentAllowed( option: String ): String =
    s"Option '--$option' does not allow an argument"

  private def badOption( option: String ): String =
    s"Unsupported option '--$option'"

  private def helpMessage: String =
    usage + "\n" +
      """Solve the TIP problem specified by FILE by using analytic induction on the goal.
      |
      |  --help             outputs this help text.
      |  --prover           use the specified prover for proof search, possible values for
      |                       this option are: escargot, prover9, vampire, spass, eprover.
      |  --axioms           use the specified type of induction axioms, possible values
      |                       are: independent, sequential.
      |  --witness          search for the specified type of proof, legal values are:
      |                       existential, lkproof, expansionproof, resolutionproof. If the value
      |                       existential is provided for this option, the prover will only check
      |                       the validity of the given problem without providing a proof.
      |  --print-summary    print a one-liner summarizing the results of the run.
      |  --print-proof      print the proof if one was found.
    """.stripMargin

  private def compileProverOptions( options: AipOptions ): ProverOptions =
    ProverOptions(
      provers.get( options.prover ).get,
      axioms.get( options.axioms ).get
    )

}
