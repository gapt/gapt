package at.logic.gapt.provers.viper.grammars2

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ folSubTerms, folTermSize }
import at.logic.gapt.expr.hol.{ CNFp, containsQuantifierOnLogicalLevel, instantiate, universalClosure }
import at.logic.gapt.formats.babel.BabelSignature
import at.logic.gapt.grammars.Rule
import at.logic.gapt.grammars.induction2.{ InductionGrammar, findMinimalInductionGrammar }
import at.logic.gapt.proofs.Context.StructurallyInductiveTypes
import at.logic.gapt.proofs.expansion.{ ExpansionProof, InstanceTermEncoding, minimalExpansionSequent }
import at.logic.gapt.proofs.lk.{ EquationalLKProver, LKProof, skolemize }
import at.logic.gapt.proofs.{ Context, HOLSequent, MutableContext, Sequent }
import at.logic.gapt.provers.{ OneShotProver, Prover }
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.maxsat.{ MaxSATSolver, bestAvailableMaxSatSolver }
import at.logic.gapt.provers.verit.VeriT
import at.logic.gapt.provers.viper.grammars.{ EnumeratingInstanceGenerator, hSolveQBUP }
import at.logic.gapt.provers.viper.grammars.TreeGrammarProverOptions.FloatRange
import at.logic.gapt.utils.{ Logger, Maybe }

import scala.collection.mutable

object DefaultProvers {
  val firstOrder: Prover = Escargot
  val smt: Prover =
    if ( VeriT.isInstalled ) VeriT
    else smtEscargot
  val smtEscargot = new Escargot( splitting = true, propositional = true, equality = true )
}

import TreeGrammarProverOptions._
case class TreeGrammarProverOptions(
    instanceNumber:   Int                 = 10,
    instanceSize:     FloatRange          = ( 0, 2 ),
    instanceProver:   Prover              = DefaultProvers.firstOrder,
    smtSolver:        Prover              = DefaultProvers.smt,
    smtEquationMode:  SmtEquationMode     = AddNormalizedFormula,
    findingMethod:    String              = "maxsat",
    quantTys:         Option[Seq[String]] = None,
    grammarWeighting: Rule => Int         = _ => 1,
    tautCheckNumber:  Int                 = 10,
    tautCheckSize:    FloatRange          = ( 2, 3 ),
    canSolSize:       FloatRange          = ( 2, 4 ),
    forgetOne:        Boolean             = false,
    maxSATSolver:     MaxSATSolver        = bestAvailableMaxSatSolver,
    equationalTheory: Seq[Formula]        = Seq() )

object TreeGrammarProverOptions {
  type FloatRange = ( Float, Float )

  trait SmtEquationMode { def adapt( th: Seq[Formula], p: Prover ): Prover }
  case object AddNormalizedFormula extends SmtEquationMode {
    override def adapt( th: Seq[Formula], p: Prover ): Prover =
      new OneShotProver {
        override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] =
          throw new NotImplementedError

        val eqTh = Normalizer( th.map( ReductionRule( _ ) ) )
        override def isValid( seq: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean =
          p.isValid( seq ++ seq.map( eqTh.normalize( _ ).asInstanceOf[Formula] ) )
      }
  }
  case object Passthru extends SmtEquationMode {
    override def adapt( th: Seq[Formula], p: Prover ): Prover =
      new OneShotProver {
        override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] =
          throw new NotImplementedError

        val eqTh: Seq[Formula] = th.map( universalClosure( _ ) )
        override def isValid( seq: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean =
          p.isValid( eqTh ++: seq )
      }
  }
}

class TreeGrammarProver( val ctx: Context, val sequent: HOLSequent, val options: TreeGrammarProverOptions ) extends Logger {
  implicit def ctx_ : Context = ctx

  val Sequent( theory, Seq( quantGoal @ All( v0, _ ) ) ) = sequent
  require( !containsQuantifierOnLogicalLevel( instantiate( quantGoal, v0 ) ) )

  val indTy = v0.ty.asInstanceOf[TBase]

  val quantTys = options.quantTys.getOrElse( ctx.get[StructurallyInductiveTypes].constructors.keySet - "o" ).toList.map( TBase( _ ) )
  val gamma = for ( ( t, i ) <- quantTys.zipWithIndex ) yield Var( s"γ_$i", t )

  val ( tau, alpha, nus ) = {
    val defaultNames = InductionGrammar.defaultNonTerminalNames(
      rename.awayFrom( containedNames( sequent ) ++ gamma ),
      indTy, InstanceTermEncoding.defaultType, gamma )
    ( defaultNames.tau, defaultNames.alpha, defaultNames.nus )
  }

  val goal = instantiate( quantGoal, alpha )

  val encoding = InstanceTermEncoding( sequent.map( identity, instantiate( _, alpha ) ) )

  val instanceGen = new EnumeratingInstanceGenerator( Seq( indTy ), implicitly )

  type Instance = Expr

  val smtSolver: Prover =
    if ( options.equationalTheory.isEmpty ) options.smtSolver
    else options.smtEquationMode.adapt( options.equationalTheory, options.smtSolver )

  def solve(): LKProof = {
    info( sequent )

    val instanceProofs = mutable.Map[Instance, ExpansionProof]()
    for ( Seq( inst ) <- instanceGen.generate( options.instanceSize._1, options.instanceSize._2, options.instanceNumber ) )
      instanceProofs( inst ) = getInstanceProof( inst )

    while ( true ) {
      val bup = findBUP( instanceProofs )

      for ( ( inst, _ ) <- instanceProofs ) {
        val genLang = bup.grammar.instanceLanguage( inst )
        require(
          smtSolver.isValid( encoding.decodeToInstanceSequent( genLang ).toNegConjunction --> instantiate( quantGoal, inst ) ),
          s"Generated instance language for $inst not tautological:\n${genLang.map( _.toSigRelativeString ).mkString( "\n" )}" )
      }

      findMinimalCounterexample( instanceProofs.keys, bup ) match {
        case Some( inst ) =>
          instanceProofs( inst ) = getInstanceProof( inst )

        case None =>
          return solveBUP( bup )
      }
    }
    throw new IllegalArgumentException
  }

  def findBUP( instanceProofs: Iterable[( Instance, ExpansionProof )] ): InductionBUP = {
    val indexedTermset = Map() ++
      instanceProofs.map { case ( inst, es ) => inst -> encoding.encode( es.expansionSequent.copy( succedent = Vector() ) ) }

    val Some( grammar ) = findMinimalInductionGrammar( indexedTermset, tau, alpha, nus, gamma, options.maxSATSolver )

    info( s"Found schematic proof with induction:\n$grammar\n" )
    for ( ( inst, terms ) <- indexedTermset ) {
      val genLang = grammar.instanceLanguage( inst )
      require(
        terms subsetOf genLang,
        s"Terms not covered by recursion scheme in $inst:\n${terms.map( _.toSigRelativeString ).mkString( "\n" )}" )
    }

    InductionBUP( grammar, encoding, goal )
  }

  def findMinimalCounterexample( correctInstances: Iterable[Instance], bup: InductionBUP ): Option[Expr] = {
    def checkInst( inst: Instance ): Boolean =
      smtSolver.isValid( encoding.decodeToInstanceSequent( bup.grammar.instanceLanguage( inst ) ).toNegConjunction -->
        instantiate( quantGoal, inst ) )
    val scale = ( 5 +: correctInstances.toSeq.map( folTermSize( _ ) ) ).max
    val testInstances =
      ( instanceGen.generate( 0, 5, 10 ) ++
        instanceGen.generate( options.tautCheckSize._1 * scale, options.tautCheckSize._2 * scale, options.tautCheckNumber ) ).map( _.head )
    val failedInstOption = testInstances.toSeq.
      sortBy( folTermSize( _ ) ).view.
      filterNot { inst =>
        val ok = checkInst( inst )
        info( s"Checking validity for instance ${inst.toSigRelativeString}: $ok" )
        ok
      }.headOption
    failedInstOption map { failedInst =>
      val minimalCounterExample = (
        folSubTerms( failedInst ).filter( _.ty == indTy ).toList.filterNot( checkInst )
        :+ failedInst ).minBy( expressionSize( _ ) )
      info( s"Minimal counterexample: ${minimalCounterExample.toSigRelativeString}" )
      minimalCounterExample
    }
  }

  def solveBUP( bup: InductionBUP ): LKProof = {
    val qbup @ Ex( x_B, qbupMatrix ) = bup.formula
    info( s"Solution condition:\n${qbup.toSigRelativeString}\n" )

    val canSolInst = instanceGen.generate( options.canSolSize._1, options.canSolSize._2, 1 ).head.head
    val xInst = bup.X( alpha, canSolInst )( gamma ).asInstanceOf[Formula]

    info( s"Canonical solution at ${xInst.toSigRelativeString}:" )
    val canSol = hSolveQBUP.canonicalSolution( qbupMatrix, xInst )
    for ( cls <- CNFp( canSol ) )
      info( cls map { _.toSigRelativeString } )

    val solution = hSolveQBUP( qbupMatrix, xInst, smtSolver, options.equationalTheory ).
      getOrElse( throw new IllegalArgumentException( s"Could not solve:\n${qbupMatrix.toSigRelativeString}" ) )

    info( s"Found solution: ${solution.toSigRelativeString}\n" )

    val formula = BetaReduction.betaNormalize( instantiate( qbup, solution ) )
    require( smtSolver.isValid( skolemize( formula ) )( ctx = Maybe.None ), "Solution not valid" )

    val proof = constructSIP(
      sequent, options.equationalTheory.toVector,
      bup,
      solution,
      if ( options.equationalTheory.isEmpty ) EquationalLKProver else Escargot )( ctx.newMutable )
    info( s"Found proof with ${proof.dagLike.size} inferences" )

    ctx.check( proof )

    proof
  }

  def getInstanceProof( inst: Instance ): ExpansionProof = {
    info( s"Proving instance ${inst.toSigRelativeString}" )
    val instanceSequent = sequent.map( identity, instantiate( _, inst ) )
    val instProof0 = options.instanceProver.getExpansionProof( instanceSequent ).getOrElse {
      throw new IllegalArgumentException( s"Cannot prove:\n$instanceSequent" )
    }
    val Some( instProof ) = minimalExpansionSequent( instProof0, smtSolver )
    require(
      smtSolver.isValid( instProof.deep ),
      s"Instance proof has invalid deep formula:\n${instProof.deep.toSigRelativeString}" )
    info( s"Instance proof for ${inst.toSigRelativeString}:" )
    info( instProof.toSigRelativeString )
    info( "Language:" )
    encoding.encode( instProof ).toSeq.map( _.toUntypedString( BabelSignature.defaultSignature ) ).sorted.foreach( info( _ ) )

    instProof
  }

}
