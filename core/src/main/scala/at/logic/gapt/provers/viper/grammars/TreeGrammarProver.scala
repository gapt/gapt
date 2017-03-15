package at.logic.gapt.provers.viper.grammars

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ folSubTerms, folTermSize }
import at.logic.gapt.expr.hol.{ CNFp, instantiate }
import at.logic.gapt.grammars.Rule
import at.logic.gapt.proofs.Context.{ BaseTypes, StructurallyInductiveTypes }
import at.logic.gapt.proofs.expansion.{ ExpansionProof, ExpansionProofToLK, InstanceTermEncoding }
import at.logic.gapt.proofs.lk.{ EquationalLKProver, LKProof, skolemize }
import at.logic.gapt.proofs.reduction._
import at.logic.gapt.proofs.{ Context, HOLSequent, Sequent }
import at.logic.gapt.prooftool.prooftool
import at.logic.gapt.provers.{ OneShotProver, Prover }
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.spass.SPASS
import at.logic.gapt.provers.verit.VeriT
import at.logic.gapt.provers.viper.grammars.TreeGrammarProverOptions.FloatRange
import at.logic.gapt.utils.Logger

import scala.collection.mutable

object SpassPred extends OneShotProver {
  override def getExpansionProof( seq: HOLSequent ): Option[ExpansionProof] = {
    val reduction = GroundingReductionET |> CNFReductionExpRes |> PredicateReductionCNF |> ErasureReductionCNF
    val ( erasedCNF, back ) = reduction forward seq
    SPASS.getResolutionProof( erasedCNF ).map { erasedProof =>
      back( erasedProof )
    }
  }

  override def getLKProof( seq: HOLSequent ): Option[LKProof] =
    getExpansionProof( seq ).flatMap( ExpansionProofToLK( _ ).toOption )
}

object SpassNoPred extends OneShotProver {
  override def getExpansionProof( seq: HOLSequent ): Option[ExpansionProof] = {
    val reduction = GroundingReductionET |> ErasureReductionET
    val ( erasedCNF, back ) = reduction forward seq
    SPASS.getExpansionProof( erasedCNF ).map { erasedProof =>
      back( erasedProof )
    }
  }

  override def getLKProof( seq: HOLSequent ): Option[LKProof] =
    getExpansionProof( seq ).flatMap( ExpansionProofToLK( _ ).toOption )
}

case class TreeGrammarProverOptions(
  instanceNumber:   Int                 = 10,
  instanceSize:     FloatRange          = ( 0, 2 ),
  instanceProver:   Prover              = Escargot,
  findingMethod:    String              = "maxsat",
  quantTys:         Option[Seq[String]] = None,
  grammarWeighting: Rule => Int         = _ => 1,
  tautCheckNumber:  Int                 = 10,
  tautCheckSize:    FloatRange          = ( 2, 3 ),
  canSolSize:       FloatRange          = ( 2, 4 ),
  forgetOne:        Boolean             = false
)

object TreeGrammarProverOptions {
  type FloatRange = ( Float, Float )
}

class TreeGrammarProver( val ctx: Context, val sequent: HOLSequent, val options: TreeGrammarProverOptions ) extends Logger {
  implicit def ctx_ = ctx

  val Sequent( theory, Seq( conj @ All.Block( vs, _ ) ) ) = sequent
  val paramTypes = vs.map( _.ty ).map( _.asInstanceOf[TBase] )

  val instanceGen = new EnumeratingInstanceGenerator( paramTypes, implicitly )

  val encoding = InstanceTermEncoding( sequent.map( identity, instantiate( _, vs ) ) )

  type Instance = Seq[Expr]

  val grammarFinder = options.findingMethod match {
    case "maxsat" | "maxsatinst" =>
      val pi1QTys = options.quantTys getOrElse ( ctx.get[StructurallyInductiveTypes].constructors.keySet - "o" ).toSeq
      val msrsf = MaxSatRecSchemFinder( vs.map( _.ty ), pi1QTys.flatMap( ctx.get[BaseTypes].baseTypes.get ), encoding.instanceTermType,
        options.grammarWeighting, options.findingMethod == "maxsatinst",
        implicitly )

      info( "Recursion scheme template:" )
      for ( ( lhs, rhs ) <- msrsf.template.template.toSeq.sortBy( _._1.toString ) )
        info( s"$lhs -> $rhs" )

      msrsf
  }

  val smtSolver =
    if ( VeriT.isInstalled ) VeriT
    else new Escargot( splitting = true, propositional = true, equality = true )

  def solve(): LKProof = {
    info( sequent )

    val instanceProofs = mutable.Map[Instance, ExpansionProof]()
    for ( inst <- instanceGen.generate( options.instanceSize._1, options.instanceSize._2, options.instanceNumber ) )
      instanceProofs( inst ) = getInstanceProof( inst )

    while ( true ) {
      val spwi = findSPWI( instanceProofs )

      for ( ( inst, _ ) <- instanceProofs ) {
        val genLang = spwi.generatedLanguage( inst )
        require(
          smtSolver.isValid( And( genLang ) --> instantiate( conj, inst ) ),
          s"Generated instance language for $inst not tautological:\n${genLang.map( _.toSigRelativeString ).mkString( "\n" )}"
        )
      }

      findMinimalCounterexample( instanceProofs.keys, spwi ) match {
        case Some( inst ) =>
          instanceProofs( inst ) = getInstanceProof( inst )

        case None =>
          return solveSPWI( spwi )
      }
    }
    throw new IllegalArgumentException
  }

  def findSPWI( instanceProofs: Iterable[( Instance, ExpansionProof )] ): SchematicProofWithInduction = {
    val taggedLanguage =
      for {
        ( inst, es ) <- instanceProofs
        term <- encoding.encode( es.expansionSequent.antecedent ++: Sequent() )
      } yield inst -> term

    val spwi = grammarFinder.find( sequent, encoding, implicitly[Context], taggedLanguage.toSet )

    info( s"Found schematic proof with induction:\n$spwi\n" )
    for ( ( Apps( _, inst ), terms ) <- taggedLanguage groupBy { _._1 } ) {
      val genLang = spwi.generatedLanguage( inst ).map( encoding.encode )
      require(
        terms.map { _._2 }.toSet subsetOf genLang,
        s"Terms not covered by recursion scheme in $inst:\n${terms.map { _._2.toSigRelativeString }.mkString( "\n" )}"
      )
    }

    spwi
  }

  def findMinimalCounterexample( correctInstances: Iterable[Instance], spwi: SchematicProofWithInduction ): Option[Seq[Expr]] = {
    def checkInst( inst: Seq[Expr] ): Boolean = smtSolver.isValid( And( spwi.generatedLanguage( inst ) ) --> instantiate( conj, inst ) )
    val scale = ( 5 +: correctInstances.toSeq.map( folTermSize( _ ) ) ).max
    val testInstances =
      instanceGen.generate( 0, 5, 10 ) ++
        instanceGen.generate( options.tautCheckSize._1 * scale, options.tautCheckSize._2 * scale, options.tautCheckNumber )
    val failedInstOption = testInstances.toSeq.
      sortBy( folTermSize( _ ) ).view.
      filterNot { inst =>
        val ok = checkInst( inst )
        info( s"Checking validity for instance ${inst.map( _.toSigRelativeString )}: $ok" )
        ok
      }.headOption
    failedInstOption map { failedInst =>
      import cats.instances.list._
      import cats.syntax.traverse._
      val minimalCounterExample = failedInst.toList.
        traverse( i => folSubTerms( i ).filter( _.ty == i.ty ).toList ).
        filterNot( checkInst ).
        minBy { _ map { expressionSize( _ ) } sum }
      info( s"Minimal counterexample: ${minimalCounterExample.map { _.toSigRelativeString }}" )
      minimalCounterExample
    }
  }

  def solveSPWI( spwi: SchematicProofWithInduction ) = {
    val qbup @ Ex( x_B, qbupMatrix ) = spwi.solutionCondition
    info( s"Solution condition:\n${qbup.toSigRelativeString}\n" )

    val axiomArgs = for ( ( t, i ) <- paramTypes.zipWithIndex ) yield Var( s"y_$i", t )
    val canSolInst = instanceGen.generate( options.canSolSize._1, options.canSolSize._2, 1 ).head
    val pi1QTys = FunctionType.unapply( x_B.ty ).get._2.drop( axiomArgs.size + canSolInst.size )
    val ws = for ( ( t, i ) <- pi1QTys.zipWithIndex ) yield Var( s"w_$i", t )
    val xInst = x_B( axiomArgs: _* )( canSolInst: _* )( ws: _* ).asInstanceOf[Formula]

    info( s"Canonical solution at ${xInst.toSigRelativeString}:" )
    val canSol = hSolveQBUP.canonicalSolution( qbupMatrix, xInst )
    for ( cls <- CNFp( canSol ) )
      info( cls map { _.toSigRelativeString } )

    val solution = hSolveQBUP( qbupMatrix, xInst, smtSolver ).
      getOrElse( throw new IllegalArgumentException( s"Could not solve ${qbupMatrix.toSigRelativeString}" ) )

    info( s"Found solution: ${solution.toSigRelativeString}\n" )

    val formula = BetaReduction.betaNormalize( instantiate( qbup, solution ) )
    require( smtSolver isValid skolemize( formula ), s"Solution not valid" )

    val proof = spwi.lkProof( Seq( solution ), EquationalLKProver )
    info( s"Found proof with ${proof.dagLike.size} inferences" )

    ctx.check( proof )

    proof
  }

  def getInstanceProof( inst: Seq[Expr] ) = {
    info( s"Proving instance ${inst.map( _.toSigRelativeString )}" )
    val instanceSequent = sequent.map( identity, instantiate( _, inst ) )
    val instProof = options.instanceProver.getExpansionProof( instanceSequent ).getOrElse {
      throw new IllegalArgumentException( s"Cannot prove:\n$instanceSequent" )
    }
    require( smtSolver.isValid( instProof.deep ) )
    info( s"Instance proof for ${inst.map( _.toSigRelativeString )}:" )
    info( instProof.toSigRelativeString )
    info( "Language:" )
    encoding.encode( instProof ).toSeq.map( _.toString ).sorted.foreach( info( _ ) )

    instProof
  }

}
