/**
 * Description: An abstract prover
 */

package at.logic.gapt.provers.atp

import at.logic.gapt.expr.FOLExpression
import at.logic.gapt.proofs.lk.algorithms.subsumption.StillmanSubsumptionAlgorithmFOL
import at.logic.gapt.language.fol.algorithms.{ UnificationAlgorithm, FOLMatchingAlgorithm, FOLUnificationAlgorithm }
import at.logic.gapt.proofs.resolution.{ Clause, ResolutionProof }
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.formats.simple.SimpleResolutionParserFOL
import at.logic.gapt.formats.readers.FileReader
import at.logic.gapt.provers.atp.commands.base._
import at.logic.gapt.provers.atp.commands.logical.DeterministicAndCommand
import at.logic.gapt.provers.atp.commands.logical.DeterministicMacroCommand
import at.logic.gapt.provers.atp.commands.refinements.base.SequentsMacroCommand
import at.logic.gapt.utils.executionModels.ndStream.{ Configuration, NDStream }
import at.logic.gapt.utils.executionModels.searchAlgorithms.BFSAlgorithm
import at.logic.gapt.utils.logging.Logger

import collection.mutable.HashMap

import commands.guided.IsGuidedNotFoundCommand
import commands.refinements.simple.SimpleRefinementGetCommand
import commands.robinson.VariantsCommand
import commands.base._
import commands.ui._
import commands.sequents._
import commands.robinson._

object Definitions {
  type State = HashMap[String, Any]
}

import Definitions._

object Main {

  def stream1: Stream[Command[Clause]] = Stream.cons( getTwoClausesFromUICommand[Clause]( PromptTerminal.GetTwoClauses ),
    Stream.cons( VariantsCommand,
      Stream.cons( DeterministicAndCommand[Clause]( (
        List( ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand( FOLUnificationAlgorithm ), FactorCommand( FOLUnificationAlgorithm ) ),
        List( ParamodulationCommand( FOLUnificationAlgorithm ) ) ) ),
        Stream.cons( SimpleForwardSubsumptionCommand[Clause]( StillmanSubsumptionAlgorithmFOL ),
          Stream.cons( SimpleBackwardSubsumptionCommand[Clause]( StillmanSubsumptionAlgorithmFOL ),
            Stream.cons( InsertResolventCommand[Clause],
              Stream.cons( RefutationReachedCommand[Clause], stream1 ) ) ) ) ) ) )
  def stream: Stream[Command[Clause]] = Stream.cons( SetTargetClause( FSequent( List(), List() ) ), Stream.cons( SearchForEmptyClauseCommand[Clause], stream1 ) )
  def main( args: Array[String] ) {
    if ( args.length < 1 ) {
      println( helpmsg )
      return
    }
    val prover = new Prover[Clause] {}
    prover.refute( Stream.cons( SetClausesCommand( ( new FileReader( args( 0 ) ) with SimpleResolutionParserFOL ).getClauseList ), stream ) ).next
  }

  val helpmsg = "usage: ./atp.sh filename"

}

/**
 * Given a clause c and a set of clauses C, this algorithm instantiates ATP to search for
 *    a Robinson resolution derivation (either propositional or first-order) of a clause c'
 *    such that c' subsumes c.
 *
 *   TODO: At the moment, the ATP configuration is taken from a test due to Tomer.
 *         It does not find some derivations, e.g. of P from P | P. It should
 *         be fixed such that it returns a derivation of a clause subsuming the given
 *         clause, if such a refutation exists.
 */

object SearchDerivation extends at.logic.gapt.utils.logging.Logger {

  // to force ATP to do propositional resolution, we use a "unification algorithm"
  // that only finds a unifier for identical formulas.
  val triv_unification = new UnificationAlgorithm {
    def unify( term1: FOLExpression, term2: FOLExpression ) =
      FOLUnificationAlgorithm.unify( term1, term2 ) match {
        case s :: _ if ( s.isIdentity ) => s :: Nil
        case _                          => Nil
      }
  }

  def stream1( alg: UnificationAlgorithm ): Stream[Command[Clause]] = Stream.cons( SequentsMacroCommand[Clause](
    SimpleRefinementGetCommand[Clause],
    List( ClauseFactorCommand( alg ), ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand( alg ),
      InsertResolventCommand[Clause] ),
    SubsumedTargedReachedCommand[Clause] ), stream1( alg ) )
  def stream( f: FSequent, alg: UnificationAlgorithm ): Stream[Command[Clause]] = Stream.cons( SetTargetClause( f ), Stream.cons( SearchForEmptyClauseCommand[Clause], stream1( alg ) ) )

  object MyProver extends Prover[Clause]

  def apply( initial_clauses: Seq[FSequent], target: FSequent, propositional: Boolean = false ) = {
    val alg = if ( propositional ) triv_unification else FOLUnificationAlgorithm
    val msg = if ( propositional ) "propositional" else "first-order"
    trace( "Looking for a " + msg + " resolution derivation of " + target + " from " + initial_clauses + "." )
    MyProver.refute( Stream.cons( SetClausesCommand( initial_clauses ), stream( target, alg ) ) ).next
  }
}

class ProverException( msg: String ) extends Exception( msg )

trait Prover[V <: Sequent] extends Logger {

  def refute( commands: Stream[Command[V]] ): NDStream[ResolutionProof[V]] = {
    //println("\nrefute")
    new NDStream( new MyConfiguration( new State(), commands, () ), myFun ) with BFSAlgorithm
  }

  private[Prover] class MyConfiguration( val state: State, val commands: Stream[Command[V]], val data: Any, val result: Option[ResolutionProof[V]] ) extends Configuration[ResolutionProof[V]] {
    def this( state: State, commands: Stream[Command[V]], data: Any ) = this( state, commands, data, None )
    def isTerminal = result != None
  }

  private[Prover] def myFun( c: Configuration[ResolutionProof[V]] ): Iterable[Configuration[ResolutionProof[V]]] = {
    val conf = c.asInstanceOf[MyConfiguration]
    //Console.println("debug -- command: " + Console.RED + conf.commands.head.getClass + Console.RESET +", data: " + conf.data + ", next Command: " + conf.commands.tail.head.getClass)
    if ( conf.commands.isEmpty ) {
      println( "\nconf.commands.isEmpty !\n" )
      List()
    } else {
      //if (!conf.commands.head.toString.matches("(VariantsCommand|IsGuidedNotFoundCommand|SimpleRefinementGetCommand|ClauseFactorCommand).*"))
      debug(s"Executing command: ${conf.commands.head.getClass.getSimpleName} :: ${conf.commands.head}")

      conf.commands.head match {
        case com: InitialCommand[_] => com( conf.state ).map( x => new MyConfiguration( x._1, conf.commands.tail, x._2 ) )
        case com: DataCommand[_] => {
          val res = com( conf.state, conf.data )
          //println("==> Command: " + com.toString)
          //println("Result of data command: " + res)
          if ( res.isEmpty ) List( new MyConfiguration( conf.state, skipNonInit( conf.commands.tail ), () ) )
          else res.map( x => new MyConfiguration( x._1, conf.commands.tail, x._2 ) )
        }
        case com: ResultCommand[_] => List( new MyConfiguration( conf.state, conf.commands.tail, conf.data, com( conf.state, conf.data ) ) )
        case com: DeterministicMacroCommand[_] => {
          val res = com( conf.state )
          res._1.map( x => new MyConfiguration( x._1, conf.commands.tail, conf.data, x._2 ) ) ++
            ( if ( res._2 ) List( new MyConfiguration( conf.state, conf.commands.tail, conf.data ) ) else List() )
        }
        case com: BranchCommand[_]  => com.commands.map( x => new MyConfiguration( conf.state, x ++ conf.commands.tail, conf.data ) )
        case com: PrependCommand[_] => List( new MyConfiguration( conf.state, ( com.commands ).foldRight( conf.commands.tail )( ( x, c ) => x +: c ), conf.data ) )
        case com: PrependOnCondCommand[_] => if ( com.cond( conf.state, conf.data ) ) List( new MyConfiguration( conf.state, ( com.commands ).foldRight( conf.commands.tail )( ( x, c ) => x +: c ), conf.data ) )
        else List( new MyConfiguration( conf.state, conf.commands.tail, conf.data ) )
        // this command should create a whole new subtree using different state and commands for replay of sub proofs
        case com: SpawnCommand[_] => {
          val state = new State() ++= conf.state += ( ( "old_commands", conf.commands.tail ) ) += ( ( "old_state", conf.state ) )
          List( new MyConfiguration( state, conf.data.asInstanceOf[Stream[Command[V]]], conf.data ) )
        }
        case com: RestoreCommand[_]   => List( new MyConfiguration( conf.state( "old_state" ).asInstanceOf[State], ( com.commands ).foldRight( conf.state( "old_commands" ).asInstanceOf[Stream[Command[V]]] )( ( x, c ) => x +: c ), conf.data ) )
        case com: SetStreamCommand[_] => List( new MyConfiguration( conf.state, conf.data.asInstanceOf[Stream[Command[V]]], conf.data ) )
      }
    }
  }

  private[Prover] def skipNonInit( stream: Stream[Command[V]] ): Stream[Command[V]] = stream.head match {
    case com: InitialCommand[_] => stream
    case _                      => skipNonInit( stream.tail )
  }
}
