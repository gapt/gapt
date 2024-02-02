package gapt.proofs.gaptic

import gapt.formats.babel.BabelSignature

import language.experimental.macros
import scala.quoted.Expr
import scala.quoted.Quotes
import gapt.expr.formula.Formula

trait LemmaHelper[T] {
  inline def applyTactics[U](inline tacticsProof: => Tactic[U]) = LemmaMacros.applyTactics(this, tacticsProof)
  def handleTacticBlock( block: ProofState => ProofState ): T
}

object LemmaMacros {
  import scala.quoted.*

  inline def applyTactics[T,U](inline helper: LemmaHelper[T], inline tacticsProof: => Tactic[U] ): T = 
    ${LemmaMacros.helperImpl('helper, 'tacticsProof)}

  def use[T]( proofState: ProofState, tactical: Tactic[T] )( implicit sig: BabelSignature ): ProofState =
    ( try tactical( proofState ) catch {
      case t: Throwable =>
        throw new TacticFailureException(
          s"Exception when applying $tactical to proof state with sub goals:\n" +
            proofState.subGoals.map { _.toPrettyString }.mkString( "\n" ),
          t )
    } ) match {
      case Right( ( _, newState ) ) => newState
      case Left( error ) =>
        throw TacticFailureFailureException( error.defaultState( proofState ) )
    }

  private def constructProofState[T,U](proofState: Expr[ProofState], tacticsProof: Expr[Tactic[U]])(using Quotes, Type[Unit], Type[U], Type[Tactic[U]], Type[Tactic[Any]], Type[ProofState]): Expr[ProofState] = {
    import quotes.reflect.*
    
    def unwrapInlined(term: Term): Term = term match {
      case Inlined(_,_,t) => unwrapInlined(t)
      case t => t
    }

    val tacticTerms: List[Term] = unwrapInlined(tacticsProof.asTerm) match {
      case Block(stmts,term) => (stmts.asInstanceOf[List[Term]]) :+ term
      case term => List(term)
    }

    tacticTerms.foldLeft(proofState) { (proofState, tactic) => 
      '{LemmaMacros.use($proofState, ${tactic.asExprOf[Tactic[_]]})}
    }
  }

  def helperImpl[T,U](helper: Expr[LemmaHelper[T]], tacticsProof: Expr[Tactic[U]] )(using Quotes, Type[T], Type[U]): Expr[T] = 
    '{ $helper.handleTacticBlock(p => ${ constructProofState('{p}, tacticsProof) }) }
}
