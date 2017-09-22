package at.logic.gapt.examples.induction
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.folTermSize
import at.logic.gapt.expr.hol.universalClosure
import at.logic.gapt.formats.lisp.{ LAtom, LFun }
import at.logic.gapt.proofs.Context.InductiveType
import at.logic.gapt.proofs.expansion.ExpansionProof
import at.logic.gapt.proofs.{ Context, HOLSequent, MutableContext }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.reduction.ErasureReductionET
import at.logic.gapt.provers.{ OneShotProver, groundFreeVariables }
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.smtlib.CVC4
import at.logic.gapt.provers.viper.grammars.TreeGrammarProver
import at.logic.gapt.utils.{ Logger, Maybe }

object factorial extends TacticsProof {
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += hoc"'*': nat>nat>nat"
  ctx += hoc"fact: nat>nat"
  ctx += hoc"qfact: nat>nat>nat"

  Logger.makeVerbose( classOf[TreeGrammarProver] )
  // Problem: escargot uses fact(0) instead of s(0)...
  val qfact_correct = Lemma(
    hols"""
          om: !x s(0)*x = x,
          mo: !x x*s(0) = x,
          mc: !x!y x*y = y*x,
          mass: !x!y!z (x*y)*z = x*(y*z),
          f0: fact 0 = s(0),
          fs: !x fact (s x) = s x * fact x,
          qf0: !y qfact y 0 = y,
          qfs: !x!y qfact y (s x) = qfact (y * s x) x
          :- !x qfact (s 0) x = fact x
        """ ) {
      treeGrammarInduction
        .quantTys( "nat" )
        .equationalTheory(
          hof"x*(y*z) = (x*y)*z",
          hof"x*s(0) = x", hof"s(0)*x = x" )
        .canSolSize( 1, 1 )
        .instanceProver( new OneShotProver {
          override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = ???
          override def getExpansionProof( sequent: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] = {
            val reduction = ErasureReductionET
            val ( folProblem, back ) = reduction forward sequent
            Prover9.getExpansionProof( folProblem ).map( back )
          }
        } )
        .smtSolver( new OneShotProver {
          override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = ???

          import at.logic.gapt.provers.Session._
          override def isValid( seq: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean = {
            val ( groundSeq, _ ) = groundFreeVariables( seq )
            new CVC4( "UF", Seq( "--tlimit=300" ) ).runSession(
              for {
                _ <- declareSymbolsIn( groundSeq.elements :+ le"s(0) * 0" )
                _ <- assert( hof"!x!y!z x*(y*z)=(x*y)*z" )
                _ <- assert( hof"!x!y!z (x*y)*z=x*(y*z)" )
                _ <- assert( hof"!x x*s(0)=x" )
                _ <- assert( hof"!x s(0)*x=x" )
                _ <- assert( groundSeq.map( identity, -_ ).elements.toList )
                res <- ask( LFun( "check-sat" ) )
              } yield res == LAtom( "unsat" ) )
          }
        } )
    }
}
