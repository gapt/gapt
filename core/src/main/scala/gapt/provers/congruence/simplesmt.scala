package gapt.provers.congruence

import gapt.expr._
import gapt.proofs.resolution.structuralCNF
import gapt.proofs.{ Context, HOLClause, HOLSequent, MutableContext, Sequent }
import gapt.provers.OneShotProver
import gapt.provers.sat.Sat4j
import gapt.utils.Maybe

import scala.collection.mutable

object checkSmtConflict {
  import gapt.proofs.congruence._
  def apply( sequent: HOLSequent, theory: CongruenceClosure => CongruenceClosure ): Option[HOLSequent] = {
    var cc = CongruenceClosure()
    for ( f <- sequent ) cc = cc.internalize( f )
    for ( eq @ Eq( _, _ ) <- sequent.antecedent ) cc = cc.merge( Input( eq ) )
    cc = cc.saturate( theory )

    def coreFromProof( p: CongruenceProof ): HOLSequent =
      p.subProofs.collect { case Input( f ) => f } ++: Sequent()

    // Tautology
    for {
      a <- sequent.antecedent
      b <- sequent.succedent
      p <- cc.getEqvProof( a, b )
    } return Some( ( a +: coreFromProof( p ) :+ b ).distinct )

    // Inequality
    for {
      eq @ Eq( a, b ) <- sequent.succedent
      p <- cc.getEqvProof( a, b )
    } return Some( coreFromProof( p ) :+ eq )

    None
  }
}

class SimpleSmtSolver( theory: CongruenceClosure => CongruenceClosure ) extends OneShotProver {
  override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ) =
    throw new NotImplementedError()

  override def isValid( seq: HOLSequent )( implicit ctx0: Maybe[Context] ): Boolean = {
    val cnf = structuralCNF( seq, propositional = true )
      .map( _.conclusion.asInstanceOf[HOLClause] )
      .to[mutable.Buffer]
    while ( true ) {
      Sat4j.solve( cnf ) match {
        case Some( model ) =>
          checkSmtConflict( model.toCube, theory ) match {
            case Some( core ) =>
              cnf += core.asInstanceOf[HOLClause]
            case None => return false
          }
        case None => return true
      }
    }
    throw new IllegalStateException
  }
}

object SimpleSmtSolver extends SimpleSmtSolver( identity )
