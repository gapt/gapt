package gapt.provers.congruence

import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.resolution.structuralCNF
import gapt.proofs.{ HOLClause, HOLSequent }
import gapt.provers.OneShotProver
import gapt.provers.sat.Sat4j
import gapt.utils.Maybe

import scala.collection.mutable

object SimpleSmtSolver extends OneShotProver {
  override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ) =
    throw new NotImplementedError()

  override def isValid( seq: HOLSequent )( implicit ctx0: Maybe[Context] ): Boolean = {
    val cnf = structuralCNF( seq, propositional = true )
      .map( _.conclusion.asInstanceOf[HOLClause] )
      .to( mutable.Buffer )
    val cc = CC().intern( cnf.flatMap( _.elements ) )
    while ( true ) {
      Sat4j.solve( cnf ) match {
        case Some( model ) =>
          cc.merge( model.toCube.antecedent ).
            explain( model.toCube ) match {
              case Some( core ) =>
                cnf += core
              case None => return false
            }
        case None => return true
      }
    }
    throw new IllegalStateException
  }
}

