package at.logic.gapt.proofs.resolution3

import at.logic.gapt.expr.{ HOLAtom, HOLFormula }
import at.logic.gapt.proofs.{ HOLClause, HOLSequent, OccConnector }

import scala.collection.mutable

object mapInputClauses {

  def apply( proof: ResolutionProof, factorEarly: Boolean = false )( f: HOLSequent => ResolutionProof ): ResolutionProof =
    withOccConn( proof ) { sequent =>
      val q = f( sequent )
      q -> OccConnector.guessInjection( sequent, q.conclusion )
    }

  def withOccConn( proof: ResolutionProof, factorEverything: Boolean = false )( f: HOLSequent => ( ResolutionProof, OccConnector[HOLFormula] ) ): ResolutionProof = {
    val memo = mutable.Map[ResolutionProof, ( ResolutionProof, OccConnector[HOLFormula] )]()

    def doFactor( p: ResolutionProof, res: ( ResolutionProof, OccConnector[HOLFormula] ) ): ( ResolutionProof, OccConnector[HOLFormula] ) = {
      val ( newP, conn ) = res
      check( p, if ( factorEverything ) {
        val ( facP, facConn ) = Factor.withOccConn( newP )
        val facConn_ = facConn.copy( parentsSequent = facConn.parentsSequent.map { _ take 1 } )
        ( facP, facConn_ * conn )
      } else {
        res
      } )
    }

    def check( p: ResolutionProof, res: ( ResolutionProof, OccConnector[HOLFormula] ) ): ( ResolutionProof, OccConnector[HOLFormula] ) = {
      val ( newP, conn ) = res
      require( conn.lowerSequent == newP.conclusion )
      require( conn.upperSequent == p.conclusion )
      res
    }

    def doMap( p: ResolutionProof ): ( ResolutionProof, OccConnector[HOLFormula] ) = memo.getOrElseUpdate( p, doFactor( p, p match {
      case Input( sequent ) => f( sequent )
      case _: InitialClause => p -> OccConnector( p.conclusion )
      case Factor( p1, i1, i2 ) =>
        val ( q1, conn1 ) = doMap( p1 )
        ( for {
          j1 <- conn1 children i1 headOption;
          j2 <- conn1 children i2 headOption;
          res = if ( j1 < j2 ) Factor( q1, j1, j2 ) else Factor( q1, j2, j1 )
        } yield res -> ( res.occConnectors.head * conn1 * p.occConnectors.head.inv ) ) getOrElse { q1 -> conn1 * p.occConnectors.head.inv }
      case Subst( p1, subst ) =>
        val ( q1, conn1 ) = doMap( p1 )
        val res = Subst( q1, subst )
        res -> ( res.occConnectors.head * conn1 * p.occConnectors.head.inv )
      case Resolution( p1, i1, p2, i2 ) =>
        val ( q1, conn1 ) = doMap( p1 )
        val ( q2, conn2 ) = doMap( p2 )
        conn1.children( i1 ).headOption map { j1 =>
          conn2.children( i2 ).headOption map { j2 =>
            val res = Resolution( q1, j1, q2, j2 )
            res -> ( ( res.occConnectors( 0 ) * conn1 * p.occConnectors( 0 ).inv ) + ( res.occConnectors( 1 ) * conn2 * p.occConnectors( 1 ).inv ) )
          } getOrElse { q2 -> conn2 * p.occConnectors( 1 ).inv }
        } getOrElse { q1 -> conn1 * p.occConnectors( 0 ).inv }
      case Paramod( p1, i1, dir, p2, i2, con ) =>
        val ( q1, conn1 ) = doMap( p1 )
        val ( q2, conn2 ) = doMap( p2 )
        conn1.children( i1 ).headOption map { j1 =>
          conn2.children( i2 ).headOption map { j2 =>
            val res = Paramod( q1, j1, dir, q2, j2, con )
            res -> ( ( res.occConnectors( 0 ) * conn1 * p.occConnectors( 0 ).inv ) + ( res.occConnectors( 1 ) * conn2 * p.occConnectors( 1 ).inv ) )
          } getOrElse { q2 -> conn2 * p.occConnectors( 1 ).inv }
        } getOrElse { q1 -> conn1 * p.occConnectors( 0 ).inv }

        // FIXME: support for propositional part
    } ) )

    doMap( proof )._1
  }
}
