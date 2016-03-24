package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr.HOLAtom
import at.logic.gapt.proofs.{ OccConnector, HOLClause, SequentIndex }
import scala.collection.mutable

object mapInputClauses {

  def apply( proof: ResolutionProof, factorEarly: Boolean = false )( f: HOLClause => ResolutionProof ): ResolutionProof =
    withOccConn( proof ) { clause =>
      val q = f( clause )
      q -> OccConnector.guessInjection( clause, q.conclusion )
    }

  def withOccConn( proof: ResolutionProof, factorEverything: Boolean = false )( f: HOLClause => ( ResolutionProof, OccConnector[HOLAtom] ) ): ResolutionProof = {
    val memo = mutable.Map[ResolutionProof, ( ResolutionProof, OccConnector[HOLAtom] )]()

    def doFactor( p: ResolutionProof, res: ( ResolutionProof, OccConnector[HOLAtom] ) ): ( ResolutionProof, OccConnector[HOLAtom] ) = {
      val ( newP, conn ) = res
      check( p, if ( factorEverything ) {
        val ( facP, facConn ) = Factor( newP )
        val facConn_ = facConn.copy( parentsSequent = facConn.parentsSequent.map { _ take 1 } )
        ( facP, facConn_ * conn )
      } else {
        res
      } )
    }

    def check( p: ResolutionProof, res: ( ResolutionProof, OccConnector[HOLAtom] ) ): ( ResolutionProof, OccConnector[HOLAtom] ) = {
      val ( newP, conn ) = res
      require( conn.lowerSequent == newP.conclusion )
      require( conn.upperSequent == p.conclusion )
      res
    }

    def doMap( p: ResolutionProof ): ( ResolutionProof, OccConnector[HOLAtom] ) = doFactor( p, memo.getOrElseUpdate( p, p match {
      case TautologyClause( _ ) | ReflexivityClause( _ ) => p -> OccConnector( p.conclusion )
      case InputClause( clause )                         => f( clause )
      case Factor( p1, i1, i2 ) =>
        val ( q1, conn1 ) = doMap( p1 )
        ( for ( j1 <- conn1 children i1 headOption; j2 <- conn1 children i2 headOption; ( res, resConn ) <- Some( Factor( q1, List( j1, j2 ) ) ) )
          yield res -> ( resConn * conn1 * p.occConnectors.head.inv ) ) getOrElse { q1 -> conn1 * p.occConnectors.head.inv }
      case Instance( p1, subst ) =>
        val ( q1, conn1 ) = doMap( p1 )
        val res = Instance( q1, subst )
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
      case Paramodulation( p1, i1, p2, i2, con, dir ) =>
        val ( q1, conn1 ) = doMap( p1 )
        val ( q2, conn2 ) = doMap( p2 )
        conn1.children( i1 ).headOption map { j1 =>
          conn2.children( i2 ).headOption map { j2 =>
            val res = Paramodulation( q1, j1, q2, j2, con, dir )
            res -> ( ( res.occConnectors( 0 ) * conn1 * p.occConnectors( 0 ).inv ) + ( res.occConnectors( 1 ) * conn2 * p.occConnectors( 1 ).inv ) )
          } getOrElse { q2 -> conn2 * p.occConnectors( 1 ).inv }
        } getOrElse { q1 -> conn1 * p.occConnectors( 0 ).inv }
      case p @ Splitting( p0, c1, c2, p1, p2 ) =>
        val ( q0, _ ) = doMap( p0 )
        val q1 = mapInputClauses.withOccConn( p1, factorEverything ) { cls =>
          if ( p.addInputClauses1 contains cls ) InputClause( cls ) -> OccConnector( cls ) else f( cls )
        }
        val q2 = mapInputClauses.withOccConn( p2, factorEverything ) { cls =>
          if ( p.addInputClauses2 contains cls ) InputClause( cls ) -> OccConnector( cls ) else f( cls )
        }
        Splitting( q0, c1, c2, q1, q2 ) -> OccConnector( HOLClause() )
    } ) )

    doMap( proof )._1
  }
}
