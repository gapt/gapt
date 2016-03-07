package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr.HOLAtom
import at.logic.gapt.proofs.{ OccConnector, HOLClause, SequentIndex }
import scala.collection.mutable

object mapInputClauses {
  def guessConn( oldConcl: HOLClause, newConcl: HOLClause ): OccConnector[HOLAtom] = {
    val alreadyUsedOldIndices = mutable.Set[SequentIndex]()
    OccConnector( newConcl, oldConcl, newConcl.zipWithIndex.map {
      case ( atom, newIdx ) =>
        val oldIdx = oldConcl.indicesWhere( _ == atom ).
          filterNot( alreadyUsedOldIndices.contains ).
          filter( newIdx.sameSideAs ).
          head
        alreadyUsedOldIndices += oldIdx
        Seq( oldIdx )
    } )
  }

  def apply( proof: ResolutionProof, factorEarly: Boolean = false )( f: HOLClause => ResolutionProof ): ResolutionProof =
    withOccConn( proof ) { clause =>
      val q = f( clause )
      q -> guessConn( clause, q.conclusion )
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
      case Paramodulation( p1, i1, p2, i2, pos, dir ) =>
        val ( q1, conn1 ) = doMap( p1 )
        val ( q2, conn2 ) = doMap( p2 )
        conn1.children( i1 ).headOption map { j1 =>
          conn2.children( i2 ).headOption map { j2 =>
            val res = Paramodulation( q1, j1, q2, j2, pos, dir )
            res -> ( ( res.occConnectors( 0 ) * conn1 * p.occConnectors( 0 ).inv ) + ( res.occConnectors( 1 ) * conn2 * p.occConnectors( 1 ).inv ) )
          } getOrElse { q2 -> conn2 * p.occConnectors( 1 ).inv }
        } getOrElse { q1 -> conn1 * p.occConnectors( 0 ).inv }
    } ) )

    doMap( proof )._1
  }
}
