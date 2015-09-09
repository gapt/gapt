
package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.{ applySubstitution => applySub, _ }
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.resolution.robinson._
import at.logic.gapt.proofs.{ Sequent, HOLSequent, HOLClause, resolutionNew }
import at.logic.gapt.proofs.resolutionNew._

object RobinsonToLK extends at.logic.gapt.utils.logging.Logger {
  type mapT = scala.collection.mutable.Map[HOLClause, LKProof]

  //encapsulates a memo table s.t. subsequent runs of PCNF are not computed multiple times for the same c
  private class PCNFMemoTable( val endsequent: HOLSequent ) {
    val table: mapT = scala.collection.mutable.Map[HOLClause, LKProof]()
    var hits: Int = 0

    def getHits() = this.hits

    def getPCNF( c: HOLClause ) = {
      if ( !( table contains c ) ) {
        table.put( c, PCNF( endsequent, c ) )
      } else {
        hits = hits + 1
      }
      table( c )
    }
  }

  // if the proof can be obtained from the CNF(-s) then we compute an LKProof of |- s
  def apply( resproof: RobinsonResolutionProof, s: HOLSequent ): LKProof = apply( resOld2New( resproof ), s )
  def apply( resproof: resolutionNew.ResolutionProof, s: HOLSequent ): LKProof = {
    assert( resproof.conclusion.isEmpty )
    val memotable = new PCNFMemoTable( s )
    WeakeningContractionMacroRule( recConvert( resproof, s, scala.collection.mutable.Map[HOLClause, LKProof](), memotable.getPCNF ), s, strict = true )
  }

  // if the proof can be obtained from the CNF(-s) then we compute an LKProof of |- s
  def apply( resproof: RobinsonResolutionProof, s: HOLSequent, map: mapT ): LKProof = apply( resOld2New( resproof ), s, map )
  def apply( resproof: resolutionNew.ResolutionProof, s: HOLSequent, map: mapT ): LKProof = {
    val memotable = new PCNFMemoTable( s )
    WeakeningContractionMacroRule( recConvert( resproof, s, map, memotable.getPCNF ), s, strict = false )
  }

  def apply( resproof: RobinsonResolutionProof ): LKProof = apply( resOld2New( resproof ) )
  def apply( resproof: resolutionNew.ResolutionProof ): LKProof =
    recConvert( resproof, HOLSequent( List(), List() ), scala.collection.mutable.Map[HOLClause, LKProof](), x => Axiom( x.negative, x.positive ) )

  /**
   * This method converts a RobinsonResolutionProof resproof, which is assumed to have the empty clause
   * as end-clause, into an LKProof of a sequent s. To do this, the provided createAxiom method is assumed
   * to return, on input c, an LKProof with end-sequent "s' merge c", where s' is a sub-sequent of s.
   */
  def apply( resproof: RobinsonResolutionProof, s: HOLSequent, createAxiom: HOLClause => LKProof ): LKProof = apply( resOld2New( resproof ), s, createAxiom )
  def apply( resproof: resolutionNew.ResolutionProof, s: HOLSequent, createAxiom: HOLClause => LKProof ): LKProof =
    WeakeningContractionMacroRule( recConvert( resproof, s, scala.collection.mutable.Map[HOLClause, LKProof](), createAxiom ), s, strict = true )

  // Enforce the inductive invariant by contracting superfluous material.
  private def contractDownTo( proof: LKProof, s: HOLSequent, c: HOLClause ) =
    {
      val es_l = proof.root.antecedent.map( _.formula ).toSet

      val p_l = es_l.foldLeft( proof )( ( p, f ) => {
        val max = s.antecedent.count( _ == f ) + c.negative.count( _ == f )
        ContractionLeftMacroRule( p, f, max )
      } )

      val es_r = proof.root.succedent.map( _.formula ).toSet
      es_r.foldLeft( p_l )( ( p, f ) => {
        val max = s.succedent.count( _ == f ) + c.positive.count( _ == f )
        ContractionRightMacroRule( p, f, max )
      } )
    }

  // Inductive invariant of this method:
  // returns an LKProof of "s' merge c", where s' is a sub-sequent of seq, and
  // c is the end-clause of proof.
  private def recConvert( proof: resolutionNew.ResolutionProof, seq: HOLSequent, map: mapT, createAxiom: HOLClause => LKProof ): LKProof = {
    if ( map.contains( proof.conclusion ) ) {
      CloneLKProof( map( proof.conclusion ) )
    } else {
      val ret: LKProof = proof match {
        case resolutionNew.TautologyClause( atom )   => Axiom( atom )
        case resolutionNew.ReflexivityClause( term ) => Axiom( Sequent() :+ Eq( term, term ) )
        case resolutionNew.InputClause( cls )        => createAxiom( cls )
        case resolutionNew.Factor( p, idx1, idx2 ) => {
          val res = recConvert( p, seq, map, createAxiom )

          if ( idx1.isAnt )
            ContractionLeftRule( res, p.conclusion( idx1 ) )
          else
            ContractionRightRule( res, p.conclusion( idx1 ) )
        }
        case resolutionNew.Instance( p, s ) => applySub( recConvert( p, seq, map, createAxiom ), s )._1
        case resolutionNew.Resolution( p1, idx1, p2, idx2 ) => {
          val u1 = recConvert( p1, seq, map, createAxiom )
          val u2 = recConvert( p2, seq, map, createAxiom )
          val cut = CutRule( u1, u2, p1.conclusion( idx1 ) )
          contractDownTo( cut, seq, proof.conclusion )
        }
        case resolutionNew.Paramodulation( p1, eq, p2, lit, poss, dir ) => {
          val u1 = recConvert( p1, seq, map, createAxiom )
          val u2 = recConvert( p2, seq, map, createAxiom )
          val Some( eqOcc ) = u1.root.succedent.find( _.formula == p1.conclusion( eq ) )
          val res = if ( lit.isAnt )
            EquationLeftMacroRule( u1, u2, eqOcc, u2.root.antecedent.find( _.formula == p2.conclusion( lit ) ).get, proof.mainFormulas.head )
          else
            EquationRightMacroRule( u1, u2, eqOcc, u2.root.succedent.find( _.formula == p2.conclusion( lit ) ).get, proof.mainFormulas.head )
          contractDownTo( res, seq, proof.conclusion )
        }
      }
      map( proof.conclusion ) = ret

      ret
    }
  }

}
