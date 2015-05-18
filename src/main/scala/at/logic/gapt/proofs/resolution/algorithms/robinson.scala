
package at.logic.gapt.proofs.resolution.algorithms

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.algorithms.{ CloneLKProof, applySubstitution => applySub }
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.resolution.FClause
import at.logic.gapt.proofs.resolution.robinson._

object RobinsonToLK extends at.logic.gapt.utils.logging.Logger {
  type mapT = scala.collection.mutable.Map[FClause, LKProof]

  //encapsulates a memo table s.t. subsequent runs of PCNF are not computed multiple times for the same c
  private class PCNFMemoTable( val endsequent: FSequent ) {
    val table: mapT = scala.collection.mutable.Map[FClause, LKProof]()
    var hits: Int = 0

    def getHits() = this.hits

    def getPCNF( c: FClause ) = {
      if ( !( table contains c ) ) {
        table.put( c, PCNF( endsequent, c ) )
      } else {
        hits = hits + 1
      }
      table( c )
    }
  }

  // if the proof can be obtained from the CNF(-s) then we compute an LKProof of |- s
  def apply( resproof: RobinsonResolutionProof, s: FSequent ): LKProof = {
    assert( resproof.root.toFSequent == FSequent( Nil, Nil ) )
    val memotable = new PCNFMemoTable( s )
    WeakeningContractionMacroRule( recConvert( resproof, s, scala.collection.mutable.Map[FClause, LKProof](), memotable.getPCNF ), s, strict = true )
  }

  // if the proof can be obtained from the CNF(-s) then we compute an LKProof of |- s
  def apply( resproof: RobinsonResolutionProof, s: FSequent, map: mapT ): LKProof = {
    val memotable = new PCNFMemoTable( s )
    WeakeningContractionMacroRule( recConvert( resproof, s, map, memotable.getPCNF ), s, strict = false )
  }

  def apply( resproof: RobinsonResolutionProof ): LKProof =
    recConvert( resproof, FSequent( List(), List() ), scala.collection.mutable.Map[FClause, LKProof](), x => Axiom( x.neg, x.pos ) )

  /**
   * This method converts a RobinsonResolutionProof resproof, which is assumed to have the empty clause
   * as end-clause, into an LKProof of a sequent s. To do this, the provided createAxiom method is assumed
   * to return, on input c, an LKProof with end-sequent "s' merge c", where s' is a sub-sequent of s.
   */
  def apply( resproof: RobinsonResolutionProof, s: FSequent, createAxiom: FClause => LKProof ): LKProof =
    WeakeningContractionMacroRule( recConvert( resproof, s, scala.collection.mutable.Map[FClause, LKProof](), createAxiom ), s, strict = true )

  // Enforce the inductive invariant by contracting superfluous material.
  private def contractDownTo( proof: LKProof, s: FSequent, c: FClause ) =
    {
      val es_l = proof.root.antecedent.map( _.formula ).toSet

      val p_l = es_l.foldLeft( proof )( ( p, f ) => {
        val max = s.antecedent.count( _ == f ) + c.neg.count( _ == f )
        ContractionLeftMacroRule( p, f, max )
      } )

      val es_r = proof.root.succedent.map( _.formula ).toSet
      es_r.foldLeft( p_l )( ( p, f ) => {
        val max = s.succedent.count( _ == f ) + c.pos.count( _ == f )
        ContractionRightMacroRule( p, f, max )
      } )
    }

  // Inductive invariant of this method:
  // returns an LKProof of "s' merge c", where s' is a sub-sequent of seq, and
  // c is the end-clause of proof.
  private def recConvert( proof: RobinsonResolutionProof, seq: FSequent, map: mapT, createAxiom: FClause => LKProof ): LKProof = {
    if ( map.contains( proof.root.toFClause ) ) {
      CloneLKProof( map( proof.root.toFClause ) )
    } else {
      val ret: LKProof = proof match {
        case InitialClause( cls ) => //
          createAxiom( cls.toFClause )
        case Factor( r, p, a, s ) => {
          // obtain the set of removed occurrences for each side
          val ( leftContracted, rightContracted ) =
            if ( a.size == 1 )
              if ( p.root.antecedent.contains( a( 0 ).head ) ) ( a( 0 ).tail, Nil )
              else ( Nil, a( 0 ).tail )
            else if ( a.size == 2 )
              if ( p.root.antecedent.contains( a( 0 ).head ) ) ( a( 0 ).tail, a( 1 ).tail )
              else ( a( 1 ).tail, a( 0 ).tail )
            else throw new Exception( "Unexpected number of auxiliary formulas!" )

          // obtain upper proof recursively and apply the current substitution to the resulted LK proof
          var res = applySub( recConvert( p, seq, map, createAxiom ), s )._1

          //trace("leftContracted: " + leftContracted)
          //trace("p.root: " + p.root)
          //trace("proof.root: " + proof.root)

          // create a contraction for each side, for each contracted formula with a._1 and a._2 (if exists)
          // note that sub must be applied to all formulas in the lk proof
          if ( !leftContracted.isEmpty ) {
            res = leftContracted.foldLeft( res )( ( p, fo ) => ContractionLeftRule(
              p, s( fo.formula ) ) )
          }
          if ( !rightContracted.isEmpty ) {
            res = rightContracted.foldLeft( res )( ( p, fo ) => ContractionRightRule(
              p, s( fo.formula ) ) )
          }
          res
        }
        // the construction of an LK proof makes sure we create a tree out of the agraph
        case Variant( r, p, s ) => applySub( recConvert( p, seq, map, createAxiom ), s )._1
        case Resolution( r, p1, p2, a1, a2, s ) => {
          val u1 = applySub( recConvert( p1, seq, map, createAxiom ), s )._1
          val u2 = applySub( recConvert( p2, seq, map, createAxiom ), s )._1
          //trace("resolution rule with conc: " + proof.root)
          //trace("p1: " + p1.root)
          //trace("p2: " + p2.root)
          //trace("u1: " + u1.root)
          //trace("u2: " + u2.root)

          val cut = CutRule( u1, u2, s( a1.formula.asInstanceOf[FOLFormula] ).asInstanceOf[FOLFormula] )
          contractDownTo( cut, seq, proof.root.toFClause )
        }
        case Paramodulation( r, p1, p2, a1, a2, _, s ) => {

          val u1 = applySub( recConvert( p1, seq, map, createAxiom ), s )._1
          val u2 = applySub( recConvert( p2, seq, map, createAxiom ), s )._1

          val FOLAtom( _, s0 :: _ ) = a1.formula
          val s1 = s( s0.asInstanceOf[FOLExpression] ).asInstanceOf[FOLTerm]

          // locate principal formula
          val lo = r.antecedent.find( _.parents.contains( a2 ) )
          val ro = r.succedent.find( _.parents.contains( a2 ) )
          // left rule
          val retProof = if ( ro == None ) {
            val lof = lo.get.formula.asInstanceOf[FOLFormula]
            // locate aux formulae
            val aux1 = u1.root.succedent.find( _.formula == s( a1.formula.asInstanceOf[FOLExpression] ).asInstanceOf[FOLFormula] ).get
            val aux2 = u2.root.antecedent.find( _.formula == s( a2.formula.asInstanceOf[FOLExpression] ).asInstanceOf[FOLFormula] ).get

            if ( isTrivial( aux1.formula, aux2.formula, lof ) ) {
              val newEndSequent = FSequent( u1.root.antecedent.map( _.formula ) ++ u2.root.antecedent.map( _.formula ),
                u1.root.succedent.filterNot( _ == aux1 ).map( _.formula ) ++ u2.root.succedent.map( _.formula ) )
              WeakeningMacroRule( u2, newEndSequent )
            } else
              EquationLeftRule( u1, u2, aux1, aux2, lof )
          } // right rule
          else {
            val rof = ro.get.formula.asInstanceOf[FOLFormula]
            // locate aux formulae

            val aux1 = u1.root.succedent.find( _.formula == s( a1.formula.asInstanceOf[FOLExpression] ).asInstanceOf[FOLFormula] ).get
            val aux2 = u2.root.succedent.find( _.formula == s( a2.formula.asInstanceOf[FOLExpression] ).asInstanceOf[FOLFormula] ).get

            if ( isTrivial( aux1.formula, aux2.formula, rof ) ) {
              val newEndSequent = FSequent( u1.root.antecedent.map( _.formula ) ++ u2.root.antecedent.map( _.formula ),
                u1.root.succedent.filterNot( _ == aux1 ).map( _.formula ) ++ u2.root.succedent.map( _.formula ) )
              WeakeningMacroRule( u2, newEndSequent )
            } else
              EquationRightRule( u1, u2, aux1, aux2, rof )
          }
          contractDownTo( retProof, seq, proof.root.toFClause )
        }
        // this case is applicable only if the proof is an instance of RobinsonProofWithInstance
        case Instance( root, p, s ) =>
          val rp = recConvert( p, seq, map, createAxiom )
          try {
            applySub( rp, s )._1
          } catch {
            case e @ LKQuantifierException( root, occf, term, formula, qvar ) =>
              throw new LKUnaryRuleCreationException( "Substitution errror: " + s + ":\n" + e.getMessage, rp, List( occf, formula ) )
          }
      }
      map( proof.root.toFClause ) = ret

      //trace( "proof.root: " + proof.root )
      //trace( "ret.root: " + ret.root )
      //trace( "ret.name: " + ret.name ) 
      //trace( "proof.name: " + proof.name ) 

      ret
    }
  }

  /**
   * Tests whether constructing an equality rule with a given equation, auxiliary formula and main formula would be superfluous.
   *
   * @param equation An Equation.
   * @param aux A Formula.
   * @param main A Formula.
   * @return True iff 1.) equation is of the form s = s 2,) main and aux coincide and 3.) s occurs in aux.
   */
  private def isTrivial( equation: Formula, aux: Formula, main: Formula ): Boolean = equation match {
    case Eq( s, t ) =>
      if ( s != t || aux != main )
        false
      else if ( aux.find( s ).isEmpty )
        throw new Exception( "Bad paramodulation: equation " + equation + ", aux formula " + aux + ", main formula" + main )
      else
        true
    case _ => throw new Exception( equation + " is not an equation." )
  }

}
