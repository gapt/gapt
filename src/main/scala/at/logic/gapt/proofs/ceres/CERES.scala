package at.logic.gapt.proofs.ceres

import at.logic.gapt.formats.llkNew.LLKExporter
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.proofs.lkOld.{ subsumedClausesRemoval, deleteTautologies }
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.resolution.{ ResolutionProof, RobinsonToLK }
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.expr._

import at.logic.gapt.provers.prover9.Prover9

/**
 * This implementation of the CERES method does the proof reconstruction via Robinson2LK.
 */
object CERES extends CERES {
  def skipNothing( f: HOLFormula ): Boolean = true

  /**
   * True if the formula is not an equation. Intended use: predicate argument of CERES.
   * In case the only cuts on equations come from a translation of binary equation rules to unary ones,
   * this should provide the same clause sets and projections as the binary rules.
   */
  def skipEquations( f: HOLFormula ): Boolean = f match { case Eq( _, _ ) => false; case _ => true }

  /**
   * True if the formula is propositional and does not contain free variables other than type i.
   * Intended use: predicate argument of CERES.
   * In case the only cuts on equations come from a translation of binary equation rules to unary ones,
   * this should provide the same clause sets and projections as the binary rules.
   */
  def skipPropositional( f: HOLFormula ): Boolean = f match {
    case Top()    => false
    case Bottom() => false
    case HOLAtom( HOLAtomConst( _, _ ), args ) =>
      args.flatMap( freeVariables( _ ) ).exists( _.exptype != Ti )
    case Neg( f )    => skipPropositional( f )
    case And( l, r ) => skipPropositional( l ) || skipPropositional( r )
    case Or( l, r )  => skipPropositional( l ) || skipPropositional( r )
    case Imp( l, r ) => skipPropositional( l ) || skipPropositional( r )
    case _           => true
  }

}

class CERES {
  /**
   * Applies the CERES method to a first order proof with equality. Internally this is handled by the RobinsoToLK method.
   * @param p a first-order LKProof (structural rules, cut, logical rules, equational rules but no definitions, schema,higher order)
   *          also each formula must be a FOLFormula, since the prover9 interface returns proofs from the FOL layer
   * @return an LK Proof in Atomic Cut Normal Form (ACNF) i.e. without quantified cuts
   */
  def apply( p: LKProof ): LKProof = apply( p, CERES.skipNothing )

  /**
   * Applies the CERES method to a first order proof with equality. Internally this is handled by the RobinsoToLK method.
   * @param p a first-order LKProof without strong quantifiers in the end-sequent
   *          (i.e. structural rules, cut, logical rules, equational rules but no definitions, schema,higher order)
   * @param pred a predicate to specify which cut formulas to eliminate
   *             (e.g. x => containsQuantifiers(x) to keep propositional cuts intact)
   * @return an LK Proof in Atomic Cut Normal Form (ACNF) i.e. without quantified cuts
   */
  def apply( p: LKProof, pred: HOLFormula => Boolean ): LKProof = {
    val es = p.endSequent
    val cs = CharacteristicClauseSet( StructCreators.extract( p, pred ) )
    val proj = Projections( p, pred ) + CERES.refProjection( es )
    /*
    val cs_ = cs.asInstanceOf[Set[HOLSequent]]
    var count = 0;
    for ( p <- proj ) {
      if ( !cs_.contains( p.endSequent diff es ) ) {
        println( LLKExporter.generateProof( p, "Proj" + count, true ) )
        println()
        count = count + 1
      }
    }*/

    val tapecl = subsumedClausesRemoval( deleteTautologies( cs ).toList )
    //println( TPTPFOLExporter.tptp_problem( tapecl.toList ) )
    //println( "original css size: " + cs.size )
    //println( "after subsumption:" + tapecl.size )

    Prover9.getRobinsonProof( tapecl ) match {
      case None => throw new Exception( "Prover9 could not refute the characteristic clause set!" )
      case Some( rp ) =>
        //println( s"refutation:\n$rp" )
        apply( es, proj, rp )
    }
  }

  /**
   * Applies the CERES method to a first order proof with equality. Internally this is handled by the RobinsoToLK method.
   * @param endsequent The end-sequent of the original proof
   * @param proj The projections of the original proof
   * @param rp A resolution refutation
   * @return an LK Proof in Atomic Cut Normal Form (ACNF) i.e. without quantified cuts
   */
  def apply( endsequent: HOLSequent, proj: Set[LKProof], rp: ResolutionProof ) = {
    RobinsonToLK( rp, endsequent, fc => CERES.findMatchingProjection( endsequent, proj + CERES.refProjection( endsequent ) )( fc ) )
  }

  def findMatchingProjection( endsequent: HOLSequent, projections: Set[LKProof] )( axfs: HOLSequent ): LKProof = {
    val nLine = sys.props( "line.separator" )
    //println( s"end-sequent: $endsequent" )
    //println( s"looking for projection to $axfs" )
    projections.find( x => StillmanSubsumptionAlgorithmHOL.subsumes( x.endSequent diff endsequent, axfs ) ) match {
      case None => throw new Exception( "Could not find a projection to " + axfs + " in " +
        projections.map( _.endSequent.diff( endsequent ) ).mkString( "{" + nLine, ";" + nLine, nLine + "}" ) )
      case Some( proj ) =>
        val Some( sub ) = StillmanSubsumptionAlgorithmHOL.subsumes_by( proj.endSequent diff endsequent, axfs )
        val subproj = applySubstitution( sub )( proj )
        val duplicates = ( subproj.endSequent diff endsequent ) diff axfs
        //println( s"duplicates: $duplicates" )
        //println( subproj.endSequent )
        val cleft = duplicates.antecedent.foldLeft( subproj )( ( p, el ) => {
          require(
            p.endSequent.antecedent.filter( _ == el ).size >= 2,
            s"Could not contract formula $el in proof $p. Can not match projection $subproj to clause $axfs."
          )
          ContractionLeftRule( p, el )
        } )
        val cright = duplicates.succedent.foldLeft( cleft )( ( p, el ) => {
          require(
            p.endSequent.succedent.filter( _ == el ).size >= 2,
            s"Could not contract formula $el in proof $p. Can not match projection $subproj to clause $axfs."
          )
          ContractionRightRule( p, el )

        } )
        require(
          ( cright.endSequent diff endsequent ).multiSetEquals( axfs ),
          "Instance of projection with end-sequent " + subproj.endSequent + " is not equal to "
            + axfs + " x " + endsequent
        )
        subproj
    }
  }

  def refProjection( es: HOLSequent ): LKProof = {
    require( es.formulas.nonEmpty, "Can not project reflexivity to an empty end-sequent!" )
    val x = Var( StringSymbol( "x" ), Ti ).asInstanceOf[Var]
    val axiomseq = HOLSequent( Nil, List( Eq( x, x ) ) )
    //addWeakenings(Axiom(axiomseq.antecedent, axiomseq.succedent), axiomseq compose es)
    WeakeningMacroRule( Axiom( axiomseq.antecedent, axiomseq.succedent ), axiomseq ++ es )
  }

}
