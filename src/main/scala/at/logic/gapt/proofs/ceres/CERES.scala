package at.logic.gapt.proofs.ceres

import at.logic.gapt.proofs.lkNew.{ lkOld2New, lkNew2Old }
import at.logic.gapt.proofs.resolution.{ RobinsonToLK, ResolutionProof }
import at.logic.gapt.proofs.{ HOLSequent, HOLClause }
import at.logic.gapt.proofs.lk.applySubstitution
import at.logic.gapt.expr._

import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.resolutionOld.RichOccClause
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.proofs.ceres.clauseSets.StandardClauseSet

import at.logic.gapt.proofs.ceres.projections.Projections
import at.logic.gapt.proofs.ceres.struct.StructCreators

/**
 * Two implementations of first-order CERES, one (CERES) grounding the proof before the transformation, the other (CERESR2LK)
 * performing the task inline in the Robinson2LK method.
 */
object CERESR2LK extends CERESR2LK
class CERESR2LK {
  /**
   * Applies the CERES method to a first order proof with equality. Internally this is handled by the RobinsoToLK method.
   * @param p a first-order LKProof (structural rules, cut, logical rules, equational rules but no definitions, schema,higher order)
   *          also each formula must be a FOLFormula, since the prover9 interface returns proofs from the FOL layer
   * @return an LK Proof in Atomic Cut Normal Form (ACNF) i.e. without quantified cuts
   */
  def apply( p: LKProof ): LKProof = apply( p, x => true )

  /**
   * Applies the CERES method to a first order proof with equality. Internally this is handled by the RobinsoToLK method.
   * @param p a first-order LKProof (structural rules, cut, logical rules, equational rules but no definitions, schema,higher order)
   *          also each formula must be a FOLFormula, since the prover9 interface returns proofs from the FOL layer
   * @param pred a predicate to specify which cut formulas to eliminate
   *             (e.g. x => containsQuantifiers(x) to keep propositional cuts intact)
   * @return an LK Proof in Atomic Cut Normal Form (ACNF) i.e. without quantified cuts
   */
  def apply( p: LKProof, pred: HOLFormula => Boolean ): LKProof = {
    val es = p.root.toHOLSequent
    val proj = Projections( p, pred ) + CERES.refProjection( es )

    val tapecl = StandardClauseSet.transformStructToClauseSet( StructCreators.extract( p, pred ) )

    Prover9.getRobinsonProof( tapecl.map( _.toHOLClause ) ) match {
      case None => throw new Exception( "Prover9 could not refute the characteristic clause set!" )
      case Some( rp ) =>
        apply( es, proj, rp )
    }
  }

  /**
   * Applies the CERES method to a first order proof with equality. Internally this is handled by the RobinsoToLK method.
   * Please note that the formulas in the different input proofs need to come from the same layer (i.e. both FOL or both HOL)
   * @param endsequent The end-sequent of the original proof
   * @param proj The projections of the original proof
   * @param rp A resolution refutation
   * @return an LK Proof in Atomic Cut Normal Form (ACNF) i.e. without quantified cuts
   */
  def apply( endsequent: HOLSequent, proj: Set[LKProof], rp: ResolutionProof ) = {
    lkNew2Old( RobinsonToLK( rp, endsequent, fc => lkOld2New( CERES.findMatchingProjection( endsequent, proj + CERES.refProjection( endsequent ) )( fc ) ) ) )
  }

}

object CERES extends CERES
class CERES {
  /**
   * Applies the CERES method to a first order proof with equality. Internally this is handled by the RobinsoToLK method.
   * @param p a first-order LKProof (structural rules, cut, logical rules, equational rules but no definitions, schema,higher order)
   *          also each formula must be a FOLFormula, since the prover9 interface returns proofs from the FOL layer
   * @return an LK Proof in Atomic Cut Normal Form (ACNF) i.e. without quantified cuts
   */
  def apply( p: LKProof ): LKProof = apply( p, x => true )

  /**
   * Applies the CERES method to a first order proof with equality. Internally this is handled by the RobinsoToLK method.
   * @param p a first-order LKProof (structural rules, cut, logical rules, equational rules but no definitions, schema,higher order)
   *          also each formula must be a FOLFormula, since the prover9 interface returns proofs from the FOL layer
   * @param pred a predicate to specify which cut formulas to eliminate
   *             (e.g. x => containsQuantifiers(x) to keep propositional cuts intact)
   * @return an LK Proof in Atomic Cut Normal Form (ACNF) i.e. without quantified cuts
   */
  def apply( p: LKProof, pred: HOLFormula => Boolean ): LKProof = {
    val es = p.root.toHOLSequent
    val proj = Projections( p, pred )

    val tapecl = StandardClauseSet.transformStructToClauseSet( StructCreators.extract( p, pred ) )
    val refl = refProjection( es )
    Prover9.getRobinsonProof( tapecl.map( _.toHOLClause ) ) match {
      case None => throw new Exception( "Prover9 could not refute the characteristic clause set!" )
      case Some( rp ) =>
        val lkproof = RobinsonToLK( rp )
        apply( es, proj + refl, lkNew2Old( lkproof ) )
    }
  }

  def apply( lkproof: LKProof, refutation: LKProof, pred: HOLFormula => Boolean ): LKProof = {
    CERES( lkproof.root.toHOLSequent, Projections( lkproof, pred ) + refProjection( lkproof.root.toHOLSequent ), refutation )
  }

  /**
   * Applies the CERES method to a first order proof with equality.
   * @param endsequent The end-sequent of the original proof
   * @param projections The projections of the original proof
   * @param refutation A resolution refutation converted to LK (for instance with Robinson2LK)
   * @return an LK Proof in Atomic Cut Normal Form (ACNF) i.e. without quantified cuts
   */
  def apply( endsequent: HOLSequent, projections: Set[LKProof], refutation: LKProof ): LKProof = refutation match {
    case Axiom( OccSequent( Seq( a ), Seq( a_ ) ) ) if a.formula == a_.formula =>
      CloneLKProof( refutation )

    case Axiom( root ) =>
      findMatchingProjection( endsequent, projections )( root.toHOLSequent )

    case CutRule( p1, p2, root, aux1, aux2 ) =>
      val rp1 = CERES( endsequent, projections, p1 )
      val rp2 = CERES( endsequent, projections, p2 )
      contractEndsequent( CutRule( rp1, rp2, aux1.formula ), endsequent )

    case ContractionLeftRule( p1, root, aux1, aux2, _ ) =>
      val rp1 = CERES( endsequent, projections, p1 )
      ContractionLeftRule( rp1, aux1.formula )
    case ContractionRightRule( p1, root, aux1, aux2, _ ) =>
      val rp1 = CERES( endsequent, projections, p1 )
      ContractionRightRule( rp1, aux1.formula )

    case WeakeningLeftRule( p1, root, aux1 ) =>
      val rp1 = CERES( endsequent, projections, p1 )
      WeakeningLeftRule( rp1, aux1.formula )
    case WeakeningRightRule( p1, root, aux1 ) =>
      val rp1 = CERES( endsequent, projections, p1 )
      WeakeningRightRule( rp1, aux1.formula )

    case EquationLeft1Rule( p1, p2, root, aux1, aux2, _, main ) =>
      val rp1 = CERES( endsequent, projections, p1 )
      val rp2 = CERES( endsequent, projections, p2 )
      contractEndsequent( EquationLeftRule( rp1, rp2, aux1.formula, aux2.formula, main.formula ), endsequent )
    case EquationLeft2Rule( p1, p2, root, aux1, aux2, _, main ) =>
      val rp1 = CERES( endsequent, projections, p1 )
      val rp2 = CERES( endsequent, projections, p2 )
      contractEndsequent( EquationLeftRule( rp1, rp2, aux1.formula, aux2.formula, main.formula ), endsequent )
    case EquationRight1Rule( p1, p2, root, aux1, aux2, _, main ) =>
      val rp1 = CERES( endsequent, projections, p1 )
      val rp2 = CERES( endsequent, projections, p2 )
      contractEndsequent( EquationRightRule( rp1, rp2, aux1.formula, aux2.formula, main.formula ), endsequent )
    case EquationRight2Rule( p1, p2, root, aux1, aux2, _, main ) =>
      val rp1 = CERES( endsequent, projections, p1 )
      val rp2 = CERES( endsequent, projections, p2 )
      contractEndsequent( EquationRightRule( rp1, rp2, aux1.formula, aux2.formula, main.formula ), endsequent )

    case _ =>
      throw new Exception( "Refutation is expected to contain only cut, contraction and equality rules!" )

  }

  def findMatchingProjection( endsequent: HOLSequent, projections: Set[LKProof] ): ( HOLSequent => LKProof ) = {
    val nLine = sys.props( "line.separator" )

    ( axfs: HOLSequent ) =>
      {
        projections.find( x => StillmanSubsumptionAlgorithmHOL.subsumes( x.root.toHOLSequent diff endsequent, axfs ) ) match {
          case None => throw new Exception( "Could not find a projection to " + axfs + " in " +
            projections.map( _.root ).mkString( "{" + nLine, "," + nLine, nLine + "}" ) )
          case Some( proj ) =>
            val Some( sub ) = StillmanSubsumptionAlgorithmHOL.subsumes_by( proj.root.toHOLSequent diff endsequent, axfs )
            val ( subproj, _ ) = applySubstitution( proj, sub )
            require(
              ( subproj.root.toHOLSequent diff endsequent ).multiSetEquals( axfs ),
              "Instance of projection with end-sequent " + subproj.root + " is not equal to " + axfs + " x " + endsequent
            )
            subproj
        }
      }
  }

  def refProjection( es: HOLSequent ): LKProof = {
    require( es.formulas.nonEmpty, "Can not project reflexivity to an empty end-sequent!" )
    val x = Var( StringSymbol( "x" ), Ti ).asInstanceOf[Var]
    val axiomseq = HOLSequent( Nil, List( Eq( x, x ) ) )
    //addWeakenings(Axiom(axiomseq.antecedent, axiomseq.succedent), axiomseq compose es)
    WeakeningMacroRule( Axiom( axiomseq.antecedent, axiomseq.succedent ), axiomseq ++ es )
  }

  def contractEndsequent( p: LKProof, es: HOLSequent ) = ContractionMacroRule( p, es, strict = false )

}

