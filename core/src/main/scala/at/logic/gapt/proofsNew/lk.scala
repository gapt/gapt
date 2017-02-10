package at.logic.gapt.proofsNew
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ HOLSequent, Sequent, SequentIndex }

package object lk {
  type LKProof = SequentProof[LKInference]

  implicit object lKProofSubstitutable extends ClosedUnderSub[LKProof] {
    override def applySubstitution( sub: Substitution, arg: LKProof ): LKProof =
      arg match {
        case DagProof( TopAxiom )                => DagProof[HOLSequent, LKInference]( TopAxiom )
        case DagProof( LogicalAxiom( formula ) ) => DagProof[HOLSequent, LKInference]( LogicalAxiom( sub( formula ) ) )
        case DagProof( NegLeft( _, aux ), subProof ) =>
          LKProofBuilder.c( applySubstitution( sub, subProof ) ).u( NegLeft( _, aux ) ).qed
        case DagProof( NegRight( _, aux ), subProof ) =>
          LKProofBuilder.c( applySubstitution( sub, subProof ) ).u( NegRight( _, aux ) ).qed
        case DagProof( OrLeft( _, aux1, _, aux2 ), subProof1, subProof2 ) =>
          LKProofBuilder.
            c( applySubstitution( sub, subProof1 ) ).
            c( applySubstitution( sub, subProof2 ) ).
            b( OrLeft( _, aux1, _, aux2 ) ).qed
        case DagProof( OrRight( _, aux1, aux2 ), subProof ) =>
          LKProofBuilder.
            c( applySubstitution( sub, subProof ) ).
            u( OrRight( _, aux1, aux2 ) ).qed
      }
  }
}

package lk {

  trait LKInference extends SequentInference

  object LKProofBuilder extends DagProofBuilder[HOLSequent, LKInference]

  trait InitialSequent extends LKInference {
    override def premises = Vector()
    override def auxIndices = Vector()
    override def occConnectors = Vector()
    override def mainIndices = conclusion.indices
  }

  case class LogicalAxiom( formula: HOLFormula ) extends InitialSequent {
    override def conclusion: HOLSequent = formula +: Sequent() :+ formula
  }

  case object TopAxiom extends InitialSequent {
    override def conclusion: HOLSequent = Sequent() :+ Top()
  }

  trait UnaryLKInf extends LKInference with ContextInf {
    def premise: HOLSequent
    override def premises = Vector( premise )
    def occConnector = occConnectors.head
  }

  trait Contraction extends UnaryLKInf {
    def aux1: SequentIndex
    def aux2: SequentIndex
    require( premise( aux1 ) == premise( aux2 ) )
    val mainFormula = premise( aux1 )
    override def auxIndices = Seq( Seq( aux1, aux2 ) )
  }

  case class ContractionLeft( premise: HOLSequent, aux1: SequentIndex, aux2: SequentIndex ) extends Contraction {
    require( aux1.isAnt )
    require( aux2.isAnt )
    override def mainFormulaSequent = mainFormula +: Sequent()
  }

  case class ContractionRight( premise: HOLSequent, aux1: SequentIndex, aux2: SequentIndex ) extends Contraction {
    require( aux1.isSuc )
    require( aux2.isSuc )
    override def mainFormulaSequent = Sequent() :+ mainFormula
  }

  case class NegLeft( premise: HOLSequent, aux: SequentIndex ) extends UnaryLKInf {
    require( aux.isSuc )
    val mainFormula = -premise( aux )
    override def auxIndices = Seq( Seq( aux ) )
    override def mainFormulaSequent = mainFormula +: Sequent()
  }

  case class NegRight( premise: HOLSequent, aux: SequentIndex ) extends UnaryLKInf {
    require( aux.isAnt )
    val mainFormula = -premise( aux )
    override def auxIndices = Seq( Seq( aux ) )
    override def mainFormulaSequent = Sequent() :+ mainFormula
  }

  trait BinaryLKInf extends LKInference with ContextInf {
    def leftPremise: HOLSequent
    def rightPremise: HOLSequent
    override def premises = Vector( leftPremise, rightPremise )
  }

  case class OrLeft( leftPremise: HOLSequent, aux1: SequentIndex, rightPremise: HOLSequent, aux2: SequentIndex ) extends BinaryLKInf {
    require( aux1.isAnt )
    require( aux2.isAnt )
    val mainFormula = leftPremise( aux1 ) | rightPremise( aux2 )
    override def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )
    override def mainFormulaSequent = mainFormula +: Sequent()
  }

  case class OrRight( premise: HOLSequent, aux1: SequentIndex, aux2: SequentIndex ) extends UnaryLKInf {
    require( aux1.isSuc )
    require( aux2.isSuc )
    val mainFormula = premise( aux1 ) | premise( aux2 )
    override def auxIndices = Seq( Seq( aux1, aux2 ) )
    override def mainFormulaSequent = Sequent() :+ mainFormula
  }
}