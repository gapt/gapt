package gapt.proofs.lk

import gapt.expr.formula.Formula
import gapt.proofs.Ant
import gapt.proofs.HOLSequent
import gapt.proofs.SequentIndex
import gapt.proofs.SequentProof
import gapt.proofs.Suc

import scala.collection.mutable

abstract class LKProof extends SequentProof[Formula, LKProof] {

  protected def LKRuleCreationException( message: String ): LKRuleCreationException =
    new LKRuleCreationException( longName, message )

  /**
   * The end-sequent of the rule.
   */
  final def endSequent: HOLSequent = conclusion

  /**
   * Checks whether indices are in the right place and premise is defined at all of them.
   *
   * @param premise The sequent to be checked.
   * @param antecedentIndices Indices that should be in the antecedent.
   * @param succedentIndices Indices that should be in the succedent.
   */
  protected final def validateIndices(
    premise:           HOLSequent,
    antecedentIndices: Seq[SequentIndex], succedentIndices: Seq[SequentIndex] ): Unit = {
    val antSet = mutable.HashSet[SequentIndex]()
    val sucSet = mutable.HashSet[SequentIndex]()

    for ( i <- antecedentIndices ) i match {
      case Ant( _ ) =>

        if ( !premise.isDefinedAt( i ) )
          throw LKRuleCreationException( s"Sequent $premise is not defined at index $i." )

        if ( antSet contains i )
          throw LKRuleCreationException( s"Duplicate index $i for sequent $premise." )

        antSet += i

      case Suc( _ ) => throw LKRuleCreationException( s"Index $i should be in the antecedent." )
    }

    for ( i <- succedentIndices ) i match {
      case Suc( _ ) =>

        if ( !premise.isDefinedAt( i ) )
          throw LKRuleCreationException( s"Sequent $premise is not defined at index $i." )

        if ( sucSet contains i )
          throw LKRuleCreationException( s"Duplicate index $i for sequent $premise." )

        sucSet += i

      case Ant( _ ) => throw LKRuleCreationException( s"Index $i should be in the succedent." )
    }
  }
}
