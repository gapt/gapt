package gapt.proofs.lk.rules

import gapt.expr.Formula
import gapt.proofs.Ant
import gapt.proofs.HOLSequent
import gapt.proofs.IndexOrFormula
import gapt.proofs.IndexOrFormula.IsFormula
import gapt.proofs.IndexOrFormula.IsIndex
import gapt.proofs.Suc
import gapt.proofs.lk.LKRuleCreationException

/**
 * Class for reducing boilerplate code in LK companion objects.
 *
 * @param longName The long name of the rule.
 */
class ConvenienceConstructor( val longName: String ) {
  /**
   * Create an LKRuleCreationException with a message starting
   * with "Cannot create longName: ..."
   *
   * @param text The rest of the message.
   * @return
   */
  protected def LKRuleCreationException( text: String ): LKRuleCreationException =
    new LKRuleCreationException( longName, text )

  def findIndicesOrFormulasInPremise( premise: HOLSequent )(
    antIndicesFormulas: Seq[IndexOrFormula],
    sucIndicesFormulas: Seq[IndexOrFormula] ): ( Seq[Formula], Seq[Int], Seq[Formula], Seq[Int] ) = {
    val antReservedIndices = ( scala.collection.mutable.HashSet.empty[Int] /: antIndicesFormulas ) { ( acc, e ) =>
      e match {
        case IsIndex( Ant( i ) ) => acc + i
        case IsIndex( i: Suc )   => throw LKRuleCreationException( s"Index $i should be in the antecedent." )
        case IsFormula( _ )      => acc
      }
    }

    val ant = for ( e <- antIndicesFormulas ) yield {
      e match {
        case IsIndex( idx @ Ant( i ) ) =>
          antReservedIndices += i
          val f = premise( idx )

          ( f, i )

        case IsFormula( f ) =>
          var i = premise.antecedent.indexOf( f )

          while ( antReservedIndices contains i )
            i = premise.antecedent.indexOf( f, i + 1 )

          if ( i != -1 )
            antReservedIndices += i

          ( f, i )

        case IsIndex( i: Suc ) => throw LKRuleCreationException( s"Index $i should be in the antecedent." )
      }
    }

    val sucReservedIndices = ( scala.collection.mutable.HashSet.empty[Int] /: sucIndicesFormulas ) { ( acc, e ) =>
      e match {
        case IsIndex( Suc( i ) ) => acc + i
        case IsIndex( i: Ant )   => throw LKRuleCreationException( s"Index $i should be in the succedent." )
        case IsFormula( _ )      => acc
      }
    }

    val suc = for ( e <- sucIndicesFormulas ) yield {
      e match {
        case IsIndex( Suc( i: Int ) ) =>
          sucReservedIndices += i

          ( premise( Suc( i ) ), i )

        case IsFormula( f ) =>
          var i = premise.succedent.indexOf( f )

          while ( sucReservedIndices contains i )
            i = premise.succedent.indexOf( f, i + 1 )

          if ( i != -1 )
            sucReservedIndices += i

          ( f, i )

        case IsIndex( i: Ant ) => throw LKRuleCreationException( s"Index $i should be in the succedent." )
      }
    }

    val ( antFormulas, antIndices ) = ant.unzip

    val ( sucFormulas, sucIndices ) = suc.unzip

    ( antFormulas, antIndices, sucFormulas, sucIndices )
  }

  /**
   * Throws an exception if the output of findFormulasInPremise contains any -1 entries.
   *
   * @param premise The sequent in question.
   * @param antFormulas The list of formulas in the antecedent.
   * @param antIndices The list of indices corresponding to antFormulas.
   * @param sucFormulas The list of formulas in the succedent.
   * @param sucIndices The list indices corresponding to sucFormulas.
   * @return
   */
  protected def validateIndices( premise: HOLSequent )( antFormulas: Seq[Formula], antIndices: Seq[Int],
                                                        sucFormulas: Seq[Formula], sucIndices: Seq[Int] ): Unit = {
    val antMap = scala.collection.mutable.HashMap.empty[Formula, Int]
    val sucMap = scala.collection.mutable.HashMap.empty[Formula, Int]

    for ( ( f, i ) <- antFormulas zip antIndices ) {
      val count = antMap.getOrElse( f, 0 )

      if ( i == -1 )
        throw LKRuleCreationException( s"Formula $f only found $count times in antecedent of $premise." )

      antMap += f -> ( count + 1 )
    }

    for ( ( f, i ) <- sucFormulas zip sucIndices ) {
      val count = sucMap.getOrElse( f, 0 )

      if ( i == -1 )
        throw LKRuleCreationException( s"Formula $f only found $count times in succedent of $premise." )

      sucMap += f -> ( count + 1 )
    }

  }

  /**
   * Combines findIndicesOrFormulasInPremise and validateIndices. That is, it will return a pair
   * of lists of indices and throw an exception if either list contains a -1.
   *
   * @param premise The sequent in question.
   * @param antIndicesFormulas The list of indices or formulas in the antecedent.
   * @param sucIndicesFormulas The list of indices or formulas in the succedent.
   * @return
   */
  protected def findAndValidate( premise: HOLSequent )(
    antIndicesFormulas: Seq[IndexOrFormula],
    sucIndicesFormulas: Seq[IndexOrFormula] ): ( Seq[Int], Seq[Int] ) = {
    val ( antFormulas, antIndices, sucFormulas, sucIndices ) =
      findIndicesOrFormulasInPremise( premise )( antIndicesFormulas, sucIndicesFormulas )
    validateIndices( premise )( antFormulas, antIndices, sucFormulas, sucIndices )
    ( antIndices, sucIndices )
  }
}
