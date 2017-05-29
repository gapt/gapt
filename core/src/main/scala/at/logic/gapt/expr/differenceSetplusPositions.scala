package at.logic.gapt.expr

import at.logic.gapt.expr.{ Apps, FOLTerm, LambdaExpression }
import scala.collection.mutable.ListBuffer

/**
 * Created by root on 02.12.16.
 */
object differenceSetplusPositions {

  // List of different pairs. It could contain also non-unifiable pairs (for instance: (c,fc) for a constant c and a function f).
  private var differenceList = ListBuffer[( LambdaExpression, LambdaExpression, String )]()

  // Initializes the computation of the list of different pairs.
  def apply( termL: LambdaExpression, termR: LambdaExpression ): ListBuffer[( LambdaExpression, LambdaExpression, String )] = {
    var differenceSet = ListBuffer[( LambdaExpression, LambdaExpression, String )]()

    differenceSet += ( ( termL, termR, "0" ) )

    walk( differenceSet )

    differenceList
  }

  //Ask how to implement this

  //def apply( language: Traversable[LambdaExpression] ): Set[LambdaExpression] = {
  //val subTerms = mutable.Set[LambdaExpression]()
  //for ( t <- language ) walk( t, subTerms )
  //subTerms.toSet
  //}

  //def apply( t: FOLTerm ): Set[FOLTerm] = apply( Some( t ) )

  //def apply( language: Traversable[FOLTerm] )( implicit dummyImplicit: DummyImplicit ): Set[FOLTerm] =
  //apply( language: Traversable[LambdaExpression] ).asInstanceOf[Set[FOLTerm]]

  // Main recursive call.
  private def walk( differenceSet: scala.collection.mutable.ListBuffer[( LambdaExpression, LambdaExpression, String )] ): scala.collection.mutable.ListBuffer[( LambdaExpression, LambdaExpression, String )] = {

    // The differenceSet corresponds to the differenceSetIterator of the former run. If it is empty we compared all subterms and exit the loop.
    if ( differenceSet.isEmpty ) return differenceList

    // For some reasons the algorithm does not work whenever I do not redefine the iterator. Maybe someone with better knowledge can help.
    var differenceSetIterator = differenceSet

    val ( differenceSetL: LambdaExpression, differenceSetR: LambdaExpression, lastPosition: String ) = differenceSet.head
    val Apps( fL, _ ) = differenceSetL
    val Apps( fR, _ ) = differenceSetR

    // If the outermost function is equal we have to add the arguments to the differenceSetIterator which contains possible different pairs. Since we compare always the
    // first element of the differenceSetIterator we can drop the first element if the outermost function is equal. Afterwards we call again the walk function with the new
    // list. Note that the differenceSetIterator might increase in this step. The good news is that we consider finite nested terms.
    if ( fL == fR ) {

      val Apps( _, argsL ) = differenceSetL
      val Apps( _, argsR ) = differenceSetR

      differenceSetIterator = differenceSetIterator.tail

      for ( i <- 1 to argsL.length ) {
        differenceSetIterator += ( ( argsL.apply( i - 1 ), argsR.apply( i - 1 ), lastPosition + i.toString ) )
      }

      walk( differenceSetIterator )

    } // If the outermost function is not equal we found a different pair and add it to the different list. On the other side we have to eliminate this pair from the
    // differenceSetIterator. Afterwards we call the walk function. This time the size of the differenceSetIterator will always decrease.
    else {

      differenceList += differenceSetIterator.head
      differenceSetIterator = differenceSetIterator.tail

      walk( differenceSetIterator )

    }

    differenceList

  }

}
