package at.logic.gapt.grammars.deltatableOld

import at.logic.gapt.cutintro.GrammarFindingMethod
import at.logic.gapt.expr.FOLTerm
import at.logic.gapt.grammars.VectTratGrammar
import at.logic.gapt.utils.logging.metrics

case class DeltaTableMethodOld( manyQuantifiers: Boolean ) extends GrammarFindingMethod {
  override def findGrammars( lang: Set[FOLTerm] ): Option[VectTratGrammar] = {
    val delta = manyQuantifiers match {
      case true  => new Deltas.UnboundedVariableDelta()
      case false => new Deltas.OneVariableDelta()
    }
    val eigenvariable = "α"
    val deltatable = metrics.time( "dtable" ) { new DeltaTable( lang.toList, eigenvariable, delta ) }

    metrics.time( "dtable2grammar" ) {
      ComputeGrammars.findValidGrammars( lang.toList, deltatable, eigenvariable ).sortBy( _.size ).headOption
    }
  }

  override def name: String = if ( manyQuantifiers ) "many_dtable" else "1_dtable"
}
