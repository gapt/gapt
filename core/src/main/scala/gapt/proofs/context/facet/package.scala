package gapt.proofs.context

import gapt.expr.formula.hol.SkolemFunctions

package object facet {

  implicit val skolemFunsFacet: Facet[SkolemFunctions] = Facet[SkolemFunctions]( SkolemFunctions( None ) )

}
