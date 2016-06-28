package at.logic.gapt.formats.nanocop
import at.logic.gapt.expr.{ FOLAtom, FOLConst, FOLFunction, FOLTerm, FOLVar }

sealed abstract class NanocopProof {
  def index: Int
}
case class NanocopMatrix( i1: Int, i2: Int, children: Seq[NanocopProof] ) extends NanocopProof {
  def index = i1
}
case class NanocopClause( i1: Int, i2: Int, terms: Seq[FOLTerm], children: Seq[NanocopProof] ) extends NanocopProof {
  def index = i1
}
case class NanocopAtom( atom: FOLAtom, pol: Boolean ) extends NanocopProof {
  def index = 0
}
