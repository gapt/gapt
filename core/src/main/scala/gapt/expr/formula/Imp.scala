package gapt.expr.formula

import gapt.expr.formula.constants.ImpC

object Imp extends BinaryPropConnectiveHelper(ImpC) {
  object Block {
    def apply(as: Seq[Formula], b: Formula): Formula = as.foldRight(b)(Imp(_, _))
    def unapply(f: Formula): Some[(List[Formula], Formula)] = f match {
      case Imp(a, Block(as, b)) => Some((a :: as, b))
      case b                    => Some((Nil, b))
    }
  }
}
