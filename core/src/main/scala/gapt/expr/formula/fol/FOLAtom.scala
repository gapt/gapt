package gapt.expr.formula.fol

import gapt.expr.Apps
import gapt.expr.formula.Atom

trait FOLAtom extends FOLPartialAtom with Atom with FOLFormula {
  private[expr] override val numberOfArguments: Int = 0
}

object FOLAtom {
  def apply(sym: String, args: FOLTerm*)(implicit dummyImplicit: DummyImplicit): FOLAtom = FOLAtom(sym, args)
  def apply(sym: String, args: Seq[FOLTerm]): FOLAtom =
    Apps(FOLAtomConst(sym, args.size), args).asInstanceOf[FOLAtom]

  def unapply(e: FOLAtom): Option[(String, List[FOLTerm])] = e match {
    case Apps(FOLAtomConst(sym, _), args) if e.isInstanceOf[FOLAtom] =>
      Some((sym, args.asInstanceOf[List[FOLTerm]]))
    case _ => None
  }
}
