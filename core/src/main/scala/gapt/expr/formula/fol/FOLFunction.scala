package gapt.expr.formula.fol

import gapt.expr.Apps

object FOLFunction {
  def apply(sym: String, args: FOLTerm*)(implicit dummyImplicit: DummyImplicit): FOLTerm = FOLFunction(sym, args)
  def apply(sym: String, args: Seq[FOLTerm]): FOLTerm =
    Apps(FOLFunctionConst(sym, args.size), args).asInstanceOf[FOLTerm]

  def unapply(e: FOLTerm): Option[(String, List[FOLTerm])] = e match {
    case Apps(FOLFunctionConst(sym, _), args) =>
      Some((sym, args.asInstanceOf[List[FOLTerm]]))
    case _ => None
  }
}
