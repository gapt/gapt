package at.logic.calculi.expansionTrees

import at.logic.language.hol._
import at.logic.utils.ds.trees._

trait ExpansionTree extends TreeA[Option[HOLFormula],Option[HOLExpression]]
case class WeakQuantifier(formula: HOLFormula, instances: Seq[Tuple2[ExpansionTree, HOLExpression]]) extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  lazy val node = Some(formula)
  lazy val children = instances.map(x => (x._1,Some(x._2)))
}
case class StrongQuantifier(formula: HOLFormula, variable: HOLVar, selection: ExpansionTree) extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  lazy val node = Some(formula)
  lazy val children = List(Pair(selection,Some(variable)))
}
case class And(left: ExpansionTree, right: ExpansionTree) extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  val node = None
  lazy val children = List(Pair(left,None),Pair(right,None))
}
case class Or(left: ExpansionTree, right: ExpansionTree) extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  val node = None
  lazy val children = List(Pair(left,None),Pair(right,None))
}
case class Imp(left: ExpansionTree, right: ExpansionTree) extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  val node = None
  lazy val children = List(Pair(left,None),Pair(right,None))
}
case class Not(tree: ExpansionTree) extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  val node = None
  lazy val children = List(Pair(tree,None))
}
case class Atom(formula: HOLFormula) extends ExpansionTree with TerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  lazy val node = Some(formula)
}
