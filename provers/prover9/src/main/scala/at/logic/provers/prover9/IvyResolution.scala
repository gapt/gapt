package at.logic.provers.prover9.ivy

import at.logic.calculi.proofs.{BinaryRuleTypeA, UnaryRuleTypeA, NullaryRuleTypeA}
import at.logic.calculi.agraphProofs.{NullaryAGraphProof, UnaryAGraphProof, BinaryAGraphProof, AGraphProof}
import at.logic.calculi.resolution.base.Clause
import at.logic.utils.ds.acyclicGraphs.{LeafAGraph, UnaryAGraph, BinaryAGraph}
import at.logic.provers.prover9.lisp.SExpression

/**** Implementation of Ivy's Resolution Calculus ***
 * Ivy has it's own variation of resolution which only resolves over identical literals but has an instantiation rule.
 * It should be possible to display the proofs in prooftool, but a translation to robinson resolution is neccessary for
 * many applications.
 */


/*****  Define Ivy Proofs in a way that Prooftool can display them  *****/
// rule types
case object InitialClauseType extends NullaryRuleTypeA { override def toString = "Initial Clause"};
case object InstantiateType extends UnaryRuleTypeA{ override def toString = "Instantiation"};
case object ParamodulationType extends BinaryRuleTypeA{ override def toString = "Paramodulation"};
case object ResolutionType extends BinaryRuleTypeA{ override def toString = "Resolution"};
case object FlipType extends UnaryRuleTypeA{ override def toString = "Flip"};

abstract sealed trait IvyResolutionProof extends AGraphProof[Clause] {
  val clause_exp : SExpression;
};

//inheritance of BinaryAGraph is necessary becauseBinaryAGraphProof does not provide a constructor
//  adding the constructor would introduce another override and use up unneccessary memory, we probably need
//  to discuss this
case class InitialClause(clause_exp : SExpression,
                         override val vertex: Clause)
  extends LeafAGraph[Clause](vertex) with NullaryAGraphProof[Clause] with IvyResolutionProof {

  def rule = InitialClauseType;
  override def name = "Initial Clause"


};

case class Instantiate(clause_exp : SExpression, override val vertex : Clause, override val t : IvyResolutionProof)
  extends UnaryAGraph(vertex, t) with UnaryAGraphProof[Clause] with IvyResolutionProof {
  def rule = InstantiateType
  override def name = "Instantiate"
};

case class Flip(clause_exp : SExpression, override val vertex : Clause, override val t : IvyResolutionProof)
  extends UnaryAGraph(vertex, t) with UnaryAGraphProof[Clause] with IvyResolutionProof {
  def rule = FlipType
  override def name = "Flip"
};

case class Paramodulation(clause_exp : SExpression,
                          override val vertex: Clause,
                          override val t1: IvyResolutionProof,
                          override val t2: IvyResolutionProof)
  extends BinaryAGraph(vertex, t1, t2) with BinaryAGraphProof[Clause] with IvyResolutionProof {
  def rule = InstantiateType
  override def name = "Paramodulation"
};

case class Resolution(clause_exp : SExpression,
                      override val vertex: Clause,
                      override val t1: IvyResolutionProof,
                      override val t2: IvyResolutionProof)
  extends BinaryAGraph(vertex, t1, t2) with BinaryAGraphProof[Clause] with IvyResolutionProof {
  def rule = InstantiateType
  override def name = "Resolution"
};
/** end of calculus defintion **/
