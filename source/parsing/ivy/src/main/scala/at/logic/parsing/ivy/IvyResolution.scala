package at.logic.parsing.ivy

import at.logic.calculi.proofs.{BinaryRuleTypeA, UnaryRuleTypeA, NullaryRuleTypeA}
import at.logic.calculi.proofs.{NullaryAGraphProof, UnaryAGraphProof, BinaryAGraphProof, AGraphProof}
import at.logic.utils.ds.acyclicGraphs.{LeafAGraph, UnaryAGraph, BinaryAGraph}
import at.logic.parsing.lisp.SExpression
import at.logic.language.fol.Substitution
import at.logic.language.fol.{FOLConst, FOLTerm}
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.resolution.Clause

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
case object PropositionalType extends UnaryRuleTypeA{ override def toString = "Propositional"};
case object NewSymbolType extends UnaryRuleTypeA{ override def toString = "NewSymbol"};

abstract sealed trait IvyResolutionProof extends AGraphProof[Clause] {
  val id : String;
  val clause_exp : SExpression;
//  val vertex : Clause;


  override def toString = { val b = new StringBuilder; printNodes(this, Nil, b); b.toString }
  def printNodes(p:IvyResolutionProof, m : List[String], out: StringBuilder) : List[String]  = p match {
    case InitialClause(id, _, clause) =>
      if (! m.contains(id)) {
        out.append(id + " : Input("+clause+")\n"); id::m } else m
    case Instantiate(id,_, sub, clause, parent) =>
      if (! m.contains(id)) {
        val l = printNodes(parent, m, out);
        out.append(id + " : Instance("+clause+") by " + parent.id + "\n"); id::l
      } else m
    case Propositional(id,_, clause, parent) =>
      if (! m.contains(id)) {
        val l1 = printNodes(parent,m, out);
        out.append(id + " : Propositional("+clause+") by "+ parent.id +"\n");
        id::l1
      } else m
    case Flip(id,_, flipped, clause, parent) =>
      if (! m.contains(id)) {
        val l1 = printNodes(parent,m, out);
        out.append(id + " : Flip("+clause+") by "+ parent.id +"\n");
        id::l1
      } else m
    case Resolution(id, _, lit1, lit2, clause, parent1, parent2) =>
      if (! m.contains(id)) {
        val l1 = printNodes(parent1,m, out);
        val l2 = printNodes(parent2,l1, out);
        out.append(id + " : Resolution("+clause+") by " + parent1.id + " and " + parent2.id + "\n");
        id::l2
      } else m
    case Paramodulation(id, _, pos, lit, orientation, clause, parent1, parent2) =>
      if (! m.contains(id)) {
        val l1 = printNodes(parent1,m, out);
        val l2 = printNodes(parent2,l1, out);
        out.append(id + " : Paramodulation("+clause+") by " + parent1.id + " and " + parent2.id + "\n")
        id::l2
      } else m
    case NewSymbol(id, _, lit, symbol, term, clause, parent ) =>
      if (! m.contains(id)) {
        val l1 = printNodes(parent,m, out);
        out.append(id + " : NewSymbol("+clause+") by "+ parent.id +"\n");
        id::l1
      } else m

    //case _ => out.append("rule not implemented"); m
  }

};

//inheritance of BinaryAGraph is necessary because BinaryAGraphProof does not provide a constructor
//  adding the constructor would introduce another override and use up unneccessary memory, we probably need
//  to discuss this
case class InitialClause(id: String,
                         clause_exp : SExpression,
                         override val vertex: Clause)
  extends LeafAGraph[Clause](vertex) with NullaryAGraphProof[Clause] with IvyResolutionProof {

  def rule = InitialClauseType;
//  override def name = "Initial Clause"
};

case class Instantiate(id: String,
                       clause_exp : SExpression,
                       substitution : Substitution,
                       override val vertex : Clause, override val t : IvyResolutionProof)
  extends UnaryAGraph(vertex, t) with UnaryAGraphProof[Clause] with IvyResolutionProof {
  def rule = InstantiateType
//  override def name = "Instantiate"
};

case class Flip(id: String,
                clause_exp : SExpression, flipped : FormulaOccurrence,
                override val vertex : Clause, override val t : IvyResolutionProof)
  extends UnaryAGraph(vertex, t) with UnaryAGraphProof[Clause] with IvyResolutionProof {
  def rule = FlipType
//  override def name = "Flip"
};

case class Propositional(id : String, clause_exp : SExpression, override val vertex : Clause, override val t : IvyResolutionProof)
  extends UnaryAGraph(vertex, t) with UnaryAGraphProof[Clause] with IvyResolutionProof {
  def rule = PropositionalType

};


case class Paramodulation(id: String,
                          clause_exp : SExpression,
                          position : List[Int],
                          lit : FormulaOccurrence,
                          is_demodulation : Boolean, // if the formula should be left to right or right to left
                          override val vertex: Clause,
                          override val t1: IvyResolutionProof,
                          override val t2: IvyResolutionProof)
  extends BinaryAGraph(vertex, t1, t2) with BinaryAGraphProof[Clause] with IvyResolutionProof {
  def rule = ParamodulationType
//  override def name = "Paramodulation"
};

case class Resolution(id: String,
                      clause_exp : SExpression,
                      lit1 : FormulaOccurrence,  //resolved literal in t1
                      lit2 : FormulaOccurrence,  //resolved literal in t2
                      override val vertex: Clause,
                      override val t1: IvyResolutionProof,
                      override val t2: IvyResolutionProof)
  extends BinaryAGraph(vertex, t1, t2) with BinaryAGraphProof[Clause] with IvyResolutionProof {
  def rule = ResolutionType
//  override def name = "Resolution"
};


case class NewSymbol(id: String,
                       clause_exp : SExpression,
                       lit : FormulaOccurrence,
                       new_symbol : FOLConst,
                       replacement_term : FOLTerm,
                       override val vertex : Clause, override val t : IvyResolutionProof)
  extends UnaryAGraph(vertex, t) with UnaryAGraphProof[Clause] with IvyResolutionProof {
  def rule = NewSymbolType
  //  override def name = "Instantiate"
};
/** end of calculus defintion **/

