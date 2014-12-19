
package at.logic.algorithms.lk.statistics

import at.logic.calculi.lk._
import at.logic.calculi.lk.base.{LKProof, Sequent}
import at.logic.calculi.slk._
import at.logic.language.lambda.types.TA
import at.logic.language.hol.{HOLExpression, HOLApp, HOLAbs, HOLConst}
import at.logic.calculi.lksk.{UnaryLKskProof}
import scala.collection.mutable

object getStatistics {
  class LKStats( var unary: Int, var binary: Int, var cuts: Int)
  {
    def incUnary = {
      unary += 1
      this
    }

    def incBinary = {
      binary += 1
      this
    }

    def incCuts = {
      cuts += 1
      this
    }
  }

  def apply( p: LKProof ) : LKStats = p match {
    case CutRule( p1, p2, _, _, _ ) => merge( getStatistics( p1 ), getStatistics( p2 ) ).incBinary.incCuts
    case BinaryLKProof(_, p1, p2, _, _, _, _) => merge( getStatistics( p1 ), getStatistics( p2 ) ).incBinary
    case UnaryLKProof(_, p, _, _, _) => getStatistics( p ).incUnary
    case UnaryLKskProof(_, p, _, _, _) => getStatistics( p ).incUnary
    case Axiom(so) => new LKStats(0, 0, 0)
  }

  def merge( s1: LKStats, s2: LKStats ) = new LKStats( s1.unary + s2.unary, s1.binary + s2.binary, s1.cuts + s2.cuts )
}

// return the types of all constants in the sequents list
// TODO: this can be implemented with an immutable map
object getTypeInformation {
  def apply(sequents: List[Sequent]): Map[HOLExpression, TA] = {
    val map = mutable.Map[HOLExpression, TA]()
    sequents.foreach(s => {
      s.antecedent.foreach(f => mapValues(map, f.formula)); 
      s.succedent.foreach(f => mapValues(map, f.formula))
    })
    map.toMap //create an immutable map from the mutable one
  }
  private def mapValues(map: mutable.Map[HOLExpression, TA], f: HOLExpression): Unit = f match {
    case c: HOLConst => map.getOrElseUpdate(c, c.exptype)
    case HOLApp(a,b) => mapValues(map, a); mapValues(map, b)
    case HOLAbs(_,b) => mapValues(map, b)
    case _ => ()
  }
}

  // Get the total number of rules of a proof
  object rulesNumber {
    def apply(p: LKProof) : Int = p match {
      case Axiom(s)  => 0
      case BinaryLKProof(_, p1, p2, _, _, _, _) => apply(p1) + apply(p2) + 1
      case UnaryLKProof(_, p, _, _, _) => apply(p) + 1
      case AndEquivalenceRule1(up, _, _, _) => apply(up) + 1
      case OrEquivalenceRule1(up, _, _, _) => apply(up) + 1
      case AndEquivalenceRule3(up, _, _, _) => apply(up) + 1
      case OrEquivalenceRule3(up, _, _, _) => apply(up) + 1
      case _ =>  throw new Exception("ERROR: Unexpected rule while computing the number of rules of a proof.")
    }
  }

  // Get the number of quantified rules of a proof
  object quantRulesNumber {
    def apply(p: LKProof) : Int = p match {
      case Axiom(s)  => 0
      case WeakeningLeftRule(p, _, _) => apply(p)
      case WeakeningRightRule(p, _, _) => apply(p)
      case ContractionLeftRule(p, _, _, _, _) => apply(p)
      case ContractionRightRule(p, _, _, _, _) => apply(p)
      case NegLeftRule(p, _, _, _) => apply(p)
      case NegRightRule(p, _, _, _) => apply(p)
      case AndLeft1Rule(p, _, _, _) => apply(p)
      case AndLeft2Rule(p, _, _, _) => apply(p)
      case AndRightRule(p1, p2, _, _, _, _) => apply(p1) + apply(p2)
      case OrRight1Rule(p, _, _, _) => apply(p)
      case OrRight2Rule(p, _, _, _) => apply(p)
      case OrLeftRule(p1, p2, _, _, _, _) => apply(p1) + apply(p2)
      case ImpLeftRule(p1, p2, _, _, _, _) => apply(p1) + apply(p2)
      case ImpRightRule(p, _, _, _, _) => apply(p)
      case ForallLeftRule(p, _, _, _, _) => apply(p) + 1
      case ForallRightRule(p, _, _, _, _) => apply(p) + 1
      case ExistsLeftRule(p, _, _, _, _) => apply(p) + 1
      case ExistsRightRule(p, _, _, _, _) => apply(p) + 1
      case CutRule(p1, p2, _, _, _) => apply(p1) + apply(p2)
      // Schema rules
      case AndLeftEquivalenceRule1(p, _, _, _) => apply(p)
      case AndRightEquivalenceRule1(p, _, _, _) => apply(p) 
      case OrLeftEquivalenceRule1(p, _, _, _) => apply(p)
      case OrRightEquivalenceRule1(p, _, _, _) => apply(p)
      case AndLeftEquivalenceRule3(p, _, _, _) => apply(p)
      case AndRightEquivalenceRule3(p, _, _, _) => apply(p)
      case OrLeftEquivalenceRule3(p, _, _, _) => apply(p)
      case OrRightEquivalenceRule3(p, _, _, _) => apply(p)     
      // Equality rules
      case EquationLeft1Rule(p1, p2, _, _, _, _, _) => apply(p1) + apply(p2)
      case EquationLeft2Rule(p1, p2, _, _, _, _, _) => apply(p1) + apply(p2)
      case EquationRight1Rule(p1, p2, _, _, _, _, _) => apply(p1) + apply(p2)
      case EquationRight2Rule(p1, p2, _, _, _, _, _) => apply(p1) + apply(p2)
      // Definition rules
      case DefinitionLeftRule(p, _, _, _) => apply(p)
      case DefinitionRightRule(p, _, _, _) => apply(p)
      
      case _ => throw new Exception("ERROR: Unexpected rule while computing the number of quantifier rules of a proof.")
    }
  }

  object weakQuantRulesNumber {
    def apply(p: LKProof) : Int = p match {
      case Axiom(s)  => 0
      case WeakeningLeftRule(p, _, _) => apply(p)
      case WeakeningRightRule(p, _, _) => apply(p)
      case ContractionLeftRule(p, _, _, _, _) => apply(p)
      case ContractionRightRule(p, _, _, _, _) => apply(p)
      case NegLeftRule(p, _, _, _) => apply(p)
      case NegRightRule(p, _, _, _) => apply(p)
      case AndLeft1Rule(p, _, _, _) => apply(p)
      case AndLeft2Rule(p, _, _, _) => apply(p)
      case AndRightRule(p1, p2, _, _, _, _) => apply(p1) + apply(p2)
      case OrRight1Rule(p, _, _, _) => apply(p)
      case OrRight2Rule(p, _, _, _) => apply(p)
      case OrLeftRule(p1, p2, _, _, _, _) => apply(p1) + apply(p2)
      case ImpLeftRule(p1, p2, _, _, _, _) => apply(p1) + apply(p2)
      case ImpRightRule(p, _, _, _, _) => apply(p)
      case ForallLeftRule(p, _, _, _, _) => apply(p) + 1
      case ForallRightRule(p, _, _, _, _) => apply(p)
      case ExistsLeftRule(p, _, _, _, _) => apply(p) 
      case ExistsRightRule(p, _, _, _, _) => apply(p) + 1
      case CutRule(p1, p2, _, _, _) => apply(p1) + apply(p2)
      // Schema rules
      case AndLeftEquivalenceRule1(p, _, _, _) => apply(p)
      case AndRightEquivalenceRule1(p, _, _, _) => apply(p) 
      case OrLeftEquivalenceRule1(p, _, _, _) => apply(p)
      case OrRightEquivalenceRule1(p, _, _, _) => apply(p)
      case AndLeftEquivalenceRule3(p, _, _, _) => apply(p)
      case AndRightEquivalenceRule3(p, _, _, _) => apply(p)
      case OrLeftEquivalenceRule3(p, _, _, _) => apply(p)
      case OrRightEquivalenceRule3(p, _, _, _) => apply(p)       
      // Equality rules
      case EquationLeft1Rule(p1, p2, _, _, _, _, _) => apply(p1) + apply(p2)
      case EquationLeft2Rule(p1, p2, _, _, _, _, _) => apply(p1) + apply(p2)
      case EquationRight1Rule(p1, p2, _, _, _, _, _) => apply(p1) + apply(p2)
      case EquationRight2Rule(p1, p2, _, _, _, _, _) => apply(p1) + apply(p2)
      // Definition rules
      case DefinitionLeftRule(p, _, _, _) => apply(p)
      case DefinitionRightRule(p, _, _, _) => apply(p)
      
      case _ => throw new Exception("ERROR: Unexpected rule while computing the number of quantifier rules of a proof.")
    }
  }

  // Get the number of contractions left in a proof
  object contLeftNumber {
    def apply(p: LKProof) : Int = p match {
      case Axiom(s)  => 0
      case WeakeningLeftRule(p, _, _) => apply(p)
      case WeakeningRightRule(p, _, _) => apply(p)
      case ContractionLeftRule(p, _, _, _, _) => apply(p) + 1
      case ContractionRightRule(p, _, _, _, _) => apply(p)
      case NegLeftRule(p, _, _, _) => apply(p)
      case NegRightRule(p, _, _, _) => apply(p)
      case AndLeft1Rule(p, _, _, _) => apply(p)
      case AndLeft2Rule(p, _, _, _) => apply(p)
      case AndRightRule(p1, p2, _, _, _, _) => apply(p1) + apply(p2)
      case OrRight1Rule(p, _, _, _) => apply(p)
      case OrRight2Rule(p, _, _, _) => apply(p)
      case OrLeftRule(p1, p2, _, _, _, _) => apply(p1) + apply(p2)
      case ImpLeftRule(p1, p2, _, _, _, _) => apply(p1) + apply(p2)
      case ImpRightRule(p, _, _, _, _) => apply(p)
      case ForallLeftRule(p, _, _, _, _) => apply(p)
      case ForallRightRule(p, _, _, _, _) => apply(p)
      case ExistsLeftRule(p, _, _, _, _) => apply(p)
      case ExistsRightRule(p, _, _, _, _) => apply(p)
      case CutRule(p1, p2, _, _, _) => apply(p1) + apply(p2)
      // Schema rules
      case AndLeftEquivalenceRule1(p, _, _, _) => apply(p)
      case AndRightEquivalenceRule1(p, _, _, _) => apply(p) 
      case OrLeftEquivalenceRule1(p, _, _, _) => apply(p)
      case OrRightEquivalenceRule1(p, _, _, _) => apply(p)
      case AndLeftEquivalenceRule3(p, _, _, _) => apply(p)
      case AndRightEquivalenceRule3(p, _, _, _) => apply(p)
      case OrLeftEquivalenceRule3(p, _, _, _) => apply(p)
      case OrRightEquivalenceRule3(p, _, _, _) => apply(p)     
      // Equality rules
      case EquationLeft1Rule(p1, p2, _, _, _, _, _) => apply(p1) + apply(p2)
      case EquationLeft2Rule(p1, p2, _, _, _, _, _) => apply(p1) + apply(p2)
      case EquationRight1Rule(p1, p2, _, _, _, _, _) => apply(p1) + apply(p2)
      case EquationRight2Rule(p1, p2, _, _, _, _, _) => apply(p1) + apply(p2)
      
      case _ => throw new Exception("ERROR: Unexpected rule while computing the number of quantifier rules of a proof.")
    }
  }

  // Get the number of contractions right in a proof
  object contRightNumber {
    def apply(p: LKProof) : Int = p match {
      case Axiom(s)  => 0
      case WeakeningLeftRule(p, _, _) => apply(p)
      case WeakeningRightRule(p, _, _) => apply(p)
      case ContractionLeftRule(p, _, _, _, _) => apply(p)
      case ContractionRightRule(p, _, _, _, _) => apply(p) + 1
      case NegLeftRule(p, _, _, _) => apply(p)
      case NegRightRule(p, _, _, _) => apply(p)
      case AndLeft1Rule(p, _, _, _) => apply(p)
      case AndLeft2Rule(p, _, _, _) => apply(p)
      case AndRightRule(p1, p2, _, _, _, _) => apply(p1) + apply(p2)
      case OrRight1Rule(p, _, _, _) => apply(p)
      case OrRight2Rule(p, _, _, _) => apply(p)
      case OrLeftRule(p1, p2, _, _, _, _) => apply(p1) + apply(p2)
      case ImpLeftRule(p1, p2, _, _, _, _) => apply(p1) + apply(p2)
      case ImpRightRule(p, _, _, _, _) => apply(p)
      case ForallLeftRule(p, _, _, _, _) => apply(p)
      case ForallRightRule(p, _, _, _, _) => apply(p)
      case ExistsLeftRule(p, _, _, _, _) => apply(p)
      case ExistsRightRule(p, _, _, _, _) => apply(p)
      case CutRule(p1, p2, _, _, _) => apply(p1) + apply(p2)
      // Schema rules
      case AndLeftEquivalenceRule1(p, _, _, _) => apply(p)
      case AndRightEquivalenceRule1(p, _, _, _) => apply(p) 
      case OrLeftEquivalenceRule1(p, _, _, _) => apply(p)
      case OrRightEquivalenceRule1(p, _, _, _) => apply(p)
      case AndLeftEquivalenceRule3(p, _, _, _) => apply(p)
      case AndRightEquivalenceRule3(p, _, _, _) => apply(p)
      case OrLeftEquivalenceRule3(p, _, _, _) => apply(p)
      case OrRightEquivalenceRule3(p, _, _, _) => apply(p)     
      // Equality rules
      case EquationLeft1Rule(p1, p2, _, _, _, _, _) => apply(p1) + apply(p2)
      case EquationLeft2Rule(p1, p2, _, _, _, _, _) => apply(p1) + apply(p2)
      case EquationRight1Rule(p1, p2, _, _, _, _, _) => apply(p1) + apply(p2)
      case EquationRight2Rule(p1, p2, _, _, _, _, _) => apply(p1) + apply(p2)
      
      case _ => throw new Exception("ERROR: Unexpected rule while computing the number of quantifier rules of a proof.")
    }
  }

