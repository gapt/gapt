package at.logic.algorithms.lk

import at.logic.calculi.lk.base.{LKProof, Sequent}
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.calculi.lk.propositionalRules.{Axiom, CutRule}
import at.logic.language.lambda.types.TA
import at.logic.language.lambda.typedLambdaCalculus._

import scala.collection.mutable.Map

package statistics {
  object getStatistics {
    class LKStats( var unary: Int, var binary: Int, var cuts: Int )
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
      case Axiom(so) => new LKStats(0, 0, 0)
    }

    def merge( s1: LKStats, s2: LKStats ) = new LKStats( s1.unary + s2.unary, s1.binary + s2.binary, s1.cuts + s2.cuts )
  }

  // return the types of all constants in the sequents list
  object getTypeInformation {
    def apply(sequents: List[Sequent]): Map[LambdaExpression, TA] = {
      val map = Map[LambdaExpression, TA]()
      sequents.foreach(s => {s.antecedent.foreach(f => mapValues(map,f)); s.succedent.foreach(f => mapValues(map,f))})
      map
    }
    private def mapValues(map: Map[LambdaExpression, TA], f: LambdaExpression): Unit = f match {
      case v @ Var(at.logic.language.hol.logicSymbols.ConstantStringSymbol(x), t) => map.getOrElseUpdate(v, t)
      case App(a,b) => mapValues(map, a); mapValues(map, b)
      case Abs(_,b) => mapValues(map, b)
      case _ => ()
    }
  }
}