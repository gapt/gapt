package at.logic.algorithms.lk

import at.logic.calculi.lk.base.LKProof
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.calculi.lk.propositionalRules.{Axiom, CutRule}

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
}
