package at.logic.provers.atp.commands

/**
 * this file contains command for a guided search using ids for clauses,as for example when parsing the output of theorem provers and using the rules from there
 */
package guided {

import _root_.at.logic.calculi.resolution.base.ResolutionProof
import _root_.at.logic.calculi.resolution.robinson.{Clause, InitialClause}
import _root_.at.logic.language.fol.FOLFormula
import _root_.at.logic.provers.atp.Definitions._
import base.DataCommand
import _root_.at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.occurrences._
import scala.collection.immutable.Seq
import scala.collection.mutable.Map

  case class GetGuidedClausesCommand(parentIds: Iterable[String]) extends DataCommand[Clause] {
    def apply(state: State, data: Any) = {
      val guidedMap = state("gmap").asInstanceOf[Map[String,ResolutionProof[Clause]]]
      List((state,parentIds.map(guidedMap(_))))
    }
  }

  case class GetGuidedClausesLiteralsPositions(ls: Iterable[Tuple3[String, Int, Iterable[Int]]]) extends DataCommand[Clause] {
    def apply(state: State, data: Any) = {
      val guidedMap = state("gmap").asInstanceOf[Map[String,ResolutionProof[Clause]]]
      List((state,ls.map(x => {
        val p = guidedMap(x._1)
        (p,p.root.literals(x._2),x._3)
      })))
    }
  }

  case class GetGuidedClausesLiterals(ls: Iterable[Tuple2[String, Int]]) extends DataCommand[Clause] {
    def apply(state: State, data: Any) = {
      val guidedMap = state("gmap").asInstanceOf[Map[String,ResolutionProof[Clause]]]
      List((state,ls.map(x => {
        val p = guidedMap(x._1)
        (p,p.root.literals(x._2))
      })))
    }
  }

  case class AddGuidedInitialClauseCommand(id: String, cls: Seq[FOLFormula]) extends DataCommand[Clause] {
    def apply(state: State, data: Any) = {
      val p = InitialClause(cls)(defaultFormulaOccurrenceFactory)
      val guidedMap = (if (state.isDefinedAt("gmap")) state("gmap").asInstanceOf[Map[String,ResolutionProof[Clause]]]
        else {
          val ret = Map[String,ResolutionProof[Clause]]()
          state += new Tuple2("gmap", ret)
          ret
        })
      guidedMap += ((id, p))
      List((state,p))
    }
  }

  // we add a clause which might be a variant of that we look for.
  case class AddGuidedResolventCommand(id: String) extends DataCommand[Clause] {
    def apply(state: State, data: Any) = {
      val p = data.asInstanceOf[ResolutionProof[Clause]]
      val guidedMap = (if (state.isDefinedAt("gmap")) state("gmap").asInstanceOf[Map[String,ResolutionProof[Clause]]]
        else {
          val ret = Map[String,ResolutionProof[Clause]]()
          state += new Tuple2("gmap", ret)
          ret
        })
      guidedMap += ((id, p))
      List((state,p))
    }
  }
}
