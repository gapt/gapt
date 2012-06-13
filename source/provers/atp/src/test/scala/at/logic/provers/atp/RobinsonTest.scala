package at.logic.provers.atp

import _root_.at.logic.language.fol.FOLExpression
import _root_.at.logic.provers.atp.commands.base.{BranchCommand, Command}
import _root_.at.logic.provers.atp.commands.logical.DeterministicAndCommand
import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import at.logic.provers.atp.commands.refinements.simple._
import at.logic.provers.atp.commands.refinements.base._
import at.logic.provers.atp.commands.sequents._
import at.logic.provers.atp.commands.robinson._
import org.specs2.mutable._
import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
import at.logic.parsing.readers.StringReader
import at.logic.calculi.resolution.base._
import at.logic.calculi.resolution.robinson._
import at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithm
import at.logic.algorithms.matching.fol.FOLMatchingAlgorithm

//private class MyParser(str: String) extends StringReader(str) with SimpleResolutionParserFOL

class RobinsonTest extends SpecificationWithJUnit {
}