/*
 * GAPScalaInteractiveShellLibrary.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.applet

import at.logic.transformations.ceres.struct.StructCreators
import at.logic.transformations.ceres.clauseSets.StandardClauseSet

import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.readers.XMLReaders._
import at.logic.algorithms.lk.simplification._
import at.logic.algorithms.lk.statistics._
import at.logic.algorithms.lk._
import at.logic.parsing.calculus.xml._
import at.logic.parsing.calculi.latex._
import at.logic.parsing.writers.FileWriter
import at.logic.parsing.language.arithmetic.HOLTermArithmeticalExporter
import at.logic.parsing.language.simple.SimpleHOLParser
import at.logic.parsing.readers.StringReader
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.hol._
import at.logic.language.fol.FOLFormula
import at.logic.language.hol.logicSymbols._

import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.lksk.base._
import at.logic.algorithms.subsumption._
import at.logic.transformations.skolemization.lksk.LKtoLKskc
import at.logic.transformations.ceres.struct._
import at.logic.algorithms.fol.hol2fol._

import java.util.zip.GZIPInputStream
import java.io.{FileReader, FileInputStream, InputStreamReader}
import java.io.File.separator

import at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
import at.logic.calculi.resolution.robinson.{Clause, ClauseOccurrence}
import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import at.logic.language.fol.{FOLExpression, FOLTerm}
import at.logic.calculi.resolution.base.ResolutionProof
import at.logic.provers.atp.commands.refinements.base.SequentsMacroCommand
import at.logic.provers.atp.commands.refinements.simple.SimpleRefinementGetCommand
import at.logic.provers.atp.Prover
import at.logic.parsing.language.simple.SimpleFOLParser
import at.logic.algorithms.unification.hol._


class AppletMain extends java.applet.Applet {
  def huet(s1: String, s2: String) : String = {
    class MyParser(input: String) extends StringReader(input) with SimpleHOLParser

    try {
      HuetAlgorithm.unify1(new MyParser(s1).getTerm(), new MyParser(s2).getTerm()).next match {
        case Some(_) => "Unifiable."
        case None => "Not unifiable."
      }
    }
    catch {
      case e : java.lang.RuntimeException => "RuntimeException (probably parsing error; check input syntax)."
      case e : java.lang.StackOverflowError => "Stack overflow error (i.e. exhausted memory before finding a solution)."
      case _ => "Unkown exception caugt."
    }
  }

  def test() = "scala test!"
}
