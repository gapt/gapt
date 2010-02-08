/*
 * GAPScalaInteractiveShellLibrary.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.cli

import at.logic.transformations.ceres.struct.StructCreators
import at.logic.transformations.ceres.clauseSets.StandardClauseSet

import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.readers.XMLReaders._
import at.logic.algorithms.lk.simplification._
import at.logic.algorithms.lk.statistics._
import at.logic.algorithms.lk._
import at.logic.parsing.calculus.xml.saveXML
import at.logic.parsing.calculi.latex.SequentsListLatexExporter
import at.logic.parsing.writers.FileWriter
import at.logic.parsing.language.arithmetic.HOLTermArithmeticalExporter
import at.logic.parsing.language.simple.SimpleHOLParser
import at.logic.parsing.readers.StringReader
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.hol.propositions._
import at.logic.language.hol.logicSymbols._

import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.algorithms.subsumption._
import at.logic.transformations.skolemization.lksk.LKtoLKskc
import at.logic.transformations.ceres.struct._

import java.util.zip.GZIPInputStream
import java.io.{FileReader, FileInputStream, InputStreamReader}
import java.io.File.separator

package GAPScalaInteractiveShellLibrary {
  object loadProofs {
    def apply(gzipedFile: String) = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream(gzipedFile)))) with XMLProofDatabaseParser).getProofs()
  }
  object printPoofStats {
    def apply(p: LKProof) = {val stats = getStatistics( p ); println("unary: " + stats.unary); println("binary: " + stats.binary); println("cuts: " + stats.cuts)}
  }
  object lkTolksk {
    def apply(p: LKProof) = LKtoLKskc( p )
  }
  object extractStruct {
    def apply(p: LKProof) = StructCreators.extract( p )
  }
  object structToClausesList {
    def apply(s: Struct) = StandardClauseSet.transformStructToClauseSet(s)
  }
  object createHOLTerm {
    def apply(s: String) = (new StringReader(s) with SimpleHOLParser {}).getTerm()
  }
  object deleteTautologies {
    def apply(ls: List[Sequent]) = at.logic.algorithms.lk.simplification.deleteTautologies( ls )
  }
  object removeDuplicates {
    def apply(ls: List[Sequent]) = ls.removeDuplicates
  }
  object unitResolve {
    def apply(ls: List[Sequent]) = simpleUnitResolutionNormalization(ls)
  }
  object removeSubsumed {
    def apply(ls: List[Sequent]) = subsumedClausesRemoval(ls)
  }
  object normalizeClauses {
    def apply(ls: List[Sequent]) = sequentNormalize(ls)
  }
  object writeLatex {
    def apply(ls: List[Sequent], outputFile: String) = (new FileWriter(outputFile) with SequentsListLatexExporter with HOLTermArithmeticalExporter).exportSequentList(ls).close
  }
  object ceresHelp {
    def apply() = {
      println("Available commands:")
      println("loadProofs: String => LKProof")
      println("printPoofStats: LKProof => Unit")
      println("lkTolksk: LKProof => LKProof")
      println("extractStruct: LKProof => Struct")
      println("structToClausesList: Struct => List[Sequent]")
      println("createHOLTerm: String => HOLTerm (Forall x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x2: i, c1: (i -> i)))")
      println("deleteTautologies: List[Sequent] => List[Sequent]")
      println("removeDuplicates: List[Sequent] => List[Sequent]")
      println("unitResolve: List[Sequent] => List[Sequent]")
      println("removeSubsumed: List[Sequent] => List[Sequent]")
      println("normalizeClauses: List[Sequent] => List[Sequent]")
      println("writeLatex: List[Sequent], String => Unit")
    }
  }
}
