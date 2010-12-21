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
import scala.collection.mutable.Map

package GAPScalaInteractiveShellLibrary {
import _root_.at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
import _root_.at.logic.calculi.resolution.robinson.{Clause, ClauseOccurrence}
import _root_.at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import _root_.at.logic.language.fol.{FOLExpression, FOLTerm}
import _root_.at.logic.calculi.resolution.base.ResolutionProof
import _root_.at.logic.provers.atp.commands.refinements.simple.SimpleRefinementGetCommand
import _root_.at.logic.provers.atp.Prover
import at.logic.parsing.language.simple.SimpleFOLParser
object loadProofs {
    def apply(file: String) = 
      try {
        (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream(file)))) with XMLProofDatabaseParser).getProofDatabase().proofs
      }
      catch
      {
        case _ =>
          (new XMLReader(new InputStreamReader(new FileInputStream(file))) with XMLProofDatabaseParser).getProofDatabase().proofs
      }
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
  object structToLabelledClausesList {
    def apply(s: Struct) = StandardClauseSet.transformStructToLabelledClauseSet(s)
  }
  object createHOLExpression {
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
  object writeLabelledSequentListLatex {
    def apply(ls: List[LabelledSequentOccurrence], outputFile: String) = {
      // maps original types and definitions of abstractions
      val sections = ("Types", getTypeInformation(ls.map( so => so.getSequent )).toList.sort((x,y) => x.toString < y.toString))::Nil
      (new FileWriter(outputFile) with LabelledSequentsListLatexExporter with HOLTermArithmeticalExporter).exportSequentList(ls,sections).close
    }
  }
  object writeLatex {
    def apply(ls: List[Sequent], outputFile: String) = {
      // maps original types and definitions of abstractions
      val sectionsPre = ("Types", getTypeInformation(ls).toList.sort((x,y) => x.toString < y.toString))::Nil
      
      val sections = try {
        // convert to fol and obtain map of definitons
        val imap = Map[at.logic.language.lambda.typedLambdaCalculus.LambdaExpression, at.logic.language.hol.logicSymbols.ConstantStringSymbol]()
        val iid = new {var idd = 0; def nextId = {idd = idd+1; idd}}
        val cs = ls.map(x => Sequent(
            x.antecedent.map(y => reduceHolToFol(y.asInstanceOf[HOLExpression],imap,iid).asInstanceOf[FOLFormula]),
            x.succedent.map(y => reduceHolToFol(y.asInstanceOf[HOLExpression],imap,iid).asInstanceOf[FOLFormula])
        ))
        ("Definitions", imap.toList.map(x => (x._1, createExampleFOLConstant(x._1, x._2))))::sectionsPre
      }
      catch {
        case _ => sectionsPre
      }
      (new FileWriter(outputFile) with SequentsListLatexExporter with HOLTermArithmeticalExporter).exportSequentList(ls,sections).close
    }
  }

  object exportXML {
    def apply( ls: List[LKProof], names: List[String], outputFile: String ) = {
      val exporter = new LKExporter{}
      val pairs = ls.zip( names )
      scala.xml.XML.saveFull( outputFile,
        <proofdatabase>
          <definitionlist/>
          <axiomset/>
          { pairs.map( p => exporter.exportProof( p._2, p._1 ) ) }
          <variabledefinitions/>
        </proofdatabase>, "UTF-8", true,
        scala.xml.dtd.DocType( "proofdatabase", scala.xml.dtd.SystemID( "http://www.logic.at/ceres/xml/5.0/proofdatabase.dtd" ) , Nil ) )
    }
  }

  object parse {
    private class CLIParserFOL(input: String) extends StringReader(input) with SimpleFOLParser
    private class CLIParserHOL(input: String) extends StringReader(input) with SimpleHOLParser

    def fol(string:String) = {
       new CLIParserFOL(string).getTerm.asInstanceOf[FOLFormula]
    }

    def folterm(string:String) = {
       new CLIParserFOL(string).getTerm.asInstanceOf[FOLTerm]
    }

    //this is redundant
    def hol(string:String) = {
       new CLIParserHOL(string) getTerm
    }

    def help() = {
      println("folterm: String => FOLFormula")
      println("folterm: String => FOLTerm")
      println("hol: String => HOLExpression")
    }
  }

  // atp support
  object refuteFOL {
    import at.logic.provers.atp.commands.base._
    import at.logic.provers.atp.commands.ui._
    import at.logic.provers.atp.commands.sequents._
    import at.logic.provers.atp.commands.robinson._
    import at.logic.provers.atp.commands.logical.DeterministicAndCommand
    def stream1:  Stream[Command[ClauseOccurrence]] = Stream.cons(SimpleRefinementGetCommand[ClauseOccurrence],
      Stream.cons(VariantsCommand,
      Stream.cons(DeterministicAndCommand[ClauseOccurrence]((
        List(ApplyOnAllPolarizedLiteralPairsCommand[ClauseOccurrence], ResolveCommand(FOLUnificationAlgorithm), FactorCommand(FOLUnificationAlgorithm)),
        List(ParamodulationCommand(FOLUnificationAlgorithm)))),
      Stream.cons(SimpleForwardSubsumptionCommand[ClauseOccurrence](new StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}),
      Stream.cons(SimpleBackwardSubsumptionCommand[ClauseOccurrence](new StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}),
      Stream.cons(InsertResolventCommand[ClauseOccurrence],
      Stream.cons(RefutationReachedCommand[ClauseOccurrence], stream1)))))))
    def stream: Stream[Command[ClauseOccurrence]] = Stream.cons(SetTargetClause(Clause(List(),List())), Stream.cons(SearchForEmptyClauseCommand[ClauseOccurrence], stream1))

    def apply(clauses: Seq[Clause]): Option[ResolutionProof[ClauseOccurrence]] =
      new Prover[at.logic.calculi.resolution.robinson.ClauseOccurrence]{}.
        refute(Stream.cons(SetClausesCommand(clauses), stream)).next
  }
  object refuteFOLI {
    import at.logic.provers.atp.commands.base._
    import at.logic.provers.atp.commands.ui._
    import at.logic.provers.atp.commands.sequents._
    import at.logic.provers.atp.commands.robinson._
    import at.logic.provers.atp.commands.logical.DeterministicAndCommand
    def stream1:  Stream[Command[ClauseOccurrence]] = Stream.cons(getTwoClausesFromUICommand[ClauseOccurrence](PromptTerminal.GetTwoClauses),
      Stream.cons(VariantsCommand,
      Stream.cons(DeterministicAndCommand[ClauseOccurrence]((
        List(ApplyOnAllPolarizedLiteralPairsCommand[ClauseOccurrence], ResolveCommand(FOLUnificationAlgorithm), FactorCommand(FOLUnificationAlgorithm)),
        List(ParamodulationCommand(FOLUnificationAlgorithm)))),
      Stream.cons(SimpleForwardSubsumptionCommand[ClauseOccurrence](new StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}),
      Stream.cons(SimpleBackwardSubsumptionCommand[ClauseOccurrence](new StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}),
      Stream.cons(InsertResolventCommand[ClauseOccurrence],
      Stream.cons(RefutationReachedCommand[ClauseOccurrence], stream1)))))))
    def stream: Stream[Command[ClauseOccurrence]] = Stream.cons(SetTargetClause(Clause(List(),List())), Stream.cons(SearchForEmptyClauseCommand[ClauseOccurrence], stream1))

    def apply(clauses: Seq[Clause]): Option[ResolutionProof[ClauseOccurrence]] =
      new Prover[at.logic.calculi.resolution.robinson.ClauseOccurrence]{}.
        refute(Stream.cons(SetClausesCommand(clauses), stream)).next
  }

  object ceres {
    def help = ceresHelp.apply
  }

  object ceresHelp {
    def apply() = {
      println("Available commands:")
      println("loadProofs: String => LKProof")
      println("printPoofStats: LKProof => Unit")
      println("lkTolksk: LKProof => LKProof")
      println("extractStruct: LKProof => Struct")
      println("structToClausesList: Struct => List[SequentOccurrence]")
      println("structToLabelledClausesList: Struct => List[LabelledSequentOccurrence]")
      println("createHOLExpression: String => HOLExpression (Forall x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x2: i, c1: (i -> i)))")
      println("deleteTautologies: List[Sequent] => List[Sequent]")
      println("removeDuplicates: List[Sequent] => List[Sequent]")
      println("unitResolve: List[Sequent] => List[Sequent]")
      println("removeSubsumed: List[Sequent] => List[Sequent]")
      println("normalizeClauses: List[Sequent] => List[Sequent]")
      println("writeLatex: List[Sequent], String => Unit")
      println("writeLabelledSequentListLatex: List[LabelledSequentOccurrence], String => Unit")
      println("parse fol: String => FOLTerm")
      println("parse hol: String => HOLExpression")
      println("exportXML: List[Proof], List[String], String => Unit")
      println("refuteFOL: Seq[Clause] => Option[ResolutionProof[ClauseOccurrence]]")
      println("refuteFOLI: Seq[Clause] => Option[ResolutionProof[ClauseOccurrence]] - simple interactive refutation")
    }
  }
}
