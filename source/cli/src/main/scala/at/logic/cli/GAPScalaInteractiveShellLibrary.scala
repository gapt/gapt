/*
 * GAPScalaInteractiveShellLibrary.scala
 *
 */

package at.logic.cli.GAPScalaInteractiveShellLibrary

import java.io.{FileInputStream, IOException, InputStreamReader, BufferedWriter => JBufferedWriter, FileWriter => JFileWriter}
import java.util.zip.GZIPInputStream

import at.logic.algorithms.cutIntroduction.Deltas._
import at.logic.algorithms.cutIntroduction._
import at.logic.algorithms.expansionTrees.{compressQuantifiers, minimalExpansionSequents => minimalExpSeq}
import at.logic.algorithms.fol.hol2fol._
import at.logic.algorithms.fol.recreateWithFactory
import at.logic.algorithms.hlk.{ExtendedProofDatabase, HybridLatexParser}
import at.logic.algorithms.interpolation._
import at.logic.algorithms.lk.statistics._
import at.logic.algorithms.lk.{deleteTautologies => deleteTaut, _}
import at.logic.algorithms.lksk.applySubstitution
import at.logic.algorithms.llk.HybridLatexExporter
import at.logic.algorithms.resolution._
import at.logic.algorithms.rewriting.{DefinitionElimination, NameReplacement}
import at.logic.algorithms.shlk._
import at.logic.algorithms.subsumption._
import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import at.logic.calculi.expansionTrees.{MultiExpansionTree, MultiExpansionSequent}
import at.logic.calculi.expansionTrees.{ExpansionSequent, ExpansionTree}
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.lksk.{ExistsSkLeftRule, ExistsSkRightRule, ForallSkLeftRule, ForallSkRightRule, LabelledSequent}
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.calculi.resolution._
import at.logic.calculi.resolution.robinson._
import at.logic.gui.prooftool.gui.Main
import at.logic.language.fol.{AllVar => FOLAllVar, And => FOLAnd, Atom => FOLAtom, ExVar => FOLExVar, Imp => FOLImp, Neg => FOLNeg, Or => FOLOr, Substitution => FOLSubstitution, freeVariables => FOLfreeVariables, _}
import at.logic.language.hoare.Program
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.{BetaReduction => HOLBetaReduction, Substitution => HOLSubstitution, containsQuantifier => containsQuantifierHOL, _}
import at.logic.language.lambda.symbols.StringSymbol
import at.logic.language.lambda.{LambdaExpression, Var, Substitution => LambdaSubstitution}
import at.logic.language.lambda.types._
import at.logic.language.schema.{AllVar => SchemaAllVar, Atom => SchemaAtom, ExVar => SchemaExVar, _}
import at.logic.parsing.calculi.latex._
import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
import at.logic.parsing.calculus.xml._
import at.logic.parsing.hoare.ProgramParser
import at.logic.parsing.ivy.conversion.IvyToRobinson
import at.logic.parsing.ivy.{IvyParser, IvyResolutionProof, InitialClause => IvyInitialClause, Instantiate => IvyInstantiate, Propositional => IvyPropositional, Resolution => IvyResolution}
import at.logic.parsing.language.arithmetic.HOLTermArithmeticalExporter
import at.logic.parsing.language.hlk.HLKHOLParser
import at.logic.parsing.language.prover9._
import at.logic.parsing.language.simple._
import at.logic.parsing.language.tptp.{TPTPFOLExporter, TPTPHOLExporter}
import at.logic.parsing.language.xml.ProofDatabase
import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.lisp.SExpressionParser
import at.logic.parsing.readers.StringReader
import at.logic.parsing.readers.XMLReaders._
import at.logic.parsing.shlk.SchemaFormulaParser
import at.logic.parsing.shlk_parsing.{sFOParser, sFOParserCNT}
import at.logic.parsing.veriT._
import at.logic.parsing.writers.FileWriter
import at.logic.provers.atp.Prover
import at.logic.provers.atp.commands.base._
import at.logic.provers.atp.commands.logical.DeterministicAndCommand
import at.logic.provers.atp.commands.refinements.base.SequentsMacroCommand
import at.logic.provers.atp.commands.refinements.simple.SimpleRefinementGetCommand
import at.logic.provers.atp.commands.robinson._
import at.logic.provers.atp.commands.sequents._
import at.logic.provers.atp.commands.ui._
import at.logic.provers.{Prover => abstractProver}
import at.logic.provers.maxsat.{MaxSATSolver, MaxSAT}
import at.logic.provers.maxsat.MaxSATSolver._
import at.logic.provers.minisat.MiniSAT
import at.logic.provers.prover9.Prover9
import at.logic.provers.prover9.commands.Prover9InitCommand
import at.logic.transformations.ceres.ACNF._
import at.logic.transformations.ceres.ceres_omega
import at.logic.transformations.ceres.clauseSets.SimplifyStruct
import at.logic.transformations.ceres.projections.Projections
import at.logic.transformations.ceres.struct._
import at.logic.transformations.skolemization.lksk.LKtoLKskc
import at.logic.transformations.skolemization.skolemize
import at.logic.transformations.ceres.{CERES, CERESR2LK}
import at.logic.transformations.{ReductiveCutElim, herbrandExtraction}
import at.logic.algorithms.lk.{rule_isomorphic => LKrule_isomorphic}
import at.logic.algorithms.lksk.{rule_isomorphic => LKSKrule_isomorphic}
import at.logic.utils.logging.Stopwatch

import scala.collection.mutable.{Map => MMap}



/*******************************************************************************
 *
 * Organisation of this file follows the structure and order of the help text.
 *
 ******************************************************************************/


/*******************************************************************************
 * Parsing
 ******************************************************************************/
object parseFOL {
  private class CLIParserFOL(input: String) extends StringReader(input) with SimpleFOLParser

  def apply( s: String ) = { new CLIParserFOL(s).getTerm.asInstanceOf[FOLFormula] }
}

object parseHOL {
  private class CLIParserHOL(input: String) extends StringReader(input) with SimpleHOLParser

  def apply( s: String ) = { new CLIParserHOL(s).getTerm }
}

object parseLISP {
  def apply( s: String ) = { SExpressionParser.parseString( s ) }
}

object parseLLKExp {
  def apply( s: String ) = { HLKHOLParser.parse( s ) }
}

object parseLLKFormula {
  def apply( s: String ) = {
    val exp = HLKHOLParser.parse(s)
    require(exp.isInstanceOf[HOLFormula], "Expression is no HOL Formula!")
    exp.asInstanceOf[HOLFormula]
  }
}

object parseProver9 {
  def apply( s: String, use_ladr: Boolean = true) = {
    if (use_ladr)
      Prover9TermParserLadrStyle.parseFormula( s )
    else
      Prover9TermParser.parseFormula( s )
  }
}


/*******************************************************************************
 * Formulas / Sequents / Expressions
 ******************************************************************************/

object hol2folpure extends convertHolToFol

object toClauses {
  def apply(f: HOLFormula) = CNFp(f)
}

object deleteTautologies {
  def apply(ls: List[FSequent]) = deleteTaut(ls)
}

object unitResolve {
  def apply(ls: List[FSequent]) = simpleUnitResolutionNormalization(ls)
}

object removeSubsumed {
  def apply(ls: List[FSequent]) = subsumedClausesRemoval(ls)
}


/*******************************************************************************
 * File Input / Output 
 ******************************************************************************/

object loadProofDB {
  def apply(file: String) =
    try {
      (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream(file)))) with XMLProofDatabaseParser).getProofDatabase()
    }
    catch {
      case _: Exception =>
        (new XMLReader(new InputStreamReader(new FileInputStream(file))) with XMLProofDatabaseParser).getProofDatabase()
    }
}

object loadProofs {
  def apply(file: String) =
    try {
      (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream(file)))) with XMLProofDatabaseParser).getProofDatabase().proofs
    }
    catch {
      case _: Exception =>
        (new XMLReader(new InputStreamReader(new FileInputStream(file))) with XMLProofDatabaseParser).getProofDatabase().proofs
    }
}

object loadProver9Proof {
  def apply(filename: String):  (RobinsonResolutionProof, FSequent, FSequent) = Prover9.parse_prover9(filename)
}

object loadProver9LKProof {
  def apply(filename: String, forceSkolemization: Boolean = false): LKProof = {
    val (proof, endsequent, clauses) = Prover9.parse_prover9(filename)
    //println("skolemizing endsequent: "+endsequent)
    //val sendsequent = skolemize(endsequent)
    //val folsendsequent= FSequent(sendsequent.antecedent.map(x => hol2fol(x)), sendsequent.succedent.map(x => hol2fol(x)))
    //println("done: "+folsendsequent)
    if (!forceSkolemization && !containsStrongQuantifiers(endsequent)) {
      //println("End-sequent does not contain strong quantifiers!.")
      val closure = FSequent(endsequent.antecedent map (x => univclosure(x.asInstanceOf[FOLFormula])),
        endsequent.succedent map (x => existsclosure(x.asInstanceOf[FOLFormula])))

      Robinson2LK(at.logic.algorithms.resolution.fixSymmetry(proof, CNFn(endsequent.toFormula).map(c => FSequent(c.neg.map(f => f.asInstanceOf[FOLFormula]), c.pos.map(f => f.asInstanceOf[FOLFormula]))).toList), closure)
    } else {
      //if (forceSkolemization) println("Using initial clauses although end-sequent is skolemized")
      //else println("End-sequent does contain strong quantifiers, using initial clauses instead.")

      val fclauses: Set[FClause] = proof.nodes.map {
        case InitialClause(clause) => clause.toFClause
        case _ => FClause(Nil, Nil)
      }.filter((x: FClause) => x match {
        case FClause(Nil, Nil) => false;
        case _ => true
      })
      val clauses = fclauses.map(c => univclosure(FOLOr(c.neg.map(f => FOLNeg(f.asInstanceOf[FOLFormula])).toList ++ c.pos.map(f => f.asInstanceOf[FOLFormula]).toList)))
      val clauses_ = clauses.partition(_ match {
        case FOLNeg(_) => false;
        case _ => true
      })
      //val cendsequent = FSequent(clauses.toList, Nil)
      val cendsequent2 = FSequent(clauses_._1.toList, clauses_._2.map(_ match {
        case FOLNeg(x) => x
      }).toList)
      //println("new endsequent: "+cendsequent2)

      Robinson2LK(proof, cendsequent2)

    }
  }


  // What is this doing here?? C'mon people!!! FIXME: move this to an appropriate place!
  def containsStrongQuantifiers(fs: FSequent): Boolean =
    fs.antecedent.exists(x => containsStrongQuantifiers(x.asInstanceOf[FOLFormula], false)) ||
      fs.succedent.exists(x => containsStrongQuantifiers(x.asInstanceOf[FOLFormula], true))

  def containsStrongQuantifiers(f: FOLFormula, pol: Boolean): Boolean = f match {
    case FOLAtom(_, _) => false
    case FOLAnd(s, t) => containsStrongQuantifiers(s, pol) || containsStrongQuantifiers(t, pol)
    case FOLOr(s, t) => containsStrongQuantifiers(s, pol) || containsStrongQuantifiers(t, pol)
    case FOLImp(s, t) => containsStrongQuantifiers(s, !pol) || containsStrongQuantifiers(t, pol)
    case FOLNeg(s) => containsStrongQuantifiers(s, !pol)
    case FOLAllVar(x, s) => if (pol == true) true else containsStrongQuantifiers(s, pol)
    case FOLExVar(x, s) => if (pol == false) true else containsStrongQuantifiers(s, pol)
    case _ => throw new Exception("Unhandled case!")
  }

}

object loadLLK {
  def apply(filename: String) = {
    val tokens = HybridLatexParser.parseFile(filename)
    HybridLatexParser.createLKProof(tokens)
  }
}

object loadSLK {
  def apply( f: String ) = { sFOParser.parseProofFlat(new InputStreamReader(new FileInputStream(f))) }
}

object loadVeriTProof {
  def apply(fileName: String) = VeriTParser.getExpansionProof(fileName)
}

object exportXML {
  def apply(ls: List[LKProof], names: List[String], outputFile: String) = {
    val exporter = new LKExporter {}
    val pairs = ls.zip(names)
    scala.xml.XML.save(outputFile,
      <proofdatabase>
        <definitionlist/>
        <axiomset/>{pairs.map(p => exporter.exportProof(p._2, p._1))}<variabledefinitions/>
      </proofdatabase>, "UTF-8", true,
      scala.xml.dtd.DocType("proofdatabase", scala.xml.dtd.SystemID("http://www.logic.at/ceres/xml/5.0/proofdatabase.dtd"), Nil))
  }
}

object exportTPTP {
  def apply(ls: List[FSequent], filename: String) = {
    val file = new JBufferedWriter(new JFileWriter(filename))
    file.write(TPTPFOLExporter.tptp_problem(ls))
    file.close
  }
}

// TODO: Martin - please clean this up.
object exportSequentListLatex {
  def apply(ls: List[Sequent], outputFile: String) = {
    // maps original types and definitions of abstractions
    val sectionsPre = ("Types", getTypeInformation(ls).toList.sortWith((x, y) => x.toString < y.toString)) :: Nil

    val sections = try {
      // convert to fol and obtain map of definitons
      val imap = Map[HOLExpression, String]()
      val iid = new {
        var idd = 0;

        def nextId = {
          idd = idd + 1; idd
        }
      }
      /*
             val cs = ls.map(x => Sequent(
             x.antecedent.map(y => reduceHolToFol(y.asInstanceOf[HOLExpression],imap,iid).asInstanceOf[FOLFormula]),
             x.succedent.map(y => reduceHolToFol(y.asInstanceOf[HOLExpression],imap,iid).asInstanceOf[FOLFormula])
             ))*/
      ("Definitions", imap.toList.map(x => (x._1, FOLConst(x._2)))) :: sectionsPre
    }
    catch {
      case _: Exception => sectionsPre
    }
    (new FileWriter(outputFile) with SequentsListLatexExporter with HOLTermArithmeticalExporter).exportSequentList(ls map (_.toFSequent), sections).close
  }
}

object exportLabelledSequentListLatex {
  def apply(ls: List[LabelledSequent], outputFile: String) = {
    // maps original types and definitions of abstractions
    val sections = ("Types", getTypeInformation(ls).toList.sortWith((x, y) => x.toString < y.toString)) :: Nil
    (new FileWriter(outputFile) with LabelledSequentsListLatexExporter with HOLTermArithmeticalExporter).exportSequentList(ls, sections).close
  }
}


/*******************************************************************************
 * Automated Deduction
 ******************************************************************************/

object refuteFOL {
  def stream1: Stream[Command[Clause]] = Stream.cons(SequentsMacroCommand[Clause](
    SimpleRefinementGetCommand[Clause],
    List(VariantsCommand, DeterministicAndCommand[Clause](
      List(ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand(FOLUnificationAlgorithm), FactorCommand(FOLUnificationAlgorithm)),
      List(ParamodulationCommand(FOLUnificationAlgorithm))),
      SimpleForwardSubsumptionCommand[Clause](StillmanSubsumptionAlgorithmFOL),
      SimpleBackwardSubsumptionCommand[Clause](StillmanSubsumptionAlgorithmFOL),
      InsertResolventCommand[Clause]),
    RefutationReachedCommand[Clause]), stream1)

  def stream: Stream[Command[Clause]] = Stream.cons(SetTargetClause(FSequent(List(), List())), Stream.cons(SearchForEmptyClauseCommand[Clause], stream1))

  def apply(clauses: Seq[FSequent]): Option[ResolutionProof[Clause]] =
    new Prover[Clause] {}.
      refute(Stream.cons(SetClausesCommand(clauses), stream)).next
}

object refuteFOLI {
  def stream1: Stream[Command[Clause]] = Stream.cons(getTwoClausesFromUICommand[Clause](PromptTerminal.GetTwoClauses),
    Stream.cons(VariantsCommand,
      Stream.cons(DeterministicAndCommand[Clause]((
        List(ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand(FOLUnificationAlgorithm), FactorCommand(FOLUnificationAlgorithm)),
        List(ParamodulationCommand(FOLUnificationAlgorithm)))),
        Stream.cons(SimpleForwardSubsumptionCommand[Clause](StillmanSubsumptionAlgorithmFOL),
          Stream.cons(SimpleBackwardSubsumptionCommand[Clause](StillmanSubsumptionAlgorithmFOL),
            Stream.cons(InsertResolventCommand[Clause],
              Stream.cons(RefutationReachedCommand[Clause], stream1)))))))

  def stream: Stream[Command[Clause]] = Stream.cons(SetTargetClause(FSequent(List(), List())), Stream.cons(SearchForEmptyClauseCommand[Clause], stream1))

  def apply(clauses: Seq[FSequent]): Option[ResolutionProof[Clause]] =
    new Prover[Clause] {}.
      refute(Stream.cons(SetClausesCommand(clauses), stream)).next
}

object prover9 {
  //we have to refute
  def apply(filename: String): Option[RobinsonResolutionProof] = Prover9.refute(filename)

  def apply(clauses: Seq[FSequent]): Option[RobinsonResolutionProof] = Prover9.refute(clauses.toList)

  def apply(clauses: List[Sequent]): Option[RobinsonResolutionProof] = Prover9.refute(clauses map (_.toFSequent))

  def refuteTPTP(fn: String) = Prover9.refuteTPTP(fn)

  //get the ground substitution of the ground resolution refutation
  //the ground substitution is a list of pairs, it can't be a map ! The reason is : a clause can be used several times in the resolution refutation.
  //def getGroundSubstitution(rrp: RobinsonResolutionProof): List[(HOLVar, HOLExpression)] = getInstantiationsOfTheIndexedFOVars(rrp)
  def getProof(seq: FSequent): Option[LKProof] = {
    val p = new at.logic.provers.prover9.Prover9Prover()
    p.getLKProof(seq)
  }
}

object proveProp {
  def apply(seq: FSequent): Option[LKProof] = solve.solvePropositional(seq)
  def apply(f: HOLFormula): Option[LKProof] = apply(FSequent(Nil, f :: Nil))
}

object miniSATsolve {
  def apply(f: HOLFormula) = (new MiniSAT).solve(f)
}

object miniSATprove {
  def apply(f: HOLFormula) = (new MiniSAT).isValid(f)
}

object MaxSATsolve {
  def apply(hard: Set[FOLFormula], soft: Set[Tuple2[FOLFormula,Int]], maxsatsolver: MaxSATSolver = MaxSATSolver.QMaxSAT) = (new MaxSAT(maxsatsolver)).solvePWM(hard, soft)
}

/*******************************************************************************
 * Proof Theory
 ******************************************************************************/

// object regularize taken directly from imports

// object skolemize taken directly from imports

object lkTolksk {
  def apply(p: LKProof) = LKtoLKskc(p)
}

object eliminateCuts {
  def apply(proof: LKProof): LKProof = ReductiveCutElim(proof)
}

object extractInterpolant {
  def apply(p: LKProof, npart: Set[FormulaOccurrence], ppart: Set[FormulaOccurrence]) = ExtractInterpolant(p, npart, ppart)
}

object extractExpansionSequent {
  def apply(proof: LKProof): ExpansionSequent = herbrandExtraction.extractExpansionTrees(proof, true)
}

object compressExpansionTree {
  def apply(tree: ExpansionTree): MultiExpansionTree = compressQuantifiers(tree)
}

object compressExpansionSequent {
  def apply(sequent: ExpansionSequent): MultiExpansionSequent = compressQuantifiers(sequent)
}

object minimalExpansionSequents {
  def apply(sequent: ExpansionSequent, prover: abstractProver): List[ExpansionSequent] = minimalExpSeq(sequent, prover).toList
}

/*******************************************************************************
 * Cut-Elimination by Resolution
 ******************************************************************************/

object extractStruct {
  def apply(p: LKProof) =
    StructCreators.extract(p)

  def apply(p: LKProof, cutformula_condition: HOLFormula => Boolean) =
    StructCreators.extract(p, cutformula_condition)

  def apply(p: LKProof, cut_occs: Set[FormulaOccurrence]) =
    StructCreators.extract(p, cut_occs)
}

object structToClausesList {
  def apply(s: Struct) = at.logic.transformations.ceres.clauseSets.StandardClauseSet.transformStructToClauseSet(s)
}

object structToLabelledClausesList {
  def apply(s: Struct) = at.logic.transformations.ceres.clauseSets.StandardClauseSet.transformStructToClauseSet(s)
}


/*******************************************************************************
 * Proof Schemata
 ******************************************************************************/

object unfoldProof {
  def apply(name: String, i: Int): LKProof = applySchemaSubstitution2(name, i, List())
}


/*******************************************************************************
 * Cut-Introduction
 ******************************************************************************/

object cutIntro {
  
  def apply () = {
    println("There are three available methods for introducing cut(s):")
    println("- one_cut_one_quantifier")
    println("- one_cut_many_quantifiers")
    println("- many_cuts_one_quantifier")
    println("See documentation for more details.")
  }

  def one_cut_one_quantifier (p: LKProof) = CutIntroduction.one_cut_one_quantifier (p, true)
  def one_cut_one_quantifier (es: ExpansionSequent, hasEquality: Boolean) = CutIntroduction.one_cut_one_quantifier (es, hasEquality, true)

  def one_cut_many_quantifiers (p: LKProof) = CutIntroduction.one_cut_many_quantifiers (p, true)
  def one_cut_many_quantifiers (es: ExpansionSequent, hasEquality: Boolean) = CutIntroduction.one_cut_many_quantifiers (es, hasEquality, true)

  def many_cuts_one_quantifier (p: LKProof) = CutIntroduction.many_cuts_one_quantifier (p, true)
  def many_cuts_one_quantifier (es: ExpansionSequent, hasEquality: Boolean) = CutIntroduction.many_cuts_one_quantifier (es, hasEquality, true)
}

object extractTerms {
  def apply(p: LKProof) = {
    val ts = TermsExtraction(p)
    println("\nTerm set: {" + ts.set + "}")
    println("Size of term set: " + ts.set.size)
    ts
  }

  def apply(ep: ExpansionSequent) = {
    val ts = TermsExtraction(ep)
    println("\nTerm set: {" + ts.set + "}")
    println("Size of term set: " + ts.set.size)
    ts
  }
}

object computeGrammars {
  def apply(terms: TermSet) = {
    val g = ComputeGrammars(terms, new UnboundedVariableDelta())
    g.size match {
      case 0 => throw new Exception("No grammars found for this list of terms.")
      case n => println(n + " grammars found.\n"); g
    }
  }
}

object seeNFirstGrammars {
  def apply(lst: List[Grammar], n: Int) = {
    println("\n");
    for (i <- 0 to n - 1) {
      println(i + ". " + lst(i) + "\n(size = " + lst(i).size + ")\n")
    }
    println("\nNote that the function symbols 'tuplei' are inserted by the system as part of the algorithm.")
  }
}

object generateExtendedHerbrandSequent {
  def apply(es: Sequent, g: Grammar) = new ExtendedHerbrandSequent(es, g)
}

object computeCanonicalSolution {
  def apply(s: Sequent, g: Grammar) = {
    println("Note that the clauses that do not contain the eigenvariable were already removed.");
    CutIntroduction.computeCanonicalSolution(s, g)
  }
}

object minimizeSolution {
  def apply(ehs: ExtendedHerbrandSequent) = {
    println("Previous solution: " + ehs.cutFormula)
    val new_ehs = MinimizeSolution(ehs, new at.logic.algorithms.cutIntroduction.DefaultProver())
    println("Improved solution: " + new_ehs.cutFormula)
    new_ehs
  }
}

object buildProofWithCut {
  def apply(ehs: ExtendedHerbrandSequent) = {
    val p = CutIntroduction.buildProofWithCut(ehs, new at.logic.algorithms.cutIntroduction.DefaultProver())
    p.flatMap(x => Some(CleanStructuralRules(x)))
  }
}

/*******************************************************************************
 * Visualization
 ******************************************************************************/

object prooftool {
  def apply(x: AnyRef) = Main.display("From CLI", x)
}

/*******************************************************************************
 * General
 ******************************************************************************/

object help {
  def apply() = {
    val msg =
      """
        | Available commands:
        |
        | Parsing:
        |   parseFOL: String => FOLFormula - example: "Forall x Imp P(x,f(x)) Exists y P(x,y)"
        |   parseHOL: String => HOLExpression
        |   parseLISP: String => List[SExpression]
        |   parseLLKExp: String => HOLExpression - example: "var x,y: i>o; (\\ x => (\\y => (x=y) ))"
        |   parseLLKFormula: String => HOLFormula -  example: "const P : i>o; const Q : i>i>o; var x,y:i; (all x (P(x) -> (exists y Q(x,y) )))"
        |   parseProver9: String => FOLFormula - example: "(all x (P(x,f(x)) -> (exists y P(x,y))))"
        |
        | Formulas / Sequents / Expressions:
        |   hol2folpure: HOLExpression => FOLExpression, HOLFormula => FOLFormula - transformation of scala type
        |   toClauses: HOLFormula => Set[FClause] - the clause set representation of the given formula
        |   deleteTautologies: List[FSequent] => List[FSequent] - remove all FSequents of form ..., A |- A, ...
        |   removeSubsumed: List[FSequent] => List[FSequent] - remove all subsumed FSequents
        |   unitResolve: List[FSequent] => List[FSequent] - normalization under unit resolution
        |
        | File Input / Output:
        |   loadProofDB: String => ProofDatabase - load proofdatabase from xml file
        |   loadProofs: String => List[(String, LKProof)] - load proofs from xml file as name/value pairs
        |   loadProver9Proof: String => (RobinsonResolutionProof, FSequent) - load a proof in the ivy proof checker format and extract its endsequent
        |   loadProver9LKProof: String => LKProof - load a proof in the ivy proof checker format and convert it to a LK Proof
        |   loadLLK : String => LKProof - load a proof in the LLK format from given filename
        |   loadSLK: String => Map[String, Tuple2[LKProof, LKProof]] - loads an SLK file
        |   loadVeriTProof : String => ExpansionSequent - loads a veriT proof in the form of an expansion proof.
        |   exportXML: List[Proof], List[String], String => Unit
        |   exportTPTP: List[Proof], List[String], String => Unit
        |   exportSequentListLatex: List[Sequent], String => Unit - write clause set to output file
        |   exportLabelledSequentListLatex: List[LabelledSequent], String => Unit
        |
        | Automated Deduction:
        |   refuteFOL: Seq[Clause] => Option[ResolutionProof[Clause]] - call internal resolution prover TAP
        |   refuteFOLI: Seq[Clause] => Option[ResolutionProof[Clause]] - simple interactive refutation
        |   prover9: List[Sequent],Seq[Clause] => Option[ResolutionProof[Clause]] - call prover9
        |   prover9: String => Option[ResolutionProof[Clause]] - call prover9 on given Ladr file
        |   prover9.refuteTPTP:  String => Option[ResolutionProof[Clause]] - call prover9 on given TPTP file
        |   prover9.getProof:  FSequent => Option[LKProof] - prove a sequent with prover9
        |   proveProp: FSequent => Option[LKProof] - tableau-like proof search for propositional logic
        |   miniSATsolve: HOLFormula => Option[Interpretation] - obtain a model for a quantifier-free formula using MiniSAT
        |   miniSATprove: HOLFormula => Boolean - check if a quantifier-free formula is valid using MiniSAT
        |   MaxSATsolve: (Set[FOLFormula], Set[Tuple2[FOLFormula,Int]]) => Option[Interpretation] - obtain a model for a set of quantifier-free formulas (interpreted as hard constraints) and a set of tuples of quantifier-free formulas (interpreted as soft constraints) w.r.t. provided weights using qmaxsat
        |
        | Proof Theory:
        |   regularize: LKProof => LKProof - regularize the given LK proof
        |   skolemize: LKProof => LKProof - skolemize the input proof
        |   lkTolksk: LKProof => LKProof
        |   eliminateCuts: LKProof => LKProof - eliminate cuts by Gentzen's method
        |   extractInterpolant: ( LKProof, Set[FormulaOccurrence], Set[FormulaOccurrence] ) => HOLFormula - extract propositional Craig interpolant
        |   extractExpansionSequent: LKProof => ExpansionSequent - extract the expansion trees of all formulas in the end sequent from a skolemized proof.
        |   compressExpansionTree: ExpansionTree => MultiExpansionTree - compress the quantifiers in the tree using vectors for the terms.
        |   compressExpansionSequent: ExpansionSequent => MultiExpansionSequent - compress the quantifiers in the trees of the sequent using vectors for the terms.
        |   minimalExpansionSequents: ( ExpansionSequent, Prover ) => List[ExpansionSequent] - find all minimal expansion sequents below the given one that are still valid according to the prover.
        |   printProofStats: LKProof => Unit
        |
        | Cut-Elimination by Resolution:
        |   extractStruct: LKProof => Struct
        |   structToClausesList: Struct => List[Sequent]
        |   structToLabelledClausesList: Struct => List[LabelledSequent]
        |
        | Proof Schemata:
        |   unfoldProof: (String, Int) => LKProof
        |
        | Cut-Introduction:
        |   cutIntro.one_cut_one_quantifier (LKProof) => LKProof - Introduces one cut with one quantifier to an LK proof.
        |   cutIntro.one_cut_many_quantifiers (LKProof) => LKProof - Introduces one cut with an arbitrary number of quantifiers to an LKProof.
        |   cutIntro.many_cuts_one_quantifier (LKProof) => List[FOLFormula] - Introduces many cuts with one quantifier each to an LKProof. Returns the cut-formulas.
        |   ncutIntro: (LKProof,Int,[MaxSATSolver]) => Option[List[FOLFormula]] - performs cut introduction for a maximum of n (Int) cuts. (optional: MaxSATSolver {QMaxSAT, ToySAT, ToySolver}")"
        |   extractTerms: LKProof => FlatTermSet - extract the witnesses of the existential quantifiers of the end-sequent of a proof
        |   computeGrammars: FlatTermSet => List[Grammar] - computes all the grammars of a given list of terms (returns a list ordered by symbolic complexity)
        |   seeNFirstGrammars: List[Grammar], Int => Unit - prints the first n grammars from a list
        |   generateExtendedHerbrandSequent: Sequent, Grammar => ExtendedHerbrandSequent - generates the Extended Herbrand Sequent from an end-sequent of a proof and a grammar
        |   computeCanonicalSolution: Sequent, Grammar => FOLFormula - computes the canonical solution for the cut-introduction problem
        |   minimizeSolution: ExtendedHerbrandSequent => ExtendedHerbrandSequent - minimizes the solution associated with the extended Herbrand sequent returning another Herbrand sequent with this minimal solution
        |   buildProofWithCut: ExtendedHerbrandSequent => LKProof - builds a proof with one cut based on the extended Herbrand sequent
        |
        | Visualization:
        |   prooftool: LKProof => Unit - visualize proof in prooftool
        |
        | General:
        |   help    : this help text
        |   copying : print redistribution conditions
        |   license : print the text of GNU General Public License
      """.stripMargin

      println(msg)
  }
}

// copying/license call taken from imports


/*******************************************************************************
 * 
 * all calls below are either not documented in the help screen or not categorized
 *
 * TODO: clean this up!
 *
 ******************************************************************************/


object printProofStats {
  def apply(p: LKProof) = {
    val stats = getStatistics(p)
    val total = rulesNumber(p)
    val quant = quantRulesNumber(p)
    val weakQuant = weakQuantRulesNumber(p)
    println("------------- Statistics ---------------")
    println("Cuts: " + stats.cuts)
    println("Number of quantifier inferences: " + quant)
    println("Number of inferences: " + total)
    println("Quantifier complexity: " + weakQuant)
    println("----------------------------------------")
  }
}

/** ****************** CERES operations *************************/

object simplifyStruct {
  def apply(s: Struct) = SimplifyStruct.apply(s)
}

object refuteClauseList {
  def apply(cl: List[Sequent]): Option[RobinsonResolutionProof] = prover9(cl)
}

object computeProjections {
  def apply(p: LKProof): Set[LKProof] = Projections(p)

  def apply(p: LKProof, pred: HOLFormula => Boolean): Set[LKProof] = Projections(p, pred) // introduced in lambda calc merge
}

object computeGroundProjections {
  def apply(projections: Set[LKProof], groundSubs: List[(HOLVar, HOLExpression)]): Set[LKProof] = {
    groundSubs.map(subs => projections.map(pr => renameIndexedVarInProjection(pr, subs))).flatten.toSet
  }
}

object CERESomega extends ceres_omega
object foCERES extends CERESR2LK
object foCERESground extends CERES

object buildACNF {
  def apply(ref: LKProof, projs: Set[LKProof], es: FSequent) = ACNF(ref, projs, es)
}

/******************** Proof loaders *************************/


object loadPrime {
  def apply(i: Int) = {
    val p2 = loadProofs("prime1-" + i + ".xml").head._2
    val p2_ = regularize(skolemize(p2))
    val cs2 = structToClausesList(extractStruct(p2_))
    /* removeDuplicates does not exist anymore
    val cs2_ = removeDuplicates(deleteEquationalTautologies(deleteTautologies(cs2 map ((x: Sequent) => x.toFSequent))))
    writeLatex(cs2_ map (fsequent2sequent.apply), "cs" + i + ".tex")
    exportTPTP(cs2_, "cs" + i + ".p")
    (p2, p2_, cs2, cs2_)
    */
  }

}

object exportVeriT {
  def apply(f: FSequent, fileName: String) = VeriTExporter(f, fileName)
}

object exportLLK {
  def apply(lkproof : LKProof, enable_latex : Boolean) = HybridLatexExporter(lkproof,enable_latex)
  def apply(lkproof : LKProof) = HybridLatexExporter(lkproof,true)
  def apply(lkproof : LKProof, filename:String) = {
    val file = new JBufferedWriter(new JFileWriter(filename))
    file.write(HybridLatexExporter(lkproof, true))
    file.close
  }
}

object escape_underscore {
  def escape_constants(r:RobinsonResolutionProof, fs:List[FSequent]) : (RobinsonResolutionProof,List[FSequent]) = {
    val names : Set[(Int,String)] = r.nodes.map( _.asInstanceOf[RobinsonResolutionProof].root.occurrences.map(fo =>
      getArityOfConstants(fo.formula.asInstanceOf[FOLFormula]))).flatten.flatten

    val pairs : Set[(String, (Int,String))] = (names.map((x:(Int,String)) =>
      (x._2, ((x._1, x._2.replaceAll("_","\\\\_")))   ))
      )

    val mapping = NameReplacement.emptySymbolMap ++ (pairs)

    (NameReplacement(r, mapping), fs.map(f => NameReplacement(f,mapping)))
  }

}


/*************************************************************/

object deleteEquationalTautologies {
  //private val counter = new {private var state = 0; def nextId = { state = state +1; state}}
  //private val emptymap = MMap[HOLExpression, String]()
  //val acu = new MulACUEquality(List("+","*") map (_), List("0","1") map (_))

  def apply(ls: List[FSequent]) = ls.filterNot(_._2 exists ((f: HOLFormula) =>
    f match {
      case Atom(c : HOLConst, List(x, y)) => c.sym == "=" && x == y
      case Atom(c : HOLVar, List(x, y)) => c.sym == "=" && x == y
      case _ => false
    }))

  /* FIXME: depends on EequalityA which is not adapted to the new lambda calculus
    def isEquationalTautology( e: EequalityA, f: HOLFormula) = f match {
      case Atom(ConstantStringSymbol(sym), List(x,y)) =>
        val s : FOLTerm = reduceHolToFol(x, emptymap, counter ).asInstanceOf[FOLTerm]
        val t : FOLTerm = reduceHolToFol(y, emptymap, counter ).asInstanceOf[FOLTerm]
        sym == "=" && e.word_equalsto (s,t )
        case _ => false
    }

    def isEquationalSequentTautology(e : EequalityA, s:FSequent) = {
      s._1 exists ((f: HOLFormula) =>
          s._2 exists  ((g: HOLFormula) =>
            e.reequal_to( reduceHolToFol(f, emptymap, counter), reduceHolToFol(g,emptymap, counter))
            ))
    }

    def apply(e : EequalityA ,ls : List[FSequent]) = (ls.filterNot( _._2 exists ((f:HOLFormula) => isEquationalTautology(e,f) ))) filterNot (isEquationalSequentTautology(e,_))
    */
}

object fsequent2sequent {
  def f2focc(f: HOLFormula) = new FormulaOccurrence(f, Nil, defaultFormulaOccurrenceFactory)

  def apply(s: FSequent) = Sequent(s._1 map f2focc, s._2 map f2focc)
}

/*
  object normalizeClauses {
    //def apply(ls: List[Sequent]) = sequentNormalize(ls map (_.toFSequent))
    def apply(ls: List[FSequent]) = sequentNormalize(ls)
  }
  */

object Robinson2Ral extends RobinsonToRal {
  override def convert_formula(e:HOLFormula) : HOLFormula = recreateWithFactory(e,HOLFactory).asInstanceOf[HOLFormula]
  override def convert_substitution(s:HOLSubstitution) : HOLSubstitution = {
    recreateWithFactory(s, HOLFactory, convert_map).asInstanceOf[HOLSubstitution]
  }

  //TODO: this is somehow dirty....
  def convert_map(m : Map[Var,LambdaExpression]) : LambdaSubstitution = HOLSubstitution(m.asInstanceOf[Map[HOLVar,HOLExpression]])
}

object GenerateRobinson2Ral {
  def apply(hol2folscope : collection.mutable.Map[LambdaExpression, StringSymbol]) : RobinsonToRal = new RobinsonToRal {
    override def convert_formula(e:HOLFormula) : HOLFormula = {

      recreateWithFactory(e,HOLFactory).asInstanceOf[HOLFormula]
    }
    override def convert_substitution(s:HOLSubstitution) : HOLSubstitution = {
      recreateWithFactory(s, HOLFactory, convert_map).asInstanceOf[HOLSubstitution]
    }

    //TODO: this is somehow dirty....
    def convert_map(m : Map[Var,LambdaExpression]) : LambdaSubstitution = HOLSubstitution(m.asInstanceOf[Map[HOLVar,HOLExpression]])
  }
}

object applyFactoring extends factoring

object rule_isomorphic extends LKSKrule_isomorphic //this subsumes the LK version

object exportLatex {
  def apply(list: List[FSequent], fn: String) = {
    val writer = (new FileWriter(fn) with SequentsListLatexExporter with HOLTermArithmeticalExporter)
    writer.exportSequentList(list, Nil).close
  }
}

object exportTHF {
  def apply(ls: List[FSequent], filename: String) = {
    val file = new JBufferedWriter(new JFileWriter(filename))
    file.write(TPTPHOLExporter(ls))
    file.close
  }
}


/*
  object exportLLK {
    def apply(lkproof : LKProof, enable_latex : Boolean) = HybridLatexExporter(lkproof,enable_latex)
    def apply(lkproof : LKProof) = HybridLatexExporter(lkproof,true)
    def apply(lkproof : LKProof, filename:String) = {
      val file = new JBufferedWriter(new JFileWriter(filename))
      file.write(HybridLatexExporter(lkproof, true))
      file.close
    }
  }

  object createEquality {
    def apply(fs : List[String], cs : List[String]) =
      new MulACUEquality(fs map (new ConstantStringSymbol(_)), cs map (new ConstantStringSymbol(_)))

      def apply(fs : List[String]) =
      new MulACEquality(fs map (new ConstantStringSymbol(_)))
  }
  */

object parse {

  private class CLIParserFOL(input: String) extends StringReader(input) with SimpleFOLParser

  private class CLIParserHOL(input: String) extends StringReader(input) with SimpleHOLParser

  private class CLIParserSchema(input: String) extends StringReader(input) with SchemaFormulaParser

  def fol(string: String) = {
    new CLIParserFOL(string).getTerm.asInstanceOf[FOLFormula]
  }

  def folterm(string: String) = {
    new CLIParserFOL(string).getTerm.asInstanceOf[FOLTerm]
  }

  //this is redundant
  def hol(string: String) = {
    new CLIParserHOL(string) getTerm
  }

  def sfo(string: String) = {
    new CLIParserSchema(string) getTerm
  }

  def p9(string: String, use_ladr: Boolean = true) = {
    if (use_ladr)
      Prover9TermParserLadrStyle.parseFormula(string)
    else
      Prover9TermParser.parseFormula(string)
  }

  def p9term(string: String, use_ladr: Boolean = true) = {
    if (use_ladr)
      Prover9TermParserLadrStyle.parseTerm(string)
    else
      Prover9TermParser.parseTerm(string)
  }

  def slk(file: String) = {
    sFOParser.parseProofFlat(new InputStreamReader(new FileInputStream(file)))
  }


  def slkh(file: String) = {
    sFOParserCNT.parseProofFlat(new InputStreamReader(new FileInputStream(file)))
  }

  def ScholParse(file: String) = {
    SCHOLParser.parseProofFlat(new InputStreamReader(new FileInputStream(file)))
  }

  def lisp(string: String) = {
    SExpressionParser.parseString(string)
  }

  def hlkexp(s: String): HOLExpression = HLKHOLParser.parse(s)

  def hlkformula(s: String): HOLFormula = {
    val exp = HLKHOLParser.parse(s)
    require(exp.isInstanceOf[HOLFormula], "Expression is no HOL Formula!")
    exp.asInstanceOf[HOLFormula]
  }

  def program(s: String): Program = ProgramParser.parseProgram(s)

  def help() = {
    println("fol: String => FOLFormula")
    println("folterm: String => FOLTerm")
    println("p9: String => FOLFormula")
    println("hlkexp: String => HOLExpression")
    println("hlkformula: String => HOLFormula")
    println("hol: String => HOLExpression")
    println("slk: String => Map[String, Tuple2[LKProof, LKProof]]")
  }
}


/*****************************************************************************************/

object eliminateInstaces {
  def apply(p: RobinsonResolutionProof) = InstantiateElimination.apply(p)
}

object replay {

  private class MyParser(str: String) extends StringReader(str) with SimpleResolutionParserFOL

  def apply1(clauses: String): Option[ResolutionProof[Clause]] = {
    apply(new MyParser(clauses).getClauseList)
  }

  def apply(clauses: Seq[FSequent]): Option[ResolutionProof[Clause]] =
    try {
      new Prover[Clause] {}.
        refute(Stream(SetTargetClause(FSequent(List(), List())), Prover9InitCommand(clauses), SetStreamCommand())).next
    } catch {
      case e: IOException => throw new IOException("Prover9 is not installed: " + e.getMessage())
    }

  def apply(clauses: List[Sequent]): Option[ResolutionProof[Clause]] =
    try {
      new Prover[Clause] {}.
        refute(Stream(SetTargetClause(FSequent(List(), List())), Prover9InitCommand((clauses map ((x: Sequent) => x.toFSequent)).toList), SetStreamCommand())).next
    } catch {
      case e: IOException => throw new IOException("Prover9 is not installed: " + e.getMessage())
    }
}

object Robinson2LK {
  def apply(resProof: ResolutionProof[Clause]): LKProof = RobinsonToLK(resProof.asInstanceOf[RobinsonResolutionProof])

  def apply(resProof: ResolutionProof[Clause], seq: FSequent): LKProof = RobinsonToLK(resProof.asInstanceOf[RobinsonResolutionProof], seq)
}


object format {
  def apply(p: ResolutionProof[Clause]) = asHumanReadableString(p)

  def asHumanReadableString(p: ResolutionProof[Clause]) = Formatter.asHumanReadableString(p)

  def asGraphVizString(p: ResolutionProof[Clause]) = Formatter.asGraphViz(p)
  def asGraphVizString(p: LKProof) = Formatter.asGraphViz(p)

  def asXml(p:LKProof) = Formatter.asXml(p)

  def asTex(p: ResolutionProof[Clause]) = Formatter.asTex(p)

  def llk(f: HOLExpression, latex: Boolean = false): String = HybridLatexExporter.getFormulaString(f, true, latex)

  def llk(f: FSequent, latex: Boolean): String = "\\SEQUENT" + HybridLatexExporter.fsequentString(f, latex)

  def llk(f: FSequent): String = llk(f, false)

  def tllk(f: HOLExpression, latex: Boolean = false) = {
    val (ctypes, vtypes) = HybridLatexExporter.getTypes(f, HybridLatexExporter.emptyTypeMap, HybridLatexExporter.emptyTypeMap)

    val fs = HybridLatexExporter.getFormulaString(f, true, latex)

    val cs = ctypes.foldLeft("")((str, p) => str + "const " + p._1 + " : " + HybridLatexExporter.getTypeString(p._2) + ";")
    val vs = vtypes.foldLeft("")((str, p) => str + "var " + p._1 + " : " + HybridLatexExporter.getTypeString(p._2) + ";")
    cs + vs + fs
  }

  /*
  def dot[T](p:AGraph[T]) = "digraph resproof {\n graph [rankdir=TB]; node [shape=box];\n" + dot1(p:AGraph,0, Map[AGraph, Int]()) + "\n}"

  def dot1[T](p:AGraph, idx : Int, map : Map[AGraph,Int]) : (String, Int) =
    if (map contains p) ("", idx) else p match {
      case LeafAGraph(_) =>
        ""

    }

    */
}


object mapProof extends map_proof {
  val help =
    """mapProof(l : LKProof, fun : HOLExpression => HOLExpression) : LKProof
      |
      |Applies the function fun to every formula in the proof. This can result in incorrect proofs.
    """.stripMargin
}

/*
object rename {
  val help =
    """
      | rename(exp: HOLExpression, map: SymbolMap): HOLExpression
      | rename(fs: FSequent, map: SymbolMap) : HOLExpression
      | rename(p: RobinsonResolutionProof, map: SymbolMap): RobinsonResolutionProof
      |
      | The symbol map is a map from oldname:String to pairs of (a:Int,newname). Applying
      | rename will replace every occurrence of a symbol with oldname and arity a by newname.
    """.stripMargin
  def apply(exp: HOLExpression, map: NameReplacement.SymbolMap): HOLExpression = NameReplacement(exp, map)

  def apply(fs: FSequent, map: NameReplacement.SymbolMap) = NameReplacement(fs, map)

  def apply(p: RobinsonResolutionProof, map: NameReplacement.SymbolMap): RobinsonResolutionProof = NameReplacement(p, map)
}

*/

//TODO: find a better name for all this stuff
object ntape {
  val p = loadLLK("algorithms/llk/src/test/resources/tape3.llk");
  val elp = regularize(definitionElimination(p, "TAPEPROOF"));
  val selp = at.logic.transformations.skolemization.lksk.LKtoLKskc(elp);

  //val (rp,es) = loadProver9Proof("ntape.out")


  def apply(filename: String = "algorithms/hlk/src/test/resources/tape3.llk", proofname: String = "TAPEPROOF")
  : (ExtendedProofDatabase, List[FSequent], List[FSequent], Struct, replaceAbstractions.ConstantsMap) = {
    println("Loading proof database " + filename)
    val p = loadLLK(filename)
    println("Eliminating definitions:")
    val elp = definitionElimination(p, proofname)
    println("Converting to LKskc")
    val selp = LKtoLKskc(regularize(elp))
    println("Extracting struct")
    val struct = extractStruct(selp, x => containsQuantifierHOL(x))
    val (full, fol, hol, csyms) = css(struct)
    println("Simplifying clauseset")
    val ax1 = FSequent(Nil, List(parse hlkformula "var x:i; const < : i>i>o; const 1 : i; const + : i>i>i; x<x+1"))
    val ax2 = FSequent(Nil, List(parse hlkformula "var x,y,z:i; const + : i>i>i; x+(y+z)=(x+y)+z"))
    val removed = subsumedClausesRemovalHOL(deleteTautologies(applyFactoring(ax1 :: ax2 :: full)))
    val (cm, qhol) = replaceAbstractions(removed)
    cm.toList map (x =>
      println(x._2 + " & " + HybridLatexExporter.getFormulaString(x._1.asInstanceOf[HOLExpression], true, true) + "\\\\"))


    val qf: List[FSequent] = selp.nodes.toList.flatMap(_ match {
      case x@ForallSkRightRule(p, r, a, f, t) => FSequent(a.formula :: Nil, f.formula :: Nil) :: Nil;
      case x@ExistsSkLeftRule(p, r, a, f, t) => FSequent(a.formula :: Nil, f.formula :: Nil) :: Nil;
      case _ => Nil;
    })

    (p, qhol, qf, struct, cm)
  }

  val rrename = NameReplacement.emptySymbolMap ++ List(("s25", (2, "s_{25}")), ("s9", (2, "s_{9}")),
    ("q1", (0, "q_{1}")), ("q2", (0, "q_{2}")),
    ("s10", (1, "s_{10}")), ("s26", (1, "s_{26}")))


  def convert(rp: RobinsonResolutionProof) = NameReplacement(rp, rrename)

  def axioms(rp: RobinsonResolutionProof) = {
    val rrp = NameReplacement(rp, rrename)
    val lkp = RobinsonToLK(rrp, FSequent(Nil, Nil), ((c: FClause) => Axiom(c.neg, c.pos)))
    val axioms = lkp.nodes.flatMap(_ match {
      case a@Axiom(_) => List(a.root.toFSequent);
      case _ => List[FSequent]()
    })
    val cmap = Map[String, TA](("q_{1}", Ti -> To), ("q_{2}", Ti -> To))
    val holaxioms = axioms.map(x => recreateWithFactory(x, HOLFactory)).toList

    val folaxs = holaxioms.flatMap(_.formulas).filter(_.factory != HOLFactory)
    require(folaxs.isEmpty, "HOL Conversion didn't work on " + folaxs)
    val raxioms = holaxioms.map(x => changeTypeIn(x, cmap))

    (lkp, raxioms)
  }

  val subterm1 = parse hlkexp """const s_{9},s_{25}:(i>o)>(i>i); const s_{10},s_{26}:(i>o)>i;
                                  const q_{1},q_{2}:i>o; const +:i>(i>i); const 1:i;
                                  (((1 + s_{25}(q_{2}, s_{26}(q_{2}))) + 1) + 1) + s_{9}(q_{1}, s_{10}(q_{1}))"""
  val subterm2 = parse hlkexp """const s_{9},s_{25}:(i>o)>(i>i); const s_{10},s_{26}:(i>o)>i;
                                  const q_{1},q_{2}:i>o; const +:i>(i>i); const 1:i;
                                  (((1 + s_{9}(q_{1}, s_{10}(q_{1}))) + 1) + 1) + s_{25}(q_{2}, s_{26}(q_{2}))"""

  val subvars1 = List(1, 3).map(x => parse hlkexp "var \\alpha_{" + x + "}:i; \\alpha_{" + x + "}")
  val subvars2 = List(4, 6).map(x => parse hlkexp "var \\alpha_{" + x + "}:i; \\alpha_{" + x + "}")
  val sub = HOLSubstitution(subvars1.map(x => (x.asInstanceOf[HOLVar], subterm1)) ++
    subvars2.map(x => (x.asInstanceOf[HOLVar], subterm2)))

  def findProj(proof: LKProof, axioms: List[FSequent]) = {
    val es = proof.root.toFSequent
    val pref = Projections.lksk_reflexivity_projection(proof)
    println("Calculated projection to reflexivity: " + pref.root.toFSequent.diff(proof.root.toFSequent))
    val proj = pref :: (Projections(proof, x => containsQuantifierHOL(x)).toList)
    println("Total projections size: " + proj.size)
    val pproj = proj.map(x => (x.root.toFSequent.diff(es), x))
    val still = StillmanSubsumptionAlgorithmHOL

    val subsumed = axioms.map(x => (x, pproj.find(y => still.subsumes(y._1, x))))
    val (can_subsume, cant_subsume) = subsumed.partition(_._2.nonEmpty)
    val substitutions = can_subsume.map(x => {
      val (ax, Some((clause, proof))) = x
      (still.subsumes_by(clause, ax).get, proof)
    })

    (substitutions, cant_subsume)
  }

  def hasWeakHOLRule(p: LKProof) = p.nodes.asInstanceOf[Set[LKProof]].filter(_ match {
    case ForallSkLeftRule(p, r, aux, f, t) if t.exptype != Ti => true;
    case ExistsSkRightRule(p, r, x, f, t) if t.exptype != Ti => true;
    case _ => false
  })

  def sub_mising(p: LKProof, sub: HOLSubstitution) = {
    val (s, _) = applySubstitution(p, sub)
    val w = hasWeakHOLRule(s).toList
    val winf = w.map(_ match {
      case ForallSkLeftRule(_, _, a, m, e) => (a, m, e)
      case ExistsSkRightRule(_, _, a, m, e) => (a, m, e)
    })

    winf
  }

  def printWorking(working: List[(HOLSubstitution, LKProof)]) = {
    val workingsubs = working.foldLeft(Map[LKProof, List[HOLSubstitution]]())((map, pair) => {
      val l = map.getOrElse(pair._2, List());
      map + ((pair._2, pair._1 :: l))
    })
    workingsubs.map(x => {
      println(format.llk(x._1.root.toFSequent.diff(selp.root.toFSequent)));
      println();
      x._2.map(z =>
        println(z.holmap.map(y =>
          format.llk(y._1) + " <- " + format.llk(y._2)).mkString("Sub={", ", ", "}")
        ));
      println()
    })
  }


}

object proofs {
  def simple1(): LKProof = {
    val x = HOLVar("x", Ti)
    val y = HOLVar("y", Ti)
    val a = HOLVar("a", Ti)
    val b = HOLVar("b", Ti)
    val Rab = Atom(HOLConst("R", Ti -> (Ti -> To)), a :: b :: Nil)
    val exyRay = ExVar(y, Atom(HOLConst("R", Ti -> (Ti -> To)), a :: y :: Nil))
    val allxexyRxy = AllVar(x, ExVar(y, Atom(HOLConst("R", Ti -> (Ti -> To)), x :: y :: Nil)))
    val ax = Axiom(Rab :: Nil, Rab :: Nil)
    val r1 = ExistsRightRule(ax, ax.root.succedent(0), exyRay, b)
    val r2 = ExistsLeftRule(r1, r1.root.antecedent(0), exyRay, b)
    val r3 = ForallLeftRule(r2, r2.root.antecedent(0), allxexyRxy, a)
    val proof: LKProof = ForallRightRule(r3, exyRay, allxexyRxy, a)
    proof
  }
}

object lkproof {
  def cutrules(p: LKProof): Set[LKProof] = p.nodes.flatMap(_ match {
    case c@CutRule(_, _, _, _, _) =>
      List(c.asInstanceOf[LKProof])
    case _ =>
      Nil
  }
  )

  def cutoccurrences(p: LKProof) = p.nodes.flatMap(_ match {
    case CutRule(_, _, _, a1, a2) =>
      List(a1, a2)
    case _ =>
      Nil
  }
  )

  def cutformulas(p: LKProof) = cutoccurrences(p).map(_.formula)

  def axiomrules(p: LKProof): Set[LKProof] = p.nodes.flatMap(_ match {
    case a@Axiom(_) =>
      List(a.asInstanceOf[LKProof])
    case _ =>
      Nil
  }
  )

  def axiomoccurrences(p: LKProof) = p.nodes.flatMap(_ match {
    case Axiom(fs) =>
      fs.occurrences
    case _ =>
      Nil
  }
  )

  def axiomformulas(p: LKProof) = axiomoccurrences(p).map(_.formula)
}


/* FIXME: Huet's algorithm is not yet adapted to the new lambda calculus
  object huet {

    class MyParser(input: String) extends StringReader(input) with SimpleHOLParser

      def apply(l: List[Tuple2[String, String]]) : NDStream[Substitution[HOLExpression]] = {
        val termargs : List[Tuple2[HOLExpression,HOLExpression]] = l map (
            (arg : Tuple2[String,String]) =>
            (parse hol arg._1, parse hol arg._2)
            )
          Huet(termargs)
      }
    def apply(s1: String, s2: String) : NDStream[Substitution[HOLExpression]] = apply(Tuple2(s1,s2)::Nil)
  }
  */

object normalizeSub {

  def apply(sub: HOLSubstitution): Unit = {
    sub.holmap.foreach(x => println("\n<" + (HOLBetaReduction.betaNormalize(x._1)).toString + " -> " + (HOLBetaReduction.betaNormalize(x._2)).toString + ">"))
  }
}

object findDefinitions {
  def apply(p: LKProof) = definitions_(p, Map[HOLFormula, HOLFormula]())

  def definitions_(p: LKProof, m: Map[HOLFormula, HOLFormula])
  : Map[HOLFormula, HOLFormula] = p match {
    case DefinitionLeftRule(proof, root, a, p) =>
      //println("definition rule left! "+a+" "+p);
      definitions_(proof, m) + ((p.formula, a.formula));
    case DefinitionRightRule(proof, root, a, p) =>
      //println("definition right rule! "+a+" "+p);
      definitions_(proof, m) + ((p.formula, a.formula));
    case x: UnaryLKProof =>
      definitions_(x.uProof, m);
    case x: BinaryLKProof => //pass map from left branch to right branch
      definitions_(x.uProof2, definitions_(x.uProof1, m));
    case _ => m
  }
}

object extractLKSKExpansionSequent {
  def apply(proof: LKProof): ExpansionSequent =
    herbrandExtraction.lksk.extractLKSKExpansionTrees(proof, true)
}

object definitionElimination {
  def apply(db: ProofDatabase, name: String): LKProof = {
    val proofs = db.proofs.filter(_._1 == name)
    require(proofs.nonEmpty, "Proof " + name + " not contained in proof database: " + db.proofs.map(_._1))
    val ((_, p)) :: _ = proofs
    apply(db.Definitions, p)
  }

  def apply(definition_map: Map[HOLExpression, HOLExpression], p: LKProof): LKProof =
    AtomicExpansion(DefinitionElimination(definition_map, p))
}

object css {
  def apply(s: Struct): (List[FSequent], List[FSequent], List[FSequent], FOLConstantsMap) = {
    val clauselist = structToClausesList(SimplifyStruct(s))
    val (fcmap, fol, hol) = apply(clauselist)
    (clauselist.map(_.toFSequent), fol, hol, fcmap)
  }

  def apply(l: List[Sequent]): (FOLConstantsMap, List[FSequent], List[FSequent]) =
    prunes(l)

  def prunes(l: List[Sequent]): (FOLConstantsMap, List[FSequent], List[FSequent]) = {
    prunefs(l map (_.toFSequent))
  }

  def prunefs(l: List[FSequent]): (FOLConstantsMap, List[FSequent], List[FSequent]) = {
    val (fcmap, fol) = extractFOL(l)
    (fcmap, removeSubsumed(fol).sorted(FSequentOrdering), extractHOL(l).toSet.toList.sorted(FSequentOrdering))
  }

  type FOLConstantsMap = Map[String, FOLExpression]

  def extractFOL(l: List[FSequent]): (FOLConstantsMap, List[FSequent]) = {
    val map = MMap[FOLExpression, String]()
    val counter = new {
      private var state = 0;

      def nextId = {
        state = state + 1; state
      }
    }

    val fol = l.flatMap(x => try {
      hol2folpure(x) :: Nil
    } catch {
      case e: Exception => Nil
    })

    val rmap = map.foldLeft(Map[String, FOLExpression]())((m, pair) => {
      require(!m.isDefinedAt(pair._2), "No duplicate constant assignment allowed during hol2fol conversion!")
      m + ((pair._2, pair._1))
    })
    (rmap, fol)
  }

  def extractHOL(l: List[FSequent]): List[FSequent] = l.flatMap(x => try {
    hol2folpure(x.toFormula)
    Nil
  } catch {
    case e: Exception => x :: Nil
  })

  type Symboltable = (Map[TA, Set[String]], Map[TA, Set[String]])
  val emptysmboltable = (Map[TA, Set[String]](), Map[TA, Set[String]]())

  def extractSymbolTable(l: List[FSequent]): Symboltable =
    l.foldLeft(emptysmboltable)((table, x) => {
      val (vt, ct) = extractSymbolTable(x.toFormula)
      val (vt_, ct_) = table
      (vt ++ vt_, ct ++ ct_)
    })


  def extractSymbolTable(l: HOLExpression): Symboltable = l match {
    case HOLVar(sym, ta) =>
      val (vt, ct) = emptysmboltable
      (vt + ((ta, Set(sym))), ct)
    case v:HOLConst if v.sym.isInstanceOf[LogicalSymbolA] =>
      emptysmboltable
    case HOLConst(sym, ta) =>
      val (vt, ct) = emptysmboltable
      (vt, ct + ((ta, Set(sym))))
    case HOLApp(s, t) =>
      val (vt1, ct1) = extractSymbolTable(s)
      val (vt2, ct2) = extractSymbolTable(t)
      (vt1 ++ vt2, ct1 ++ ct2)
    case HOLAbs(x, t) =>
      val (vt1, ct1) = extractSymbolTable(x)
      val (vt2, ct2) = extractSymbolTable(t)
      (vt1 ++ vt2, ct1 ++ ct2)
  }
}

object sequent {
  def find(p: LKProof, pred: (LKProof => Boolean)): List[LKProof] = p match {
    case p: NullaryLKProof => if (pred(p)) p :: Nil else List();
    case p: UnaryLKProof =>
      val rec = find(p.uProof, pred);
      if (pred(p)) p :: rec else rec
    case p: BinaryLKProof =>
      val rec = find(p.uProof1, pred) ++ find(p.uProof2, pred)
      if (pred(p)) p :: rec else rec
  }
}

object hol2fol extends reduceHolToFol

object replaceAbstractions extends replaceAbstractions

object undoReplaceAbstractions extends undoReplaceAbstractions


object tbillc {
  def help() = println(helptext)

  val helptext =

    """
        | This is an example used in the talk[1] at TbiLLC 2013. It generates a (cut-free) LK proof where the extracted
        | expansion tree has nested quantifiers. Use:
        |
        | > prooftool(tbillc())
        |
        | then select "LK Proof -> Extract Expansion Tree" from the menu and click on the quantifiers to view the
        | instantiation terms.
        |
        | [1] http://www.illc.uva.nl/Tbilisi/Tbilisi2013/uploaded_files/inlineitem/riener.pdf
      """.stripMargin

    def pa : LKProof  = {
    val pa = parse fol "P(a)"
    val expxqxy = parse fol "Exists x And P(x) Exists y Q(x,y)"
    val qfa = parse fol "Q(a,f(a))"
    val qay = parse fol "Exists y Q(a,y)"
    val qga = parse fol "Q(a,g(a))"
    val a = parse folterm "a"
    val fa = parse folterm "f(a)"
    val ga = parse folterm "g(a)"

    val a1 = Axiom(pa::Nil, pa::Nil)
    val a2 = Axiom(qfa::Nil,qfa::Nil)
    val r2 = ExistsRightRule(a2, a2.root.succedent(0), qay, fa)

    val a3 = Axiom(qga ::Nil,qga::Nil)
    val r3 = ExistsRightRule(a3, a3.root.succedent(0), qay, ga)

    val r4 = OrLeftRule(r2, r3, r2.root.antecedent(0), r3.root.antecedent(0))
    val r5 = ContractionRightRule(r4, r4.root.succedent(0), r4.root.succedent(1))

    val r6 = AndRightRule(a1, r5, a1.root.succedent(0), r5.root.succedent(0))
    val r7 = ExistsRightRule(r6, r6.root.succedent(0), expxqxy, a)
    r7
    }

    def pb: LKProof  = {
      val pb = parse fol "P(b)"
      val expxqxy = parse fol "Exists x And P(x) Exists y Q(x,y)"
      val qfb = parse fol "Q(b,f(b))"
      val qby =parse fol "Exists y Q(b,y)"
      val qgb = parse fol "Q(b,g(b))"
      val b = parse folterm "b"
      val fb = parse folterm "f(b)"

      val gb = parse folterm "g(b)"

      val b1 = Axiom(pb::Nil, pb ::Nil)

      val b2
      = Axiom(qfb::Nil,qfb::Nil)
      val r2 = ExistsRightRule(b2, b2.root.succedent(0), qby, fb)

      val b3 = Axiom(qgb::Nil,qgb::Nil)
      val r3 = ExistsRightRule(b3,b3.root.succedent(0), qby, gb)

      val r4 = OrLeftRule(r2, r3, r2.root.antecedent(0), r3.root.antecedent(0))
      val r5 = ContractionRightRule(r4,r4.root.succedent(0), r4.root.succedent(1))

      val r6 = AndRightRule(b1, r5, b1.root.succedent(0), r5.root.succedent(0))
      val r7 = ExistsRightRule(r6,r6.root.succedent(0),expxqxy, b)
      r7
    }

    def apply() = {
      val a : LKProof = pa
      val b : LKProof = pb

      val allpab = parse fol "Forall x Or Q(x,f(x)) Q(x,g(x))"
      val ta = parse folterm "a"
      val tb = parse folterm "b"
      //val x = (parse folterm "x").asInstanceOf[FOLVar]

      val r1 = OrLeftRule(a,b,a.root.antecedent(0), b.root.antecedent(0))
      val r2 = ForallLeftRule(r1, r1.root.antecedent(0), allpab, ta  )
      val r3 = ForallLeftRule(r2, r2.root.antecedent(0), allpab, tb  )
      val r4 = ContractionLeftRule(r3, r3.root.antecedent(1), r3.root.antecedent(2))
      val r5 = ContractionRightRule(r4, r4.root.succedent(0), r4.root.succedent(1))
      r5
    }

}


object philsci {
  def apply() : (LKProof,
    LKProof) = {
    val p1= parse fol "B"
    val p2= parse fol "A"
    val q = parse fol "C"
    val r1 = Axiom(p1 ::Nil,p1::Nil)
    val r1_ = Axiom(p1::Nil,p1::Nil)
    val r2 = Axiom(p2::Nil,p2::Nil)
    val r3 = Axiom(q::Nil,q::Nil)
    val r4 = OrLeftRule(r2,r1, r2.root.antecedent(0), r1.root.antecedent(0) )
    val r5 = NegLeftRule(r4, r4.root.succedent(1))
    val r6 = ImpRightRule(r5, r5.root.antecedent(1), r5.root.succedent(0))

    val r7 = NegLeftRule(r1_, r1_.root.succedent(0))
    val r8 = NegRightRule(r7, r7.root.antecedent(0))
    val r9 = WeakeningLeftRule(r3, p2)
    val

    r10 = ImpLeftRule(r8,r9,r8.root.succedent(0), r9.root.antecedent(1))
    val r11 = CutRule(r6, r10, r6.root.succedent(0),r10.root.antecedent(2))

    val proj = Projections(r11).toList
    val acnf1 = CutRule(proj(0), proj(1), proj(0).root.succedent(1), proj(1).root.antecedent(0))
    val acnf2 = ContractionLeftRule(acnf1, acnf1.root.antecedent(2), acnf1.root.antecedent(4))
    val acnf3 = ContractionRightRule(acnf2, acnf2.root.succedent(1), acnf2.root.succedent(2))
    val acnf4 =ContractionLeftRule(acnf3, acnf3.root.antecedent(0), acnf3.root.antecedent(3))
    val acnf5 = ContractionLeftRule(acnf4, acnf4.root.antecedent(0), acnf4.root.antecedent(1))

    (r11, acnf5)
  }

}

object equation_example {
  def apply : (LKProof, FOLSubstitution) = {
    val List(
    uv,fuu,fuv,ab,fab) = List("u = v",
      "f(u)=f(u)", "f(u)=f(v)", "a=b", "f(a)=f(b)") map (Prover9TermParserLadrStyle.parseFormula)
    val List(uy,xy,ay) = List("(all y (u = y -> f(u) = f(y)))",
      "(all x all y (x = y -> f(x) = f(y)))",
      "(all y (a = y -> f(a) = f(y)))") map (Prover9TermParserLadrStyle
      .parseFormula)
    val List(u,v) = List("u","v").map(s => FOLVar(s))

    val List(a,b) = List("a","b").map(s => FOLConst(s))
    val ax1 = Axiom(List(uv),List(uv))
    val ax2 = Axiom(List(),List(fuu))
    val ax3 = Axiom(List(ab),List(ab))
    val ax4 = Axiom(List(fab),List(fab))

    val i1 = EquationRight1Rule(ax1,ax2,ax1.root.succedent(0),ax2.root.succedent(0), fuv)

    val i2 = ImpRightRule(i1, i1.root.antecedent(0),i1.root.succedent(0))
    println(i2.root)
    val i3 = ForallRightRule(i2, i2.root.succedent(0), uy, v )
    val i4 = ForallRightRule(i3, i3.root.succedent(0), xy, u )

    val i5 = ImpLeftRule(ax3,ax4,ax3.root.succedent(0),ax4.root.antecedent(0))
    val i6 = ForallLeftRule(i5, i5.root.antecedent(1),ay, b)
    val i7 = ForallLeftRule(i6, i6.root.antecedent(1), xy, a)

    val es = CutRule(i4,i7,i4.root.succedent(0),i7.root.antecedent(1))
    val sub = FOLSubstitution((u,b)::Nil)
    (es, sub)
  }
}
