/*
 * GAPScalaInteractiveShellLibrary.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.cli

import at.logic.algorithms.fol.hol2fol._
import at.logic.algorithms.hlk.{LKProofParser, SchemaFormulaParser}
import at.logic.algorithms.interpolation._
import at.logic.algorithms.lk._
import at.logic.algorithms.lk.simplification._
import at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
import at.logic.algorithms.resolution._
import at.logic.algorithms.rewriting.NameReplacement
import at.logic.algorithms.shlk._
import at.logic.algorithms.subsumption._
import at.logic.algorithms.unification.hol._
import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import at.logic.algorithms.unification.{MulACEquality, MulACUEquality}

import at.logic.calculi.expansionTrees.ExpansionTree
import at.logic.calculi.expansionTrees.multi.MultiExpansionTree
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lksk.base._
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.calculi.resolution.base._
import at.logic.calculi.resolution.robinson._

import at.logic.language.fol
import at.logic.language.fol.{FOLFormula, FOLExpression, FOLTerm, FOLVar}
import at.logic.language.hol._
import at.logic.language.hol.Definitions._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.typedLambdaCalculus.{Var, LambdaExpression}
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.schema._
import at.logic.language.schema.IndexedPredicate._
import at.logic.language.schema.indexedFOVar._

import at.logic.parsing.calculi.latex._
import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
import at.logic.parsing.calculus.xml._
import at.logic.parsing.ivy.{IvyParser, IvyResolutionProof}
import at.logic.parsing.ivy.conversion.IvyToRobinson
import at.logic.parsing.ivy
import at.logic.parsing.language.arithmetic.HOLTermArithmeticalExporter
import at.logic.parsing.language.prover9.{Prover9TermParserLadrStyle, Prover9TermParser}
import at.logic.parsing.language.simple.SimpleFOLParser
import at.logic.parsing.language.simple.SimpleHOLParser
import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.lisp.SExpressionParser
import at.logic.parsing.readers.StringReader
import at.logic.parsing.readers.XMLReaders._
import at.logic.parsing.writers.FileWriter

import at.logic.provers.atp.commands.base.SetStreamCommand
import at.logic.provers.atp.commands.refinements.base.SequentsMacroCommand
import at.logic.provers.atp.commands.refinements.simple.SimpleRefinementGetCommand
import at.logic.provers.atp.commands.sequents.SetTargetClause
import at.logic.provers.atp.Prover
import at.logic.provers.prover9.commands.Prover9InitCommand
import at.logic.provers.prover9.Prover9

import at.logic.transformations.skolemization.skolemize
import at.logic.transformations.ceres.clauseSchema._

import java.io.{File, FileReader, FileInputStream, InputStreamReader, FileWriter => JFileWriter, BufferedWriter=>JBufferedWriter}
import java.io.IOException
import java.util.zip.GZIPInputStream

import scala.collection.mutable.{Map => MMap}

package GAPScalaInteractiveShellLibrary {

import at.logic.algorithms.lk.statistics._
import at.logic.calculi.slk.SchemaProofDB
import at.logic.transformations.ceres.ACNF.getInstantiationsOfTheIndexedFOVars
import at.logic.transformations.ceres.ACNF.ConvertCutsToHOLFormulasInResProof
import at.logic.transformations.ceres.ACNF.renameIndexedVarInProjection
import at.logic.algorithms.unification.EequalityA
import at.logic.language.fol.FOLConst
import at.logic.calculi.lk.quantificationRules.ForallLeftRule

object printProofStats {
    def apply(p: LKProof) = {
      val stats = getStatistics( p )
      val total = rulesNumber(p)
      val quant = quantRulesNumber(p)
      val weakQuant = weakQuantRulesNumber(p)
      println("------------- Statistics ---------------")
      println("Cuts: " + stats.cuts)
      println("Number of quantifier rules: " + quant)
      println("Number of rules: " + total)
      println("Quantifier complexity: " + weakQuant)
      println("----------------------------------------")
    }
  }

  object lkTolksk {
    def apply(p: LKProof) = at.logic.transformations.skolemization.lksk.LKtoLKskc( p )
  }

/******************** CERES operations *************************/

  import at.logic.transformations.ceres.struct._
  object extractStruct {
    def apply(p: LKProof) = StructCreators.extract( p )
  }

  object structToClausesList {
    def apply(s: Struct) = at.logic.transformations.ceres.clauseSets.StandardClauseSet.transformStructToClauseSet(s)
  }

  object structToLabelledClausesList {
    def apply(s: Struct) = at.logic.transformations.ceres.clauseSets.StandardClauseSet.transformStructToLabelledClauseSet(s)
  }

  object refuteClauseList {
    def apply(cl: List[Sequent]) : Option[RobinsonResolutionProof] = prover9(cl)
  }

  object computeProjections {
    def apply(p: LKProof) : Set[LKProof] = at.logic.transformations.ceres.projections.Projections(p)
  }

  object computeGroundProjections {
    def apply(projections: Set[LKProof], groundSubs: List[(HOLVar, HOLExpression)]): Set[LKProof] = {
      groundSubs.map(subs => projections.map(pr => renameIndexedVarInProjection(pr, subs))).flatten.toSet
    }
  }

  object buildACNF {
    def apply(ref: LKProof, projs: Set[LKProof], es: FSequent) = at.logic.transformations.ceres.ACNF.ACNF(ref, projs, es)
  }

/******************** Proof loaders *************************/

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

  object loadProofDB {
    def apply(file: String) =
      try {
        (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream(file)))) with XMLProofDatabaseParser).getProofDatabase()
      }
    catch
    {
      case _ =>
        (new XMLReader(new InputStreamReader(new FileInputStream(file))) with XMLProofDatabaseParser).getProofDatabase()
    }
  }

  object loadPrime {
    def apply(i : Int) = {
      val p2   = loadProofs("prime1-"+i+".xml").head._2
      val p2_  = regularize(skolemize(p2))._1
      val cs2  = structToClausesList(extractStruct(p2_))
      val cs2_ = removeDuplicates(deleteEquationalTautologies(deleteTautologies(cs2 map ((x:Sequent) => x.toFSequent))))
      writeLatex(cs2_ map (fsequent2sequent.apply), "cs"+i+".tex")
      exportTPTP(cs2_, "cs"+i+".p")
      (p2,p2_,cs2,cs2_)
    }

  }

  import at.logic.parsing.veriT._
  object loadVeriTProof {
    // NOTE: this method returns a proof in the form of an expansion proof
    def apply(fileName : String) = VeriTParser.read(fileName)
  }

  object loadIvyProof {
    var naming_style : IvyParser.VariableNamingConvention = IvyParser.IvyStyleVariables
    def set_ivy_naming = { naming_style = IvyParser.IvyStyleVariables }
    def set_ladr_naming = { naming_style = IvyParser.LadrStyleVariables }
    def set_prolog_naming = { naming_style = IvyParser.LadrStyleVariables }

    def apply(fn : String) : RobinsonResolutionProof = {
      val rp = IvyToRobinson(intoIvyResolution(fn))
      InstantiateElimination(rp)
    }

    def intoIvyResolution(fn : String) : IvyResolutionProof = {
      val ivyproof = IvyParser.apply(fn, naming_style)
      ivyproof
    }

    def printNodes(p:IvyResolutionProof, m : List[String]) : List[String] = p match {
      case ivy.InitialClause(id, _, clause) => if (! m.contains(id)) { println(id + " : "+clause); id::m } else m
      case ivy.Instantiate(id,_, sub, clause, parent) => if (! m.contains(id)) { val l = printNodes(parent, m); println(id + " : "+clause); id::l } else m
      case ivy.Propositional(id,_, clause, parent) => if (! m.contains(id)) { val l1 = printNodes(parent,m); println(id + " : "+clause); id::l1 } else m
      case ivy.Resolution(id, _, lit1, lit2, clause, parent1, parent2) =>
        if (!m.contains(id)) {
          val l1 = printNodes(parent1,m);
          val l2 = printNodes(parent2,l1);
          println(id + " : "+clause); id::l2
        }
        else m
      case _ => println("rule not implemented"); m
    }

    def collectIds(p:IvyResolutionProof) : List[String] = p match {
      case ivy.InitialClause(id, _, clause) => id::Nil
      case ivy.Instantiate(id,_, sub, clause, parent) => id::collectIds(parent)
      case ivy.Propositional(id,_, clause, parent) => id::collectIds(parent)
      case ivy.Resolution(id, _, lit1, lit2, clause, parent1, parent2) => id::(collectIds(parent1) ++ collectIds(parent2))
      case _ => println("rule not implemented"); Nil
    }

  }

  object loadHLK {
    def apply(filename : String) = LKProofParser.parseProof(new InputStreamReader(new FileInputStream(filename)))

  }

  object loadProver9Proof {
    def apply(filename : String, escape_underscore : Boolean = true, newimpl : Boolean = true) :
      (RobinsonResolutionProof, FSequent) = Prover9.parse_prover9(filename, escape_underscore, newimpl)
  }

  object loadProver9LKProof {
    def apply(filename : String, newimpl : Boolean = true, forceSkolemization: Boolean = false) : LKProof = {
      val (proof, endsequent) = Prover9.parse_prover9(filename, true, newimpl)
      //println("skolemizing endsequent: "+endsequent)
      //val sendsequent = skolemize(endsequent)
      //val folsendsequent= FSequent(sendsequent.antecedent.map(x => hol2fol(x)), sendsequent.succedent.map(x => hol2fol(x)))
      //println("done: "+folsendsequent)
      if (!forceSkolemization && !containsStrongQuantifiers(endsequent)) {
        //println("End-sequent does not contain strong quantifiers!.")
          val closure = FSequent(endsequent.antecedent map (x => univclosure( x.asInstanceOf[FOLFormula])),
              endsequent.succedent map (x => existsclosure( x.asInstanceOf[FOLFormula])))

          Robinson2LK(proof,closure)
      } else {
        //if (forceSkolemization) println("Using initial clauses although end-sequent is skolemized")
        //else println("End-sequent does contain strong quantifiers, using initial clauses instead.")

          val fclauses : Set[FClause]  = proof.nodes.map( _ match {
              case InitialClause(clause) => clause.toFClause;
              case _ => FClause(Nil,Nil) }
              ).filter( (x:FClause) => x match { case FClause(Nil,Nil) => false; case _ => true } )
            val clauses = fclauses.map( c => univclosure(fol.Or(c.neg.map(f => fol.Neg(f.asInstanceOf[FOLFormula])) ++ c.pos.map(f => f.asInstanceOf[FOLFormula])))  )
            val clauses_ = clauses.partition(_ match { case fol.Neg(_) => false; case _ => true})
            //val cendsequent = FSequent(clauses.toList, Nil)
            val cendsequent2 = FSequent(clauses_._1.toList, clauses_._2.map(_ match {case fol.Neg(x) => x} ).toList)
            //println("new endsequent: "+cendsequent2)

            Robinson2LK(proof,cendsequent2)

      }
    }
    def univclosure(f:FOLFormula) = f.freeVariables.foldRight(f)((v,g) => fol.AllVar(v.asInstanceOf[FOLVar],g))
    def existsclosure(f:FOLFormula) = f.freeVariables.foldRight(f)((v,g) => fol.ExVar(v.asInstanceOf[FOLVar],g))

      def containsStrongQuantifiers(fs:FSequent) : Boolean =
        fs.antecedent.exists(x => containsStrongQuantifiers(x.asInstanceOf[FOLFormula],false)) ||
        fs.succedent.exists(x => containsStrongQuantifiers(x.asInstanceOf[FOLFormula],true))

      def containsStrongQuantifiers(f:FOLFormula, pol : Boolean) : Boolean = f match {
        case fol.Atom(_,_) => false
        case fol.And(s,t) => containsStrongQuantifiers(s, pol)  || containsStrongQuantifiers(t,pol)
        case fol.Or(s,t)  => containsStrongQuantifiers(s, pol)  || containsStrongQuantifiers(t,pol)
        case fol.Imp(s,t) => containsStrongQuantifiers(s, !pol) || containsStrongQuantifiers(t,pol)
        case fol.Neg(s)   => containsStrongQuantifiers(s, !pol)
        case fol.AllVar(x,s) => if (pol == true) true else containsStrongQuantifiers(s, pol)
        case fol.ExVar(x,s)  => if (pol == false) true else containsStrongQuantifiers(s, pol)
        case _ => throw new Exception("Unhandled case!")
      }

  }

/*************************************************************/

  object createHOLExpression {
    def apply(s: String) = (new StringReader(s) with SimpleHOLParser {}).getTerm()
  }

  object deleteTautologies {
    def apply(ls: List[FSequent]) = at.logic.algorithms.lk.simplification.deleteTautologies( ls )
  }

  object deleteEquationalTautologies {
    private val counter = new {private var state = 0; def nextId = { state = state +1; state}}
    private val emptymap = MMap[LambdaExpression, ConstantStringSymbol]()
      val acu = new MulACUEquality(List("+","*") map (new ConstantStringSymbol(_)), List("0","1") map (new ConstantStringSymbol(_)))

      def apply(ls : List[FSequent]) = ls.filterNot(_._2 exists ((f:HOLFormula) =>
            f match {
            case Atom(ConstantStringSymbol(sym), List(x,y)) => sym == "=" && x == y
            case _ => false
            } ))

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
  }

  object fsequent2sequent {
    def f2focc(f:HOLFormula) = new FormulaOccurrence(f, Nil, defaultFormulaOccurrenceFactory)
      def apply(s : FSequent) = Sequent(s._1 map f2focc , s._2 map f2focc )
  }

  object removeDuplicates {
    def apply[A](ls: List[A]) = ls.distinct
  }
  object unitResolve {
    //def apply(ls: List[Sequent]) = simpleUnitResolutionNormalization(ls map (_.toFSequent))
    def apply(ls: List[FSequent]) = simpleUnitResolutionNormalization(ls)
  }
  object removeSubsumed {
    //def apply(ls: List[Sequent]) = subsumedClausesRemoval(ls map (_.toFSequent))
    def apply(ls: List[FSequent]) = subsumedClausesRemoval(ls)
  }
  object normalizeClauses {
    //def apply(ls: List[Sequent]) = sequentNormalize(ls map (_.toFSequent))
    def apply(ls: List[FSequent]) = sequentNormalize(ls)
  }
  object writeLabelledSequentListLatex {
    def apply(ls: List[LabelledSequent], outputFile: String) = {
      // maps original types and definitions of abstractions
      val sections = ("Types", getTypeInformation(ls).toList.sortWith((x,y) => x.toString < y.toString))::Nil
        (new FileWriter(outputFile) with LabelledSequentsListLatexExporter with HOLTermArithmeticalExporter).exportSequentList(ls,sections).close
    }
  }
  object writeLatex {
    def apply(ls: List[Sequent], outputFile: String) = {
      // maps original types and definitions of abstractions
      val sectionsPre = ("Types", getTypeInformation(ls).toList.sortWith((x,y) => x.toString < y.toString))::Nil

        val sections = try {
          // convert to fol and obtain map of definitons
          val imap = Map[at.logic.language.lambda.typedLambdaCalculus.LambdaExpression, at.logic.language.hol.logicSymbols.ConstantStringSymbol]()
            val iid = new {var idd = 0; def nextId = {idd = idd+1; idd}}
          /*
             val cs = ls.map(x => Sequent(
             x.antecedent.map(y => reduceHolToFol(y.asInstanceOf[HOLExpression],imap,iid).asInstanceOf[FOLFormula]),
             x.succedent.map(y => reduceHolToFol(y.asInstanceOf[HOLExpression],imap,iid).asInstanceOf[FOLFormula])
             ))*/
          ("Definitions", imap.toList.map(x => (x._1, createExampleFOLConstant(x._1, x._2))))::sectionsPre
        }
      catch {
        case _ => sectionsPre
      }
      (new FileWriter(outputFile) with SequentsListLatexExporter with HOLTermArithmeticalExporter).exportSequentList(ls map (_.toFSequent),sections).close
    }
  }

  object exportXML {
    def apply( ls: List[LKProof], names: List[String], outputFile: String ) = {
      val exporter = new LKExporter{}
      val pairs = ls.zip( names )
        scala.xml.XML.save( outputFile,
            <proofdatabase>
            <definitionlist/>
            <axiomset/>
            { pairs.map( p => exporter.exportProof( p._2, p._1 ) ) }
            <variabledefinitions/>
            </proofdatabase>, "UTF-8", true,
            scala.xml.dtd.DocType( "proofdatabase", scala.xml.dtd.SystemID( "http://www.logic.at/ceres/xml/5.0/proofdatabase.dtd" ) , Nil ) )
    }
  }

  object exportTPTP {
    def apply( ls : List[FSequent], filename : String) = {
      val file = new JBufferedWriter(new JFileWriter(filename))
        file.write(at.logic.parsing.language.tptp.TPTPFOLExporter.tptp_problem(ls))
        file.close
    }
  }

  object createEquality {
    def apply(fs : List[String], cs : List[String]) =
      new MulACUEquality(fs map (new ConstantStringSymbol(_)), cs map (new ConstantStringSymbol(_)))

      def apply(fs : List[String]) =
      new MulACEquality(fs map (new ConstantStringSymbol(_)))
  }

  object parse {
    private class CLIParserFOL(input: String) extends StringReader(input) with SimpleFOLParser
    private class CLIParserHOL(input: String) extends StringReader(input) with SimpleHOLParser
    private class CLIParserSchema(input: String) extends StringReader(input) with SchemaFormulaParser

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

    def sfo(string:String) = {
      new CLIParserSchema(string) getTerm
    }

    def p9(string:String, use_ladr : Boolean = true) = {
      if (use_ladr)
        Prover9TermParserLadrStyle.parseFormula(string)
      else
        Prover9TermParser.parseFormula(string)
    }

    def slk(file:String) = {
      sFOParser.parseProofFlat( new InputStreamReader(new FileInputStream( file ) ) )
    }

    def lisp(string:String) = {
      SExpressionParser.parseString(string)
    }

    def help() = {
      println("folterm: String => FOLFormula")
        println("folterm: String => FOLTerm")
        println("hol: String => HOLExpression")
        println("slk: String => Map[String, Pair[LKProof, LKProof]]")
    }
  }

/*************************** Cut introduction algorithm **********************************/

  import at.logic.algorithms.cutIntroduction._
  object extractTerms {
    def apply( p: LKProof ) = {
      val ts = new FlatTermSet(TermsExtraction(p))
      println( "\nTerm set: {" + ts.termset + "}" )
      println( "Size of term set: " + ts.termset.size )
      ts
    }
    def apply( ep: (Seq[ExpansionTree], Seq[ExpansionTree])) {
      val ts = new FlatTermSet(TermsExtraction(ep))
      println( "\nTerm set: {" + ts.termset + "}" )
      println( "Size of term set: " + ts.termset.size )
      ts
    }
  }

  object computeGrammars {
    def apply(terms: FlatTermSet) = {
      val g = ComputeGrammars(terms)
        g.size match {
          case 0 => throw new Exception("No grammars found for this list of terms.")
          case n => println(n + " grammars found.\n"); g
        }
    }
  }

  object seeNFirstGrammars {
    def apply(lst: List[Grammar], n: Int) = {
      for(i <- 0 to n-1) {
        println(i + ". " + lst(i).toPrettyString + "(size = " + lst(i).size + ")"  )
      }
      println("\nNote that the function symbols 'tuplei' are inserted by the system as part of the algorithm.")
    }
  }

  object generateExtendedHerbrandSequent {
    def apply( es: Sequent, g: Grammar) =
      new ExtendedHerbrandSequent(es, g)
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
      ehs.minimizeSolution
      println("Improved solution: " + ehs.cutFormula)
    }
  }

  object buildProofWithCut {
    def apply(ehs: ExtendedHerbrandSequent) =
      CutIntroduction.buildFinalProof(ehs) match {
        case Some(proof) => proof
        case None => throw new Exception("Could not construct a proof with cut.")
      }
  }

  object cutIntro {
    def apply( p: LKProof ) : LKProof = CutIntroduction(p)
    def apply( e: (Seq[ExpansionTree], Seq[ExpansionTree]) ) : LKProof = CutIntroduction(e)
  }

  object cutIntro2 {
    def apply( p: LKProof ) : LKProof = CutIntroduction.apply2(p)
    def apply( e: (Seq[ExpansionTree], Seq[ExpansionTree]) ) : LKProof = CutIntroduction.apply2(e)
  }

/*****************************************************************************************/

  object toClauses {
    def apply( f: HOLFormula ) = CNFp(f)
  }

  object extractInterpolant {
    def apply( p: LKProof, npart: Set[FormulaOccurrence], ppart: Set[FormulaOccurrence] ) = ExtractInterpolant( p, npart, ppart )
  }

  object extractHerbrandSequent {
    def apply( p: LKProof ) = at.logic.transformations.herbrandExtraction.ExtractHerbrandSequent(p)
  }

  object eliminateInstaces {
    def apply(p:RobinsonResolutionProof) = InstantiateElimination.apply(p)
  }

  object miniSATsolve {
    def apply( f : HOLFormula ) = (new at.logic.provers.minisat.MiniSAT).solve(f)
  }

  object miniSATprove {
    def apply ( f : HOLFormula ) = (new at.logic.provers.minisat.MiniSAT).isValid(f)
  }

  // atp support
  object refuteFOL {
      import at.logic.provers.atp.commands.base._
      import at.logic.provers.atp.commands.sequents._
      import at.logic.provers.atp.commands.robinson._
      import at.logic.provers.atp.commands.logical.DeterministicAndCommand
      def stream1:  Stream[Command[Clause]] = Stream.cons(SequentsMacroCommand[Clause](
            SimpleRefinementGetCommand[Clause],
            List(VariantsCommand, DeterministicAndCommand[Clause](
                List(ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand(FOLUnificationAlgorithm), FactorCommand(FOLUnificationAlgorithm)),
                List(ParamodulationCommand(FOLUnificationAlgorithm))),
              SimpleForwardSubsumptionCommand[Clause](new StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}),
              SimpleBackwardSubsumptionCommand[Clause](new StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}),
              InsertResolventCommand[Clause]),
            RefutationReachedCommand[Clause]), stream1)
      /*def stream1:  Stream[Command[Clause]] = Stream.cons(SimpleRefinementGetCommand[Clause],
        Stream.cons(VariantsCommand,
        Stream.cons(DeterministicAndCommand[Clause]((
        List(ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand(FOLUnificationAlgorithm), FactorCommand(FOLUnificationAlgorithm)),
        List(ParamodulationCommand(FOLUnificationAlgorithm)))),
        Stream.cons(SimpleForwardSubsumptionCommand[Clause](new StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}),
        Stream.cons(SimpleBackwardSubsumptionCommand[Clause](new StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}),
        Stream.cons(InsertResolventCommand[Clause],
        Stream.cons(RefutationReachedCommand[Clause], stream1)))))))                                                                                  */
      def stream: Stream[Command[Clause]] = Stream.cons(SetTargetClause(FSequent(List(),List())), Stream.cons(SearchForEmptyClauseCommand[Clause], stream1))

      def apply(clauses: Seq[FSequent]): Option[ResolutionProof[Clause]] =
                                         new Prover[Clause]{}.
                                           refute(Stream.cons(SetClausesCommand(clauses), stream)).next
  }
  object refuteFOLI {
    import at.logic.provers.atp.commands.base._
    import at.logic.provers.atp.commands.ui._
    import at.logic.provers.atp.commands.sequents._
    import at.logic.provers.atp.commands.robinson._
    import at.logic.provers.atp.commands.logical.DeterministicAndCommand
    def stream1:  Stream[Command[Clause]] = Stream.cons(getTwoClausesFromUICommand[Clause](PromptTerminal.GetTwoClauses),
        Stream.cons(VariantsCommand,
          Stream.cons(DeterministicAndCommand[Clause]((
                List(ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand(FOLUnificationAlgorithm), FactorCommand(FOLUnificationAlgorithm)),
                List(ParamodulationCommand(FOLUnificationAlgorithm)))),
            Stream.cons(SimpleForwardSubsumptionCommand[Clause](new StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}),
              Stream.cons(SimpleBackwardSubsumptionCommand[Clause](new StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}),
                Stream.cons(InsertResolventCommand[Clause],
                  Stream.cons(RefutationReachedCommand[Clause], stream1)))))))
    def stream: Stream[Command[Clause]] = Stream.cons(SetTargetClause(FSequent(List(),List())), Stream.cons(SearchForEmptyClauseCommand[Clause], stream1))

    def apply(clauses: Seq[FSequent]): Option[ResolutionProof[Clause]] =
      new Prover[Clause]{}.
        refute(Stream.cons(SetClausesCommand(clauses), stream)).next
  }

  object replay {
    private class MyParser(str: String) extends StringReader(str) with SimpleResolutionParserFOL
      def apply1(clauses: String): Option[ResolutionProof[Clause]] = {
        apply(new MyParser(clauses).getClauseList)
      }

    def apply(clauses: Seq[FSequent]): Option[ResolutionProof[Clause]] =
      try {
        new Prover[Clause]{}.
          refute(Stream(SetTargetClause(FSequent(List(),List())), Prover9InitCommand(clauses), SetStreamCommand())).next
      } catch {
        case e: IOException => throw new IOException("Prover9 is not installed: " + e.getMessage())
      }

    def apply(clauses: List[Sequent]): Option[ResolutionProof[Clause]] =
      try {
        new Prover[Clause]{}.
          refute(Stream(SetTargetClause(FSequent(List(),List())), Prover9InitCommand( (clauses map ( (x:Sequent) => x.toFSequent)).toList   ), SetStreamCommand())).next
      } catch {
        case e: IOException => throw new IOException("Prover9 is not installed: " + e.getMessage())
      }
  }

  object Robinson2LK {
    def apply(resProof: ResolutionProof[Clause]): LKProof = at.logic.algorithms.resolution.RobinsonToLK(resProof.asInstanceOf[RobinsonResolutionProof])
    def apply(resProof: ResolutionProof[Clause], seq: FSequent): LKProof = at.logic.algorithms.resolution.RobinsonToLK(resProof.asInstanceOf[RobinsonResolutionProof],seq)
    def toHOL(FOLresProofLK: LKProof): LKProof = ConvertCutsToHOLFormulasInResProof(FOLresProofLK)
  }

  object prover9 {
    //we have to refute
    def apply( filename : String) : Option[RobinsonResolutionProof] = Prover9.refute(filename)
    def apply( clauses: Seq[FSequent] ) : Option[RobinsonResolutionProof] = Prover9.refute( clauses.toList )
    def apply( clauses: List[Sequent] ) : Option[RobinsonResolutionProof]= Prover9.refute( clauses map (_.toFSequent))
    def refuteTPTP(fn:String) = Prover9.refuteTPTP(fn)

    //get the ground substitution of the ground resolution refutation
    //the ground substitution is a list of pairs, it can't be a map ! The reason is : a clause can be used several times in the resolution refutation.
    def getGroundSubstitution(rrp: RobinsonResolutionProof): List[(HOLVar, HOLExpression)] = getInstantiationsOfTheIndexedFOVars(rrp)
  }

  // called "proveProp" and not autoProp to be more consistent with many other commands which are (or start with) a verb
  object proveProp {
    def apply( seq: FSequent ) : Option[LKProof] = solvePropositional(seq)
    def apply( f: HOLFormula ) : Option[LKProof] = apply( FSequent( Nil, f::Nil ))
  }

  object format {
    def apply(p: ResolutionProof[Clause]) = asHumanReadableString(p)

      def asHumanReadableString(p: ResolutionProof[Clause]) = Formatter.asHumanReadableString(p)
      def asGraphVizString(p:ResolutionProof[Clause]) = Formatter.asGraphViz(p)
      def asTex(p:ResolutionProof[Clause]) = Formatter.asTex(p)
  }

  object rename {
    def apply[T <: LambdaExpression](exp : T, map : NameReplacement.SymbolMap) : T = NameReplacement(exp, map)
    def apply(fs: FSequent, map : NameReplacement.SymbolMap) = NameReplacement(fs,map)
    def apply(p : RobinsonResolutionProof, map : NameReplacement.SymbolMap) : RobinsonResolutionProof = NameReplacement(p, map)
  }

  object proofs {
    def simple1() : LKProof = {
      val x = HOLVar(new VariableStringSymbol("x"), i)
        val y = HOLVar(new VariableStringSymbol("y"), i)
        val a = HOLVar(new VariableStringSymbol("a"), i)
        val b = HOLVar(new VariableStringSymbol("b"), i)
        val Rab = Atom( new ConstantStringSymbol("R"), a::b::Nil )
        val exyRay = ExVar( y, Atom( new ConstantStringSymbol("R"), a::y::Nil ) )
        val allxexyRxy = AllVar( x, ExVar( y, Atom( new ConstantStringSymbol("R"), x::y::Nil ) ) )
        val ax = Axiom( Rab::Nil, Rab::Nil )
        val r1 = ExistsRightRule( ax, ax.root.succedent(0), exyRay, b )
        val r2 = ExistsLeftRule( r1, r1.root.antecedent(0) , exyRay, b )
        val r3 = ForallLeftRule( r2, r2.root.antecedent(0), allxexyRxy, a )
        val proof : LKProof = ForallRightRule( r3, exyRay, allxexyRxy, a )
        proof
    }
  }

  object huet {
    import at.logic.parsing.readers.StringReader
    import at.logic.parsing.language.simple._
    import at.logic.algorithms.unification.hol.huet._
    import at.logic.utils.executionModels.ndStream.{NDStream, Configuration}

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

  object normalizeSub {
    import at.logic.language.lambda.substitutions._
    import at.logic.language.lambda.BetaReduction
    import at.logic.language.lambda.BetaReduction._
    import StrategyOuterInner._
    import StrategyLeftRight._
    def apply(sub : Substitution[HOLExpression]):Unit = {
      sub.map.foreach(x => println("\n<"+(BetaReduction.betaNormalize(x._1)(Outermost)).toStringSimple+" -> "+(BetaReduction.betaNormalize(x._2)(Outermost)).toStringSimple+">"))
    }
  }

  object prooftool {
    def apply(x: AnyRef) = at.logic.gui.prooftool.gui.Main.display("From CLI", x)
  }

  object findDefinitions {
    def apply(p: LKProof) = definitions_(p, Map[HOLFormula, HOLFormula]())

      def definitions_(p: LKProof, m : Map[HOLFormula, HOLFormula])
      : Map[HOLFormula, HOLFormula] = p match {
        case DefinitionLeftRule(proof, root, a, p) =>
          //println("definition rule left! "+a+" "+p);
          definitions_(proof,m) + ((p.formula,a.formula));
        case DefinitionRightRule(proof, root, a, p) =>
          //println("definition right rule! "+a+" "+p);
          definitions_(proof,m) + ((p.formula,a.formula));
        case x : UnaryLKProof =>
                 definitions_(x.uProof, m);
        case x: BinaryLKProof => //pass map from left branch to right branch
                definitions_(x.uProof2, definitions_(x.uProof1,m));
                case _ =>  m
      }
  }

  object extractExpansionTrees {
    def apply(proof: LKProof): Tuple2[Seq[ExpansionTree],Seq[ExpansionTree]] = at.logic.transformations.herbrandExtraction.extractExpansionTrees(proof)
  }

  object compressExpansionTree {
    def apply(tree: ExpansionTree): MultiExpansionTree = at.logic.algorithms.expansionTrees.compressQuantifiers(tree)
  }

  object definitions {
  }

  object sequent {
    def find(p:LKProof, pred : (LKProof => Boolean)) : List[LKProof] = p match {
      case p:NullaryLKProof => if (pred(p)) p::Nil else List();
      case p:UnaryLKProof =>
             val rec = find(p.uProof,pred);
             if (pred(p)) p::rec else rec
      case p:BinaryLKProof =>
             val rec = find(p.uProof1,pred) ++ find(p.uProof2,pred)
               if (pred(p)) p::rec else rec
    }
  }

  object printTRS {
    def ClauseSchema(i: Int):Unit = {
      val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero()))); val four = Succ(three); val five = Succ(four)
        val j: IntegerTerm = if (i == 0) zero else if (i == 1) one else if (i == 2) two else if (i == 3) three else if (i == 4) four else five
        val k = IntVar(new VariableStringSymbol("k"))
        val l = IntVar(new VariableStringSymbol("l"))
        val n1 = Succ(k); val n2 = Succ(n1); val n3 = Succ(n2)


        val Pk1 = IndexedPredicate(new ConstantStringSymbol("P"), Succ(k))
        val X = sClauseVar("X")
        val x = fo2Var(new VariableStringSymbol("x"))
        val P = HOLConst(new ConstantStringSymbol("P"), ->(Ti(), To()))
        val g = HOLVar(new VariableStringSymbol("g"), ->(Ti(),Ti()))
        val sigma0x0 = sTermN("σ", zero::x::zero::Nil)
        val sigmaskxsk = sTermN("σ", Succ(k)::x::Succ(k)::Nil)
        val Psigma0x0 = Atom(P, sigma0x0::Nil)
        val Psigmaskxsk = Atom(P, sigmaskxsk::Nil)

        // --- trs sigma ---
        val sigma_base = sTermN("σ", zero::x::l::Nil)
        val sigma_rec = sTermN("σ", Succ(k)::x::l::Nil)
        val st = sTermN("σ", k::x::l::Nil)
        val rewrite_base = indexedFOVar(new VariableStringSymbol("x"), l)
        val rewrite_step = HOLApp(g, st)
        var trsSigma = dbTRSsTermN("σ", Pair(sigma_base, rewrite_base), Pair(sigma_rec, rewrite_step))

        // --- trs clause schema ---
        val c1 = clauseSchema("c", k::x::X::Nil)
        val ck = clauseSchema("c", Succ(k)::x::X::Nil)
        val c0 = clauseSchema("c", zero::x::X::Nil)
        val clauseSchBase: sClause = sClauseComposition(X, nonVarSclause(Nil, Psigma0x0::Nil))
        val clauseSchRec: sClause = sClauseComposition(c1, nonVarSclause(Nil, Psigmaskxsk::Nil))
        val trsClauseSch = dbTRSclauseSchema("c", Pair(c0, clauseSchBase), Pair(ck, clauseSchRec))
        // ----------

        val map = Map[Var, HOLExpression]() + Pair(k.asInstanceOf[Var], j) + Pair(l.asInstanceOf[Var], three)
        val subst = new SchemaSubstitution3(map)

        val sig = subst(trsSigma.map.get("σ").get._2._1)
        //      println("sig = "+sig)
        val sigma3 = unfoldSTermN(sig, trsSigma)
        //      println("\n\nsigma3 = "+sigma3)

        println(Console.RED+"\nrewriting systems :\n"+Console.RESET)

        println(trsSigma.map.get("σ").get._1._1 +Console.GREEN+"       →  "+Console.RESET+trsSigma.map.get("σ").get._1._2)
        println(trsSigma.map.get("σ").get._2._1 +Console.GREEN+"  →  "+Console.RESET+trsSigma.map.get("σ").get._2._2)

        println("\n\n"+trsClauseSch.map.get("c").get._1._1 +Console.GREEN+"    →  "+Console.RESET+trsClauseSch.map.get("c").get._1._2)
        println(trsClauseSch.map.get("c").get._2._1 +Console.GREEN+"  →  "+Console.RESET+trsClauseSch.map.get("c").get._2._2)


        val clause3 = applySubToSclauseOrSclauseTerm(subst, trsClauseSch.map.get("c").get._2._1).asInstanceOf[sClause]
        println("\n\nclause schema for instance "+Console.RED+printSchemaProof.formulaToString(map.get(k).get)+Console.RESET+" :\n" )
        println(clause3)
        val rwclause3 = unfoldSchemaClause(clause3, trsClauseSch, trsSigma, subst)
        println("\n\n\nunfolding : \n\n"+rwclause3)
        println("\n\n\noptimizing : \n\n"+deComposeSClause(rwclause3))

    }
    def ClauseSetSchema(i: Int):Unit = {
      val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero()))); val four = Succ(three); val five = Succ(four)
        val j: IntegerTerm = if (i == 0) zero else if (i == 1) one else if (i == 2) two else if (i == 3) three else if (i == 4) four else five
        val k = IntVar(new VariableStringSymbol("k"))
        val l = IntVar(new VariableStringSymbol("l"))

        val X = sClauseVar("X")
        val g = HOLVar(new VariableStringSymbol("g"), ->(Ti(),Ti()))
        val x = fo2Var(new VariableStringSymbol("x"))

        val a = HOLVar(new VariableStringSymbol("a"), Ti())
        val sigma1_base = sTermN("σ'", zero::Nil)
        val sigma1_rec = sTermN("σ'", Succ(k)::Nil)
        val st1 = sTermN("σ'", k::Nil)
        val rewrite_base1 = a
        val rewrite_step1 = HOLApp(g, st1)
        val P = HOLConst(new ConstantStringSymbol("P"), ->(Ti(), To()))
        val sigma_base = sTermN("σ", zero::x::l::Nil)
        val sigma_rec = sTermN("σ", Succ(k)::x::l::Nil)
        val st = sTermN("σ", k::x::l::Nil)
        val rewrite_base = indexedFOVar(new VariableStringSymbol("x"), l)
        val rewrite_step = HOLApp(g, st)
        var trsSigma = dbTRSsTermN("σ", Pair(sigma_base, rewrite_base), Pair(sigma_rec, rewrite_step))

        val d1base = clauseSetTerm("d1", zero::x::X::Nil)
        val d1step = clauseSetTerm("d1", Succ(k)::x::X::Nil)
        val d2base = clauseSetTerm("d2", zero::x::X::Nil)
        val d2step = clauseSetTerm("d2", Succ(k)::x::X::Nil)
        val d2k = clauseSetTerm("d2", k::x::X::Nil)
        val cstep = clauseSchema("c", Succ(k)::x::X::Nil)
        val cbase = clauseSchema("c", zero::x::X::Nil)
        val Pa = Atom(P, a::Nil)
        val Psig1 = Atom(P, sigma1_rec::Nil)
        val xi = sclTermVar("ξ")
        val pair1base = Pair(d1base, sclPlus(d2base, xi))
        val pair1step = Pair(d1step, sclPlus(d2step, cstep))
        val pair2base = Pair(d2base, nonVarSclause(Pa::Nil, Nil))
        val pair2step = Pair(d2step, sclPlus(d2k, nonVarSclause(Psig1::Nil, Nil)))
        val c1 = clauseSchema("c", k::x::X::Nil)
        val ck = clauseSchema("c", Succ(k)::x::X::Nil)
        val c0 = clauseSchema("c", zero::x::X::Nil)
        val sigma0x0 = sTermN("σ", zero::x::zero::Nil)
        val sigmaskxsk = sTermN("σ", Succ(k)::x::Succ(k)::Nil)
        val Psigma0x0 = Atom(P, sigma0x0::Nil)
        val Psigmaskxsk = Atom(P, sigmaskxsk::Nil)
        val clauseSchBase: sClause = sClauseComposition(X, nonVarSclause(Nil, Psigma0x0::Nil))
        val clauseSchRec: sClause = sClauseComposition(c1, nonVarSclause(Nil, Psigmaskxsk::Nil))
        val trsClauseSch = dbTRSclauseSchema("c", Pair(c0, clauseSchBase), Pair(ck, clauseSchRec))
        //      val trsSigma = dbTRSsTermN("σ'", Pair(sigma1_base, rewrite_base1), Pair(sigma1_rec, rewrite_step1))
        trsSigma = trsSigma.add("σ'", Pair(sigma1_base, rewrite_base1), Pair(sigma1_rec, rewrite_step1))
        println("trsSigma : "+trsSigma.map)
        val trsSCLterm = dbTRSclauseSetTerm("d1", pair1base, pair1step)
        trsSCLterm.add("d2", pair2base, pair2step)

        val map = Map[Var, HOLExpression]() + Pair(k.asInstanceOf[Var], j)
        val subst = new SchemaSubstitution3(map)
        println("\n\n\n\n\n\ninstantiating = "+d1step)
        val d1step_ground = applySubToSclauseOrSclauseTerm(subst, d1step)
        println("\narithmetically ground clause schema = "+d1step_ground)

        val unfold_d1step_ground = unfoldClauseSetTerm(d1step_ground, trsSCLterm, trsClauseSch, trsSigma, subst, false, false)
        println("\nclause-set term = "+unfold_d1step_ground)
        val mapX = Map[sClauseVar, sClause]() + Pair(X.asInstanceOf[sClauseVar], nonVarSclause(Nil, Nil))

        val rwd1step_ground = RewriteClauseSchemaInSclauseTerm(unfold_d1step_ground, trsClauseSch, trsSigma, subst, mapX)
        println("\nrewriting = "+rwd1step_ground)

        val rwd1step_ground_toSet = clauseSetTermToSet(rwd1step_ground)
        println("\n\nclause set : \n\n{\n"+rwd1step_ground_toSet.head);rwd1step_ground_toSet.tail.foreach(x => println(" ; "+unfoldSchemaClause(x,trsClauseSch, trsSigma, subst)));println("}")
        //      println(trsSigma.map)
        //      println(trsClauseSch.map)
        val rwrwd1step_ground_toSet = rwd1step_ground_toSet.map(x => unfoldSchemaClause(x, trsClauseSch, trsSigma, subst)  )
        println("\n\nrewriting the clause set = "+rwrwd1step_ground_toSet)

        println(trsSCLterm.map)

        println("\n\n")
        val rhoBase = ResolutionProofSchema("ρ", zero::x::X::Nil)
        val rhoStep = ResolutionProofSchema("ρ", Succ(k)::x::X::Nil)
        val rwBase = rTerm(sClauseComposition(nonVarSclause(Nil, Atom(P, sTermN("σ", zero::x::zero::Nil)::Nil)::Nil), X), nonVarSclause(Atom(P, sTermN("σ'", zero::Nil)::Nil)::Nil , Nil) , Atom(P, sTermN("σ", zero::x::zero::Nil)::Nil))
        val rwStep = rTerm(ResolutionProofSchema("ρ", k::x::sClauseComposition(nonVarSclause(Nil, Atom(P, sTermN("σ", Succ(k)::x::Succ(k)::Nil)::Nil)::Nil), X)::Nil),              nonVarSclause(Atom(P, sTermN("σ'", Succ(k)::Nil)::Nil)::Nil , Nil) , Atom(P, sTermN("σ", Succ(k)::x::Succ(k)::Nil)::Nil))
        resolutionProofSchemaDB.clear
        resolutionProofSchemaDB.add("ρ", Pair(rhoBase, rwBase), Pair(rhoStep, rwStep))
        println("\ntrsRes = "+resolutionProofSchemaDB.map )
        println("\n\n")
    }
  }



  //unfolding a proof for a concrete instance
  object unfoldProof {
    def apply(name: String, i:Int): LKProof = {
      applySchemaSubstitution2(name, i)
    }

    def apply(i: Int): Unit = {
      val s = new InputStreamReader(new FileInputStream("/home/cvetan/gapt-trunk/source/integration_tests/simple_schema_test/src/test/resources/sINDauto.lks"))
        val map = sFOParser.parseProof(s)
        def f = HOLConst(new ConstantStringSymbol("f"), Ti()->Ti())
        def h = HOLConst(new ConstantStringSymbol("h"), ->(Tindex() , ->(Ti(), Ti())))
        def g = HOLConst(new ConstantStringSymbol("g"), ->(Tindex() , ->(Ti(), Ti())))
        val k = IntVar(new VariableStringSymbol("k"))
        val x = hol.createVar(new VariableStringSymbol("x"), Ti(), None).asInstanceOf[HOLVar]
        val base1 = sTerm(g, IntZero(), x::Nil)
        val step1 = sTerm(g, Succ(k), x::Nil)
        val base2 = x
        val step2 = foTerm("f",  sTerm(g, Succ(k), x::Nil)::Nil)
        dbTRS.clear
        dbTRS.add(g, Tuple2(base1, base2), Tuple2(step1, step2))

        //      val varphi = applySchemaSubstitution2("\\varphi",1, db)
        //      va
        // l varphi = applySchemaSubstitution2("\\tau",1, db)
        val sigma = applySchemaSubstitution2("\\sigma",i)
        //Main.display("sigma", sigma);
        //while(true){}
    }
  }

  object goat {
    lazy val (proof, endsequent) = loadProver9Proof( "provers/prover9/src/test/resources/PUZ047+1.out")
    lazy val lkproof = loadProver9LKProof( "provers/prover9/src/test/resources/PUZ047+1.out")
  }

  object hol2fol {

    def apply(term: HOLExpression) : FOLExpression =
      reduceHolToFol( term )

    def apply(term: HOLFormula) : FOLFormula =
      reduceHolToFol( term  )

  }


  object philsci {
    def apply : (LKProof, LKProof) = {
      val p1= parse fol "B"
      val p2= parse fol "A"
      val q = parse fol "C"

      val r1 = Axiom(p1::Nil,p1::Nil)
      val r1_ = Axiom(p1::Nil,p1::Nil)
      val r2 = Axiom(p2::Nil,p2::Nil)
      val r3 = Axiom(q::Nil,q::Nil)
      val r4 = OrLeftRule(r2,r1, r2.root.antecedent(0), r1.root.antecedent(0) )
      val r5 = NegLeftRule(r4, r4.root.succedent(1))
      val r6 = ImpRightRule(r5, r5.root.antecedent(1), r5.root.succedent(0))

      val r7 = NegLeftRule(r1_,r1_.root.succedent(0))
      val r8 = NegRightRule(r7, r7.root.antecedent(0))
      val r9 = WeakeningLeftRule(r3, p2)
      val r10 = ImpLeftRule(r8,r9,r8.root.succedent(0), r9.root.antecedent(1))
      val r11 = CutRule(r6, r10, r6.root.succedent(0), r10.root.antecedent(2))

      val proj = at.logic.transformations.ceres.projections.Projections(r11).toList
      val acnf1 = CutRule(proj(0), proj(1), proj(0).root.succedent(1), proj(1).root.antecedent(0))
      val acnf2 = ContractionLeftRule(acnf1, acnf1.root.antecedent(2), acnf1.root.antecedent(4))
      val acnf3 = ContractionRightRule(acnf2, acnf2.root.succedent(1), acnf2.root.succedent(2))
      val acnf4 = ContractionLeftRule(acnf3, acnf3.root.antecedent(0), acnf3.root.antecedent(3))
      val acnf5 = ContractionLeftRule(acnf4, acnf4.root.antecedent(0), acnf4.root.antecedent(1))

      (r11, acnf5)
    }

  }

  object equation_example {
    def apply : (LKProof, Substitution[HOLExpression]) = {
      import at.logic.calculi.lk.propositionalRules._
      import at.logic.calculi.lk.equationalRules._
      import at.logic.calculi.lk.quantificationRules._
      val List(uv,fuu,fuv,ab,fab) = List("u = v", "f(u)=f(u)", "f(u)=f(v)", "a=b", "f(a)=f(b)") map (Prover9TermParserLadrStyle.parseFormula)
      val List(uy,xy,ay) = List("(all y (u = y -> f(u) = f(y)))",
        "(all x all y (x = y -> f(x) = f(y)))",
        "(all y (a = y -> f(a) = f(y)))") map (Prover9TermParserLadrStyle.parseFormula)
      val List(u,v) = List("u","v").map(s => FOLVar(VariableStringSymbol(s)))
      val List(a,b) = List("a","b").map(s => FOLConst(ConstantStringSymbol(s)))
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
      val i7 = ForallLeftRule(i6, i6.root.antecedent(1),xy, a)

      val es = CutRule(i4,i7,i4.root.succedent(0),i7.root.antecedent(1))

      val sub = Substitution[HOLExpression]((u,b))
      (es, sub)
    }
  }


  object help {
    def apply() = {
      val msg =
        """
          | Available commands:
          |
          | Parsing:
          |   parse.fol: String => FOLFormula - example: \"Forall x Imp P(x,f(x)) Exists y P(x,y)\"
          |   parse.hol: String => HOLExpression
          |   parse.slk: String => Map[String, Pair[LKProof, LKProof]]
          |   parse.lisp: String => List[SExpression]
          |
          | File Input/Output:
          |   loadProofDB: String => ProofDatabase - load proofdatabase from xml file
          |   loadProofs: String => List[(String, LKProof)] - load proofs from xml file as name/value pairs
          |   loadIvyProof: String => RobinsonResolutionProof - load a proof in the ivy proof checker format
          |   loadProver9Proof: String => (RobinsonResolutionProof, FSequent) - load a proof in the ivy proof checker format and extract its endsequent
          |   loadProver9LKProof: String => LKProof - load a proof in the ivy proof checker format and convert it to a LK Proof
          |   loadHLK : String => LKProof - load a proof in the HLK 2 format from given filename
          |   loadVeriTProof : String => (Seq[ExpansionTree], Seq[ExpansionTree]) - loads a veriT proof in the form of an expansion proof.
          |   exportXML: List[Proof], List[String], String => Unit
          |   exportTPTP: List[Proof], List[String], String => Unit
          |
          | Automated Deduction:
          |   refuteFOL: Seq[Clause] => Option[ResolutionProof[Clause]] - call internal resolution prover TAP
          |   refuteFOLI: Seq[Clause] => Option[ResolutionProof[Clause]] - simple interactive refutation
          |   prover9: List[Sequent],Seq[Clause] => Option[ResolutionProof[Clause]] - call prover9
          |   prover9: String => Option[ResolutionProof[Clause]] - call prover9 on given Ladr file
          |   prover9.refuteTPTP:  String => Option[ResolutionProof[Clause]] - call prover9 on given TPTP file
          |   proveProp: FSequent => Option[LKProof] - tableau-like proof search for propositional logic
          |   toClauses: HOLFormula => Set[FClause] - the clause set representation of the given formula
          |   miniSATsolve: HOLFormula => Option[Interpretation] - obtain a model for a quantifier-free formula using MiniSAT
          |   miniSATprove: HOLFormula => Boolean - check if a quantifier-free formula is valid using MiniSAT
          |
          | Proof Theory:
          |   skolemize: LKProof => LKProof - skolemize the input proof
          |   extractInterpolant: ( LKProof, Set[FormulaOccurrence], Set[FormulaOccurrence] ) => HOLFormula - extract propositional Craig interpolant
          |   extractHerbrandSequent: LKProof => Sequent - extract the Herbrand sequent from a proof without quantified cuts.
          |   extractExpansionTrees: LKProof => (Seq[ExpansionTree],Seq[ExpansionTree) - extract the expansion trees of all formulas in the end sequent from a skolemized proof.
          |   compressExpansionTree: ExpansionTree => MultiExpansionTree - compress the quantifiers in the tree using vectors for the terms.
          |
          | Cut-Elimination by Resolution:
          |   extractStruct: LKProof => Struct
          |   structToClausesList: Struct => List[Sequent]
          |   structToLabelledClausesList: Struct => List[LabelledSequent]
          |
          | Proof Schemata:
          |   parse.slk: String => Map[String, Pair[LKProof, LKProof]]
          |   unfoldProof: (String, Int) => LKProof
          |
          | Cut-Introduction:
          |   cutIntro: LKProof => LKProof
          |   extractTerms: LKProof => FlatTermSet - extract the witnesses of the existential quantifiers of the end-sequent of a proof
          |   computeGrammars: FlatTermSet => List[Grammar] - computes all the grammars of a given list of terms (returns a list ordered by symbolic complexity)
          |   seeNFirstGrammars: List[Grammar], Int => Unit - prints the first n grammars from a list
          |   generateExtendedHerbrandSequent: Sequent, Grammar => ExtendedHerbrandSequent - generates the Extended Herbrand Sequent from an end-sequent of a proof and a grammar
          |   computeCanonicalSolution: Sequent, Grammar => FOLFormula - computes the canonical solution for the cut-introduction problem
          |   minimizeSolution: ExtendedHerbrandSequent => Unit - updates the solution associated with this extended Herbrand sequent to the minimal one
          |   buildProofWithCut: ExtendedHerbrandSequent => LKProof - builds a proof with one cut based on the extended Herbrand sequent
          |
          | Visualization:
          |   prooftool: LKProof => Unit - visualize proof in prooftool
          |
          | Uncategorized:
          |   hol2fol: HOLExpression => FOLExpression
          |   hol2fol: HOLFormula => FOLFormula
          |   regularize: LKProof => LKProof - regularize the given LK proof
          |   rename: (LambaExpression, Map[String, (Int,String)]) => LambdaExpression - use map from oldname to (arity, newname) to rename constants in a given LambdaExpressions
          |   rename: (RobinsonResolutionProof, Map[String, (Int,String)]) => RobinsonResolutionProof - the same for resolution proofs
          |   printProofStats: LKProof => Unit
          |   lkTolksk: LKProof => LKProof
          |   createHOLExpression: String => HOLExpression (Forall x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x2: i, c1: (i -> i)))
          |   fsequent2sequent: FSequent => Sequent
          |   deleteTautologies: List[FSequent] => List[FSequent]
          |   removeDuplicates: List[FSequent] => List[FSequent]
          |   unitResolve: List[FSequent] => List[FSequent]
          |   removeSubsumed: List[FSequent] => List[FSequent]
          |   normalizeClauses: List[FSequent] => List[FSequent]
          |   writeLatex: List[FSequent], String => Unit
          |   writeLabelledSequentListLatex: List[LabelledSequent], String => Unit
          |
          | General:
          |   help    : this help text
          |   copying : print redistribution conditions
          |   license : print the text of GNU General Public License
        """.stripMargin

        println(msg)


    }
  }
}
