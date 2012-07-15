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
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.base.FSequent

import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.lksk.base._
import at.logic.algorithms.subsumption._
import at.logic.transformations.skolemization.lksk.LKtoLKskc
import at.logic.transformations.ceres.struct._
import at.logic.algorithms.fol.hol2fol._

import java.util.zip.GZIPInputStream
import java.io.{FileReader, FileInputStream, InputStreamReader, FileWriter => JFileWriter, BufferedWriter=>JBufferedWriter}
import java.io.File.separator
import scala.collection.mutable.Map
import scala.collection.immutable.HashSet

import at.logic.algorithms.unification.hol._

import at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
import at.logic.calculi.resolution.robinson.{Clause}
import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import at.logic.language.fol.{FOLExpression, FOLTerm}
import at.logic.calculi.resolution.base.ResolutionProof
import at.logic.provers.atp.commands.refinements.base.SequentsMacroCommand
import at.logic.provers.atp.commands.refinements.simple.SimpleRefinementGetCommand
import at.logic.provers.atp.Prover
import at.logic.parsing.language.simple.SimpleFOLParser
import at.logic.language.lambda.substitutions.Substitution


import at.logic.gui.prooftool.gui.Main

import  at.logic.calculi.lk.base.types._

import at.logic.algorithms.cutIntroduction._

package GAPScalaInteractiveShellLibrary {
import java.io.IOException
import at.logic.provers.atp.commands.sequents.SetTargetClause
import at.logic.provers.prover9.commands.Prover9InitCommand
import at.logic.provers.atp.commands.base.SetStreamCommand
import base.FSequent
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.transformations.skolemization.skolemize
import at.logic.algorithms.unification.{MulACEquality, MulACUEquality}
import at.logic.calculi.lkmodulo.EequalityA
import at.logic.algorithms.fol.hol2fol.reduceHolToFol
import definitionRules.{DefinitionRightRule, DefinitionLeftRule}
import at.logic.language.lambda.typedLambdaCalculus.{Var, LambdaExpression}
import propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.language.lambda.types.Definitions._
import at.logic.calculi.resolution.robinson._
import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL

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

  object printProofStats {
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
    //def apply(ls: List[Sequent]) = at.logic.algorithms.lk.simplification.deleteTautologies( ls map (_.toFSequent) )
    def apply(ls: List[FSequent]) = at.logic.algorithms.lk.simplification.deleteTautologies( ls )
  }

  object deleteEquationalTautologies {
    private val counter = new {private var state = 0; def nextId = { state = state +1; state}}
    private val emptymap = Map[LambdaExpression, ConstantStringSymbol]()
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
  
  object createEquality {
    def apply(fs : List[String], cs : List[String]) =
      new MulACUEquality(fs map (new ConstantStringSymbol(_)), cs map (new ConstantStringSymbol(_)))

    def apply(fs : List[String]) =
      new MulACEquality(fs map (new ConstantStringSymbol(_)))
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

  object LinearExampleTermset {
    def apply( n : Int) = at.logic.testing.LinearExampleTermset( n )
  }

  object LinearExampleProof {
    def apply( n : Int) = at.logic.testing.LinearExampleProof( n )
  }

  object SquareDiagonalExampleProof {
    def apply( n : Int) = at.logic.testing.SquareDiagonalExampleProof( n )
  }

  object SquareEdgesExampleProof {
    def apply( n : Int) = at.logic.testing.SquareEdgesExampleProof( n )
  }

  object SumExampleProof {
    def apply( n : Int) = at.logic.testing.SumExampleProof( n )
  }

  object termsExtraction {
    def apply( p : LKProof) = at.logic.algorithms.cutIntroduction.termsExtraction( p )
  }

  object termsExtractionFlat {
    def apply( p : LKProof) = at.logic.algorithms.cutIntroduction.termsExtraction( p ).
    //foldLeft( new HashSet[FOLTerm]() )( (s, l) => s ++ l._2 )
      foldRight(List[FOLTerm]()) ( (t, acc) => 
        t._2.foldRight(acc) ((lst, ac) =>
          lst ++ ac
        )
      )
  }

  object cutIntro {
    def apply(p : LKProof) = {
      cutIntroduction(p)
    }
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
      new Prover[at.logic.calculi.resolution.robinson.Clause]{}.
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
      new Prover[at.logic.calculi.resolution.robinson.Clause]{}.
        refute(Stream.cons(SetClausesCommand(clauses), stream)).next
  }

  object prover9 {
    private class MyParser(str: String) extends StringReader(str) with SimpleResolutionParserFOL
    def apply1(clauses: String): Option[ResolutionProof[Clause]] = {
      apply(new MyParser(clauses).getClauseList)
    }

    def apply(clauses: Seq[FSequent]): Option[ResolutionProof[Clause]] =
      try {
         new Prover[at.logic.calculi.resolution.robinson.Clause]{}.
          refute(Stream(SetTargetClause(FSequent(List(),List())), Prover9InitCommand(clauses), SetStreamCommand())).next
      } catch {
        case e: IOException => throw new IOException("Prover9 is not installed: " + e.getMessage())
      }
  }

  object replay {
    def apply = prover9.apply _
  }

  object format {
    def apply(p: ResolutionProof[Clause]) = asHumanReadableString(p)

    def asHumanReadableString(p: ResolutionProof[Clause]) = Formatter.asHumanReadableString(p)
    def asGraphVizString(p:ResolutionProof[Clause]) = Formatter.asGraphViz(p)
    def asTex(p:ResolutionProof[Clause]) = Formatter.asTex(p)
  }

  object ceres {
    def help = ceresHelp.apply
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

  object normalizeSub{
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
    def apply[V <: Sequent](p: at.logic.calculi.treeProofs.TreeProof[V]) = Main.display("proof", p)
  }

  object findDefinitions {
    def apply(p: LKProof) = definitions_(p, collection.immutable.Map[HOLFormula, HOLFormula]())
    
    def definitions_(p: LKProof, m : collection.immutable.Map[HOLFormula, HOLFormula])
      : collection.immutable.Map[HOLFormula, HOLFormula] = p match {
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

  object ceresHelp {
    def apply() = {
      println("Available commands:")
      println("loadProofs: String => List[(String, LKProof)]")
      println("loadProofDB: String => ProofDatabase")
      println("printProofStats: LKProof => Unit")
      println("lkTolksk: LKProof => LKProof")
      println("extractStruct: LKProof => Struct")
      println("structToClausesList: Struct => List[Sequent]")
      println("structToLabelledClausesList: Struct => List[LabelledSequent]")
      println("createHOLExpression: String => HOLExpression (Forall x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x2: i, c1: (i -> i)))")
      println("regularize: LKProof => LKProof")
      println("skolemize: LKProof => LKProof")
      println("fsequent2sequent: FSequent => Sequent")
      println("deleteTautologies: List[FSequent] => List[FSequent]")
      println("removeDuplicates: List[FSequent] => List[FSequent]")
      println("unitResolve: List[FSequent] => List[FSequent]")
      println("removeSubsumed: List[FSequent] => List[FSequent]")
      println("normalizeClauses: List[FSequent] => List[FSequent]")
      println("writeLatex: List[FSequent], String => Unit")
      println("writeLabelledSequentListLatex: List[LabelledSequent], String => Unit")
      println("parse fol: String => FOLTerm")
      println("parse hol: String => HOLExpression")
      println("exportXML: List[Proof], List[String], String => Unit")
      println("exportTPTP: List[Proof], List[String], String => Unit")
      println("refuteFOL: Seq[Clause] => Option[ResolutionProof[Clause]]")
      println("refuteFOLI: Seq[Clause] => Option[ResolutionProof[Clause]] - simple interactive refutation")
      println("prooftool: LKProof => Unit - visualize proof in prooftool")
      println("decompose: String => Unit - take a list of terms (as a string with each term separated by a semi-colon) and shows the decompositions")
      println("LinearExampleTermset: Int => Set[FOLTerm] - construct the linear example termset for cut-introduction")
      println("LinearExampleProof: Int => LKProof - construct the linear example proof for cut-introduction")
      println("SquareDiagonalExampleProof: Int => LKProof - construct the square (diagonal) example proof for cut-introduction")
      println("SquareEdgesExampleProof: Int => LKProof - construct the square (edges) example proof for cut-introduction")
      println("SumExampleProof: Int => LKProof - construct the sum example proof for cut-introduction")
      println("termsExtraction: LKProof => List[List[FOLTerm]] - extract the witnesses of the existential quantifiers of the end-sequent of a proof (as a list of lists)")
      println("termsExtractionFlat: LKProof => Set[FOLTerm] - extract the witnesses of the existential quantifiers of the end-sequent of a proof (as a ,,flat'' set)")
    }
  }
}
