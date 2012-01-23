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
    def stream: Stream[Command[Clause]] = Stream.cons(SetTargetClause((List(),List())), Stream.cons(SearchForEmptyClauseCommand[Clause], stream1))

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
    def stream: Stream[Command[Clause]] = Stream.cons(SetTargetClause((List(),List())), Stream.cons(SearchForEmptyClauseCommand[Clause], stream1))

    def apply(clauses: Seq[FSequent]): Option[ResolutionProof[Clause]] =
      new Prover[at.logic.calculi.resolution.robinson.Clause]{}.
        refute(Stream.cons(SetClausesCommand(clauses), stream)).next
  }

  object prover9 {
    def apply(clauses: Seq[FSequent]): Option[ResolutionProof[Clause]] =
      try {
         new Prover[at.logic.calculi.resolution.robinson.Clause]{}.
          refute(Stream(SetTargetClause((List(),List())), Prover9InitCommand(clauses), SetStreamCommand())).next
      } catch {
        case e: IOException => throw new IOException("Prover9 is not installed: " + e.getMessage())
      }
  }
  object ceres {
    def help = ceresHelp.apply
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


  class ElimEx(val uproofs : List[LKProof], val aux : List[FormulaOccurrence], val prim : HOLFormula, val defs : Option[collection.immutable.Map[FormulaOccurrence, FormulaOccurrence]] ) extends Exception {
    override def getMessage() = {
      var s = ("proofs:\n\n")
      for (p <- uproofs)
        s = s + p.toString() + "\n"
      s = s + "\nauxiliary formulas:\n\n"
      for (p <- aux)
        s = s + p.toString() + "\n"
      s = s + "\nprimary formula:\n"+ prim +"\n"

      s
    }
  }


  object definitions {
    import collection.immutable.Map
    import collection.immutable.Seq
    type DefinitionsMap = Map[HOLFormula, HOLFormula]
    type ProcessedDefinitionsMap = Map[SymbolA, (List[HOLVar], HOLFormula)]

    private val emptymap = Map[FormulaOccurrence,FormulaOccurrence]() //this will be passed to some functions
    
    
    def fixedpoint_val[A](f : (A=>A), l : A) : A = {
      val r = f(l)
      if (r==l) r  else fixedpoint_val(f,r)
    }

    def fixedpoint_seq[A](f : (A=>A), l : Seq[A] ) : Seq[A] = {
      val r = l map f
      if (r==l) r  else fixedpoint_seq(f,r)
    }

    def recursive_elimination_from(defs: DefinitionsMap, l : FSequent) : FSequent =
      FSequent(recursive_elimination_from(defs,l._1), recursive_elimination_from(defs,l._2))

    def recursive_elimination_from(defs: DefinitionsMap, l : Seq[HOLFormula]) : Seq[HOLFormula] =
      fixedpoint_seq(((x:HOLFormula) => eliminate_from(defs,x)), l )

    def recursive_elimination_from(defs: DefinitionsMap, l : HOLFormula) : HOLFormula =
      fixedpoint_val(((x:HOLFormula) => eliminate_from(defs,x)), l )

    def eliminate_from(defs : DefinitionsMap, f : HOLFormula) : HOLFormula = {
      //preprocess definitions
      var map : ProcessedDefinitionsMap = Map[SymbolA, (List[HOLVar], HOLFormula)]()
      //TODO: expand definitions in map
      for (k <- defs.keys) k match {
        case Atom(sym, args) =>
          if (args forall (_.isInstanceOf[HOLVar]))
            map = map + Tuple2(sym, (args.asInstanceOf[List[HOLVar]], defs(k)))
          else
            println("Warning: arguments of definition are not variables!")
            args.filterNot(_.isInstanceOf[HOLVar]) map println
        case _ => println("Warning: ignoring non-atomic definition during definition elimination!")
      }
      eliminate_from_(map, f)
    }
    
    private def eliminate_from_(defs : ProcessedDefinitionsMap, f : HOLFormula) : HOLFormula = {
      f match {
        case Atom(sym, args) =>
          defs.get(sym) match {
            case Some((definition_args, defined_formula)) =>
              if (args.length != definition_args.length) {
                println("Warning: ignoring definition replacement because argument numbers dont match!")
                f
              } else {
                //we need to insert the correct values for the free variables in the definition
                //the casting is needed since we cannot make a map covariant
                //val pairs = (definition_args zip args)  filter ((x:(HOLExpression, HOLExpression) ) => x._1.isInstanceOf[HOLVar])
                val pairs = definition_args zip  args
                val sub = Substitution(pairs)
                println("Substitution:")
                println(sub)
                sub.apply(defined_formula).asInstanceOf[HOLFormula]
              }
            case _ => f
          }
        case Neg(f1) => Neg(eliminate_from_(defs, f1))
        case AllVar(q,f1) => AllVar(q, eliminate_from_(defs, f1))
        case ExVar(q,f1) => ExVar(q, eliminate_from_(defs, f1))
        case And(f1,f2) => And(eliminate_from_(defs, f1), eliminate_from_(defs, f2))
        case Imp(f1,f2) => Imp(eliminate_from_(defs, f1), eliminate_from_(defs, f2))
        case Or(f1,f2)  => Or(eliminate_from_(defs, f1), eliminate_from_(defs, f2))
        case _ => println("Warning: unhandled case in definition elimination!"); f
      }
    }


    def handleWeakeningRule(defs: definitions.DefinitionsMap,
                            uproof: LKProof, root: Sequent, prin: FormulaOccurrence,
                             createRule : (LKProof,  HOLFormula) => LKProof )
    : (Map[FormulaOccurrence,FormulaOccurrence], LKProof) = {
      val (dmap, duproof) = eliminate_in_proof_(defs, uproof)
      val dproof = createRule(duproof, recursive_elimination_from(defs, prin.formula))
      val correspondences = calculateCorrespondences(defs, root, dproof)
      (correspondences, dproof)
    }

    def handleContractionRule(defs: definitions.DefinitionsMap,
                              uproof: LKProof,
                              root: Sequent, aux1: FormulaOccurrence, aux2: FormulaOccurrence,
                              createRule : (LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof)
    : (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
      val (dmap, duproof) = eliminate_in_proof_(defs, uproof)
      println("Contracting from: "+aux1+" and "+ aux2)
      println("Contracting to:   "+dmap(aux1)+" and "+ dmap(aux2))
      throw new ElimEx(uproof::duproof::Nil, aux1::aux2::Nil, uproof.root.toFormula, Some(dmap))

      val dproof = createRule(duproof, dmap(aux1), dmap(aux2))
      val correspondences = calculateCorrespondences(defs, root, dproof)
      (correspondences, dproof)
    }

    def handleNegationRule(defs: definitions.DefinitionsMap, uproof: LKProof, root: Sequent,
                               aux: FormulaOccurrence,
                               createRule : (LKProof, FormulaOccurrence) => LKProof)
    : (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
      val (dmap,duproof) = eliminate_in_proof_(defs, uproof)
      val dproof = createRule(duproof, dmap(aux) )
      val correspondences = calculateCorrespondences(defs, root, dproof)
      (correspondences,  dproof)
    }

    //only handles AndL1,2 and OrR1,2 -- ImpR and NegL/R are different
    def handleUnaryLogicalRule(defs: definitions.DefinitionsMap, uproof: LKProof, root: Sequent,
                              aux: FormulaOccurrence, prin : FormulaOccurrence,
                              createRule : (LKProof, FormulaOccurrence, HOLFormula) => LKProof)
    : (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
      val (dmap,duproof) = eliminate_in_proof_(defs, uproof)
      val dproof = createRule(duproof, dmap(aux), recursive_elimination_from(defs,prin.formula)  )
      val correspondences = calculateCorrespondences(defs, root, dproof)
      (correspondences,  dproof)
    }


    def handleBinaryLogicalRule(defs: definitions.DefinitionsMap, uproof1: LKProof, uproof2: LKProof,
                               root: Sequent, aux1: FormulaOccurrence, aux2: FormulaOccurrence,
                               prin : FormulaOccurrence,
                               createRule : (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof)
    : (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
      val (dmap1,duproof1) = eliminate_in_proof_(defs, uproof1)
      val (dmap2,duproof2) = eliminate_in_proof_(defs, uproof2)
//      val correspondences1 = calculateCorrespondences(defs, emptymap, root, duproof1)
//      val correspondences2 = calculateCorrespondences(defs, correspondences1, root, duproof2)

      val dproof = createRule(duproof1, duproof2, dmap1(aux1), dmap2(aux2)  )
      val correspondences = calculateCorrespondences(defs, root, dproof)
      (correspondences,  dproof)
    }


    def handleQuantifierRule[T <: HOLExpression](defs: definitions.DefinitionsMap, uproof: LKProof, root: Sequent,
                               aux: FormulaOccurrence, prin : FormulaOccurrence, substituted_term : T,
                               createRule : (LKProof, FormulaOccurrence, HOLFormula, T) => LKProof)
    : (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
      val (dmap,duproof) = eliminate_in_proof_(defs, uproof)
      //TODO: take care of function definitions in substituted term
      val dproof = createRule(duproof, dmap(aux), recursive_elimination_from(defs,prin.formula),  substituted_term   )
      val correspondences = calculateCorrespondences(defs, root, dproof)
      (correspondences,  dproof)
    }


    def handleEquationalRule(defs: definitions.DefinitionsMap, uproof1: LKProof, uproof2: LKProof,
                                root: Sequent, aux1: FormulaOccurrence, aux2: FormulaOccurrence,
                                prin : FormulaOccurrence,
                                createRule : (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence, HOLFormula) => LKProof)
    : (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
      val (dmap1,duproof1) = eliminate_in_proof_(defs, uproof1)
      val (dmap2,duproof2) = eliminate_in_proof_(defs, uproof2)
      val correspondences1 = calculateCorrespondences2(defs, emptymap, root, duproof1)
      val correspondences2 = calculateCorrespondences2(defs, correspondences1, root, duproof2)

      val dproof = createRule(duproof1, duproof2, dmap1(aux1), dmap2(aux2) , correspondences2(prin).formula )
      (correspondences2,  dproof)
    }

    def handleDefinitionRule(defs: definitions.DefinitionsMap, uproof: LKProof, root: Sequent,
                              aux: FormulaOccurrence, prin : FormulaOccurrence,
                              createRule : (LKProof, FormulaOccurrence, HOLFormula) => LKProof)
    : (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
      val (dmap,duproof) = eliminate_in_proof_(defs, uproof)
      val elim_prin = recursive_elimination_from(defs,prin.formula)
      if (elim_prin == dmap(aux).formula ) {
        println("eliminating: "+prin)
        (dmap, duproof)
      } else {
        println("not eliminating:" + prin)
//        println("trying with: "+duproof.vertex + " ::: " + dmap(aux) +" / " +aux + " ::: " + elim_prin  )
        try {
          val dproof = createRule(duproof, dmap(aux), elim_prin)

          val correspondences = calculateCorrespondences(defs, root, dproof)

          check_map(correspondences, root, dproof.root)
          (correspondences,  dproof)
        } catch {
          case e: ElimEx => throw e
          case e:Exception =>
            println("exception!")
            e.printStackTrace()

            throw new ElimEx(List(duproof), List(aux,dmap(aux)), elim_prin, None)
        }
      }
    }

    def check_map(map : collection.immutable.Map[FormulaOccurrence, FormulaOccurrence], proof: LKProof) : Boolean = {
      val ant = proof.root.antecedent
      val succ = proof.root.succedent
      for (el <- map.values) {
        println("searching for "+System.identityHashCode(el))
        if ((! ant.contains(el)) && (! succ.contains(el)))
          throw new ElimEx(proof::Nil, el::Nil, el.formula, Some(map))
      }
      true
    }

    def check_map(map : collection.immutable.Map[FormulaOccurrence, FormulaOccurrence], proof: LKProof, dproof : LKProof) : Boolean =
      check_map(map, proof.root, dproof.root)


    def check_map(map : collection.immutable.Map[FormulaOccurrence, FormulaOccurrence], root: Sequent, droot : Sequent) : Boolean = {
      var error = false
      for (fo <- root.antecedent) {
        if (! (map.keySet contains fo)) {
          println("PROBLEM: map does not contain "+fo.id)
          error = true
        }
        else
        if (! (droot.antecedent contains map(fo))) {
          println("PROBLEM: FO #" + fo.id, " maps to "+map(fo).id + ", but is not present in antecedent of new root!")
          error = true
        }
      }
      for (fo <- root.succedent) {
        if (! (map.keySet contains fo)) {
          println("PROBLEM: map does not contain "+fo.id)
          error = true
        }
        else
        if (! (droot.succedent contains map(fo))) {
          println("PROBLEM: FO #" + fo.id, " maps to "+map(fo).id + ", but is not present in succedent of new root!")
          error = true
        }
      }
      
      if (error) {
        print_hashcodes("Original Proof:", root )
        print_hashcodes("Modified Proof:", droot )
        print_hashcodes("Map:", map )
      }

      error
    }



    def print_hashcodes(msg: String, s:Sequent) = {
      println(msg)
      println(s)
      print(s.antecedent map  ((x:FormulaOccurrence) => x.id))
      print(" :- ")
      print(s.succedent map  ((x:FormulaOccurrence) => x.id))
      println
    }

    def print_hashcodes(msg: String, m : Map[FormulaOccurrence, FormulaOccurrence]) = {
      println(msg)
      println(m)
      println(m map ((x:(FormulaOccurrence,FormulaOccurrence)) => (x._1.id,x._2.id)))
    }

    //eliminates defs in proof and returns a mapping from the old aux formulas to the new aux formulas
    // + the proof with the definition removed
    def eliminate_in_proof_(defs : DefinitionsMap, proof : LKProof) :
      (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
      proof match {
        // introductory rules
        case Axiom(Sequent(antecedent, succedent)) =>
          println("Axiom!")
          val antd  = recursive_elimination_from(defs,antecedent.map((x:FormulaOccurrence) => x.formula))
          val succd = recursive_elimination_from(defs,succedent.map((x:FormulaOccurrence) => x.formula))
          val sequent = fsequent2sequent.apply( (antd,succd) )
          val dproof = Axiom(sequent)
//          val correspondences = emptymap ++ ((antecedent ++ succedent) zip (duproof.root.antecedent ++ duproof.root.succedent))
          val correspondences = calculateCorrespondences(defs,Sequent(antecedent, succedent) , dproof)

          check_map(correspondences, proof, dproof)

          (correspondences, dproof)

        /* in the following part, dmap[1,2] holds the old correspondences of the upper subproof(s), needed to map the auxiliary formulas to the
         * ones with removed definitions; correspondences holds the new mapping. */
        //structural rules
        case CutRule(uproof1,uproof2,root,aux1,aux2) =>
          println("Cut!")
          val (dmap1,duproof1) = eliminate_in_proof_(defs, uproof1)
          val (dmap2,duproof2) = eliminate_in_proof_(defs, uproof2)
          //val correspondences1 = calculateCorrespondences(defs, emptymap, root, duproof1)
          //val correspondences2 = calculateCorrespondences(defs, correspondences1, root, duproof2)

          val dproof = CutRule(duproof1,  duproof2,  dmap1(aux1), dmap2(aux2))
          val correspondences = calculateCorrespondences(defs, root, dproof)
          (correspondences, dproof )

        case WeakeningLeftRule(uproof, root, prin) =>
          println("Weakening Left!")
          handleWeakeningRule(defs, uproof, root, prin, WeakeningLeftRule.apply)

        case WeakeningRightRule(uproof, root, prin) =>
          println("Weakening Right!")
          handleWeakeningRule(defs, uproof, root, prin, WeakeningRightRule.apply)

        case ContractionLeftRule(uproof, root, aux1, aux2, prim) =>
          println("Contraction Left!")
          handleContractionRule(defs, uproof, root, aux1, aux2, ContractionLeftRule.apply)

        case ContractionRightRule(uproof, root, aux1, aux2, prim) =>
          println("Contraction Right!")
          handleContractionRule(defs, uproof, root, aux1, aux2, ContractionRightRule.apply)

        //logical rules
        case NegLeftRule(uproof, root, aux, prin)  =>
          println("Negation Left!")
          handleNegationRule(defs, uproof, root, aux, NegLeftRule.apply)

        case NegRightRule(uproof, root, aux, prin)  =>
          println("Negation Right!")
          handleNegationRule(defs, uproof, root, aux, NegRightRule.apply)

        case AndLeft1Rule(uproof, root, aux, prin)  =>
          println("And 1 Left!")
          handleUnaryLogicalRule(defs, uproof, root, aux, prin, AndLeft1Rule.apply )

        case AndLeft2Rule(uproof, root, aux, prin)  =>
          println("And 2 Left!")
          handleUnaryLogicalRule(defs, uproof, root, aux, prin, switchargs(AndLeft2Rule.apply) )

        case AndRightRule(uproof1, uproof2, root, aux1, aux2, prin)  =>
          println("And Right")
          handleBinaryLogicalRule(defs, uproof1, uproof2, root, aux1, aux2, prin, AndRightRule.apply)

        case OrRight1Rule(uproof, root, aux, prin)  =>
          println("Or 1 Right")
          handleUnaryLogicalRule(defs, uproof, root, aux, prin, OrRight1Rule.apply )

        case OrRight2Rule(uproof, root, aux, prin)  =>
          println("Or 2 Right")
          handleUnaryLogicalRule(defs, uproof, root, aux, prin, switchargs(OrRight2Rule.apply) )

        case OrLeftRule(uproof1, uproof2, root, aux1, aux2, prin)  =>
          println("Or Left!")
          handleBinaryLogicalRule(defs, uproof1, uproof2, root, aux1, aux2, prin, OrLeftRule.apply)

        case ImpLeftRule(uproof1, uproof2, root, aux1, aux2, prin)  =>
          println("Imp Left")
          handleBinaryLogicalRule(defs, uproof1, uproof2, root, aux1, aux2, prin, ImpLeftRule.apply)

        case ImpRightRule(uproof, root, aux1, aux2, prin)  =>
          println("Imp Right")
          val (dmap,duproof) = eliminate_in_proof_(defs, uproof)
          val dproof = ImpRightRule(duproof, dmap(aux1), dmap(aux2)  )
          val correspondences = calculateCorrespondences(defs, root, duproof)
          (correspondences,  dproof)

        //quantfication rules
        case ForallLeftRule(uproof, root, aux, prim, substituted_term) =>
          println("Forall Left")
          handleQuantifierRule(defs, uproof, root, aux, prim, substituted_term, ForallLeftRule.apply)
        case ForallRightRule(uproof, root, aux, prim, substituted_term) =>
          println("Forall Right")
          handleQuantifierRule(defs, uproof, root, aux, prim, substituted_term, ForallRightRule.apply)
        case ExistsLeftRule(uproof, root, aux, prim, substituted_term) =>
          println("Exists Left")
          handleQuantifierRule(defs, uproof, root, aux, prim, substituted_term, ExistsLeftRule.apply)
        case ExistsRightRule(uproof, root, aux, prim, substituted_term) =>
          println("Exists Right")
          handleQuantifierRule(defs, uproof, root, aux, prim, substituted_term, ExistsRightRule.apply)

        //equational rules
        case EquationLeft1Rule(uproof1, uproof2, root, aux1, aux2, prim) =>
          println("Equation Left 1")
          handleEquationalRule(defs, uproof1, uproof2, root, aux1, aux2, prim, EquationLeft1Rule.apply)
        case EquationLeft2Rule(uproof1, uproof2, root, aux1, aux2, prim) =>
          println("Equation Left 2")
          handleEquationalRule(defs, uproof1, uproof2, root, aux1, aux2, prim, EquationLeft2Rule.apply)
        case EquationRight1Rule(uproof1, uproof2, root, aux1, aux2, prim) =>
          println("Equation Right 1")
          handleEquationalRule(defs, uproof1, uproof2, root, aux1, aux2, prim, EquationRight1Rule.apply)
        case EquationRight2Rule(uproof1, uproof2, root, aux1, aux2, prim) =>
          println("Equation Right 2")
          handleEquationalRule(defs, uproof1, uproof2, root, aux1, aux2, prim, EquationRight2Rule.apply)

        //definition rules
        case DefinitionLeftRule(uproof, root, aux, prin) =>
          println("Def Left")
          handleDefinitionRule(defs, uproof, root, aux, prin, DefinitionLeftRule.apply)


        case DefinitionRightRule(uproof, root, aux, prin) =>
          println("Def Right")
          handleDefinitionRule(defs, uproof, root, aux, prin, DefinitionRightRule.apply)

      }

    }

    private def append_ancestors(endsequent : FSequent, ancestors : Sequent) =
      Sequent(append_ancestors_(endsequent._1, ancestors.antecedent),
              append_ancestors_(endsequent._2, ancestors.succedent))
    private def append_ancestors_(endsequent : Seq[HOLFormula], ancestors : Seq[FormulaOccurrence]) :
      Seq[FormulaOccurrence] = {
      endsequent.zip(ancestors).map(
        (x:(HOLFormula, FormulaOccurrence)) =>
            x._2.factory.createFormulaOccurrence(x._1, Seq(x._2)  )  )
    }

    //needs a different name because type erasure removes HOLFormula/FormulaOccurrence from append_ancestors(2)_
    private def append_ancestors2(endsequent : Sequent, ancestors : Sequent) =
      Sequent(append_ancestors2_(endsequent.antecedent, ancestors.antecedent),
        append_ancestors2_(endsequent.succedent, ancestors.succedent))
    private def append_ancestors2_(endsequent : Seq[FormulaOccurrence], ancestors : Seq[FormulaOccurrence]) :
    Seq[FormulaOccurrence] = {
      endsequent.zip(ancestors).map(
        (x:(FormulaOccurrence, FormulaOccurrence)) =>
          x._2.factory.createFormulaOccurrence(x._1.formula, x._1.ancestors ++ x._2.ancestors  )  )
    }



    /* calculates the correspondences between occurences of the formulas in the original end-sequent and those in the
    *  definition free one. in binary rules, ancestors may occur in both branches, so we also pass a map with previously
    *  calculated correspondences and add the new ones */
    private def calculateCorrespondences2(defs: definitions.DefinitionsMap,
                                         existing_correspondences : Map[FormulaOccurrence, FormulaOccurrence],
                                         root: Sequent, duproof: LKProof)
      : Map[FormulaOccurrence, FormulaOccurrence] = {
      //
      val eroot_fs = recursive_elimination_from(defs, root.toFSequent())
      val eroot_f = append_ancestors(eroot_fs, duproof.root)
      val additional = (root.antecedent ++ root.succedent) zip (eroot_f.antecedent ++ eroot_f.succedent)
      var correspondences = existing_correspondences
      for ( el@(key,value) <- additional ) {
        //if there are ancestors in both subproofs, the entry needs to be merged
        if (correspondences.contains(key)) {
          val entry = correspondences(key)
          correspondences = correspondences + ((key,(new FormulaOccurrence(entry.formula, entry.ancestors ++ value.ancestors, entry.factory))))

        } else {
          correspondences = correspondences + el
        }

      }

      correspondences
    }

    /* calculates the correspondences between occurences of the formulas in the original end-sequent and those in the
    *  definition free one. in binary rules, ancestors may occur in both branches, so we also pass a map with previously
    *  calculated correspondences and add the new ones */
    private def calculateCorrespondences(defs: definitions.DefinitionsMap,
                                         root: Sequent, duproof: LKProof)
    : Map[FormulaOccurrence, FormulaOccurrence] = {
      val r = emptymap ++ (root.antecedent zip duproof.root.antecedent) ++ (root.succedent zip duproof.root.succedent)
      print_hashcodes("DEBUG: Correspondences", r)
      r
    }

    //switches arguments such that the apply methods of AndL1,2 and OrL1,2 have the same signature
    def switchargs[A,B,C,D](f : (A, B, C) => D) : ((A, C ,B) => D) = ((a:A, c:C ,b:B) => f(a,b,c))

    
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
    }
  }
}
