package at.logic.provers.prover9

/**
 * Created by IntelliJ IDEA.
 * User: shaolin
 * Date: 8/29/11
 * Time: 5:20 PM
 * To change this template use File | Settings | File Templates.
 */

package commands {

import _root_.at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import _root_.at.logic.calculi.lk.base.types.FSequent
import _root_.at.logic.calculi.occurrences.FormulaOccurrence
import _root_.at.logic.calculi.resolution.base.ResolutionProof
import _root_.at.logic.calculi.resolution.robinson.Clause
import _root_.at.logic.language.fol._
import _root_.at.logic.language.hol.logicSymbols.ConstantStringSymbol
import _root_.at.logic.language.hol.replacements.getAtPosition
import _root_.at.logic.language.hol.{HOLExpression, HOLFormula}
import _root_.at.logic.language.lambda.symbols.VariableStringSymbol
import _root_.at.logic.language.lambda.types.Ti
import _root_.at.logic.parsing.language.tptp.TPTPFOLExporter
import _root_.at.logic.provers.atp.commands.base._
import _root_.at.logic.provers.atp.commands.guided.{GetGuidedClausesLiterals, GetGuidedClausesLiteralsPositions, AddGuidedResolventCommand, AddGuidedInitialClauseCommand}
import _root_.at.logic.provers.atp.commands.replay.ReplayNoParamodulationCommand
import _root_.at.logic.provers.atp.commands.robinson.{ResolveCommand, VariantLiteralPositionCommand, VariantLiteralCommand, ParamodulationLiteralPositionCommand}
import _root_.at.logic.provers.atp.commands.sequents.{InsertResolventCommand, SetSequentsCommand}
import _root_.at.logic.provers.atp.Definitions._
import sys.process._
import java.io._
import scala.xml._
import scala.collection.immutable.Seq
import org.xml.sax.InputSource
import javax.xml.parsers.SAXParserFactory
import util.parsing.combinator.JavaTokenParsers
import util.matching.Regex

/**
 * Should translate prover9 justifications into a robinson resolution proof. The justifications are:

Clause Justifications
After the initial stage of the output, each clause in the file has an integer identifier (ID) and a justification that may refer to IDs of other clauses. A justification is a list consisting of one primary step and some number of secondary steps. Most primary steps are inference rules applied to given clauses, and most secondary steps consist of simplification, rewriting, or orienting equalities.

Many of the types of step refer to positions of literals or terms in the parent clauses. Literals are identified by the characters 'a' (first literal), 'b' (second literal), etc. Terms are identified by the literal identifier followed by a sequence of integers giving the position of the term within the literal. For example, the position 'c,1,3,2' means third literal, first argument, third argument, second argument. Negation signs on literals are not included in the sequence.

Primary Steps.

    assumption -- input formula.
    clausify -- from CNF translation of a non-clausal assumption.
    goal -- input formula.
    deny -- from CNF translation of the negation of a goal.
    resolve(59,b,47,c) -- resolve the second literal of clause 59 with the third literal of clause 47.
    hyper(59, b,47,a, c,38,a) -- hyperresolution; interpret the list as a clause ID followed by a sequence of triples, <literal,clause-ID,literal> the inference is presented as a sequence of binary resolution steps. In the example shown, start with clause 59; then resolve literal b with clause 47 on literal a; with the result of the first step, resolve literal c with clause 38 on literal a. The special case "xx" means resolution with x=x.
    ur(39, a,48,a, b,88,a, c,87,a, d,86,a) -- unit-resulting resolution; the list is interpreted as in hyperresolution.
    para(47(a,1),28(a,1,2,2,1)) -- paramodulate from the clause 47 into clause 28 at the positions shown.
    copy(59) -- copy clause 59.
    back_rewite(59) -- copy clause 59.
    back_unit_del(59) -- copy clause 59.
    new_symbol(59) -- introduce a new constant (see parameter new_constants).
    factor(59,b,c) -- factor clause 59 by unifying the second and third literals.
    xx_res(59,b) -- resolve the second literal of clause 59 with x=x.
    propositional -- not used in sandard proofs.
    instantiate -- not used in standard proofs.
    ivy -- not used in standard proofs.

Secondary Steps (each assumes a working clause, which is either the result of a primary step or a previous secondary step).

    rewrite([38(5,R),47(5),59(6,R)]) -- rewriting (demodulation) with equations 38, 47, then 59; the arguments (5), (5), and (6) identify the positions of the rewritten subterms (in an obscure way), and the argument R indicates that the demodulator is used backward (right-to-left).
    flip(c) -- the third literal is an equality that has been flipped by the term ordering. This does not necessarily mean that the equality is orientable by the primary term ordering, e.g., KBO.
    merge(d) -- the fourth literal has been removed because it was identical to a preceding literal.
    unit_del(b,38) -- the second literal has been removed because it was an instance of the negation clause 38 (which is a unit clause).
    xx(b) -- the second literal has been removed because it was an instance of x!=x.
 */

  case class Prover9InitCommand(override val clauses: Iterable[FSequent]) extends SetSequentsCommand[Clause](clauses) {
    def apply(state: State, data: Any) = {

      // execute prover9 and obtain the xml
      val tptp = TPTPFOLExporter.tptp_problem(clauses.toList)
      val buffer = new Array[ Byte ]( 1024 )
      val tptpIS = new ByteArrayInputStream(tptp.getBytes)

      var cmnds = Stream[Command[Clause]]()

      // here we parse the given xml
      val pio = new ProcessIO(
        stdin => {Stream.continually(tptpIS.read(buffer)).takeWhile(_ != -1).foreach(stdin.write(buffer,0,_));stdin.flush;stdin.close}, //writing tptp to program
        stdout => {
          val f = SAXParserFactory.newInstance()
          f.setValidating(false)
          f.setNamespaceAware(false)
          f.setFeature("http://xml.org/sax/features/namespaces", false)
          f.setFeature("http://xml.org/sax/features/validation", false)
          f.setFeature("http://apache.org/xml/features/nonvalidating/load-dtd-grammar", false)
          f.setFeature("http://apache.org/xml/features/nonvalidating/load-external-dtd", false)
          val xml = XML.loadXML(new InputSource(stdout),f.newSAXParser())
          println(xml)
	  // prover9 justifications. We translate the regular ones (factor, res and assumption) and replay the rest
          val AssumptionRE = new Regex("""\[(assumption)\]\.""")
          val FactorRE = new Regex("""\[factor\((\d+\w*),(\w+),(\w+)\)\]\.""")
          val ResolveRE = new Regex("""\[resolve\((\d+\w*),(\w+),(\d+\w*),(\w+)\)\]\.""")
          val ParaRE = new Regex("""\[para\((\d+\w*)\((\w+),(\d+)\),(\d+\w*)\((\w+),(\d+( d+)*)\)\)\]\.""")
          (xml \\ "clause").foreach(e => {
            val cls = getLiterals(e)
            val id = (e\"@id").text
            cmnds = cmnds ++ ((e\\"@jstring").text match {
              case AssumptionRE(_) => assumption(id, cls)
              case FactorRE(parent, lit1, lit2) => factor(parent, lit1, lit2, id, cls)
              case ResolveRE(par1, lit1, par2, lit2) => resolve(par1, lit1, par2, lit2, id, cls)
              case ParaRE(fPar, fLit, fPos, tPar, tLit, tPos, _) => paramodulate(fPar, fLit, fPos.toInt, tPar, tLit, tPos.split("""\s""").map(_.toInt), id, cls)
              case _ => replay(getParents(e), id, cls)
            })
          })
        },
        stderr => {val err:String = scala.io.Source.fromInputStream(stderr).mkString; if (!err.isEmpty) throw new Prover9Exception(err)}
      )

      val p  = "tptp_to_ladr" #| "prover9" #| "prooftrans xml expand"
      val proc = p.run(pio)
      val exitValue = proc.exitValue

      tptpIS.close()

      List((state, cmnds))
    }

    // the second value is the literals permutation from prover9 order to fsequent (as we have positive and negative
    private def getLiterals(e: Node): Seq[FOLFormula] = {
      if ((e \\ "literal").text.trim == "$F") List()
      else (e \\ "literal").map(l => MyParser.parseAll(MyParser.literal, l.text).get)
    }

    private def literals2FSequent(lits: Seq[FOLFormula]): FSequent = {
     (lits.filter(l => l match {
            case Neg(_) => true
            case _ => false})
          .map(l => l match {
            case Neg(f) => f
           }),
      lits.filter(l => l match {
            case Neg(_) => false
            case _ => true}))
    }
    val INT_CHAR = 97

    private def getParents(e: Node): Iterable[String] = (e \\ "@parents").text.split(" ")

    private def assumption(id: String, cls: Seq[FOLFormula]): TraversableOnce[Command[Clause]] = {
      List(AddGuidedInitialClauseCommand(id, cls), InsertResolventCommand[Clause])
    }
    private def factor(parentId: String, lit1: String, lit2: String, id: String, cls: Seq[FOLFormula]): TraversableOnce[Command[Clause]] = {
      throw new Exception("not implemented yet")
    }
    private def resolve(par1Id: String, lit1: String, par2Id: String, lit2: String, id: String, cls: Seq[FOLFormula]): TraversableOnce[Command[Clause]] = {
      /*require(lit1.size == 1 && lit2.size == 1) // the parsing should be changed if the arity of functions is bigger than the english alphabet
      List(GetGuidedClausesLiterals(List((par1Id, lit1.head.toInt - INT_CHAR), (par2Id, lit2.head.toInt - INT_CHAR))), VariantLiteralCommand, ResolveCommand(FOLUnificationAlgorithm), AddGuidedResolventCommand(id))
      */
      replay(List(par1Id,par2Id), id, cls)
    }
    private def paramodulate(fromParentId: String, fromLiteral: Seq[Char], fromPos: Int, toParentId: String, toLiteral: Seq[Char], toPos: Iterable[Int], id: String, cls: Seq[FOLFormula]): TraversableOnce[Command[Clause]] = {
      require(fromLiteral.size == 1 && toLiteral.size == 1) // the parsing should be changed if the arity of functions is bigger than the english alphabet
      List(GetGuidedClausesLiteralsPositions(List((fromParentId, fromLiteral.head.toInt - INT_CHAR, List(fromPos)), (toParentId, toLiteral.head.toInt - INT_CHAR, toPos))), VariantLiteralPositionCommand, ParamodulationLiteralPositionCommand(FOLUnificationAlgorithm), AddGuidedResolventCommand(id))
    }
    private def replay(parentIds: Iterable[String], id: String, cls: Seq[FOLFormula]): TraversableOnce[Command[Clause]] = {
      Stream(ReplayNoParamodulationCommand(parentIds, id, literals2FSequent(cls)), SpawnCommand())
    }

    object MyParser extends JavaTokenParsers {
      def literal: Parser[FOLFormula] = negeq | poseq | negatom | posatom
      def posatom: Parser[FOLFormula] = atom
      def negatom: Parser[FOLFormula] = "-" ~ atom  ^^ {case "-" ~ a => Neg(a)}
      def atom: Parser[FOLFormula] = atom1 | atom2
      def atom1: Parser[FOLFormula] = conssymb ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Atom(new ConstantStringSymbol(x), params.asInstanceOf[List[FOLTerm]])}
      def atom2: Parser[FOLFormula] = conssymb ^^ {case x => Atom(new ConstantStringSymbol(x), Nil)}
      def poseq: Parser[FOLFormula] = term ~ "=" ~ term ^^ {case t1 ~ "=" ~ t2 => Equation(t1,t2)}
      def negeq: Parser[FOLFormula] = term ~ "!=" ~ term ^^ {case t1 ~ "!=" ~ t2 => Neg(Equation(t1,t2))}
      def conssymb: Parser[String] = """[a-z][a-zA-Z0-9]*""".r
      def varsymb: Parser[String] = """[A-Z][a-zA-Z0-9]*""".r
      def term: Parser[FOLTerm] = function | constant | variable
      def function: Parser[FOLTerm] = conssymb ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Function(new ConstantStringSymbol(x), params.asInstanceOf[List[FOLTerm]])}
      def constant: Parser[FOLTerm] = conssymb ^^ {case x => FOLFactory.createVar(new ConstantStringSymbol(x), Ti()).asInstanceOf[FOLConst]}
      def variable: Parser[FOLTerm] = varsymb ^^ {case x => FOLFactory.createVar(new VariableStringSymbol(x), Ti()).asInstanceOf[FOLVar]}
    }
  }

  // in prover9, negated equations are considered to be one application and in gapt it is considered a negation of an equation, so two applications
  case object Prover92GAPTPositionsCommand extends DataCommand[Clause] {
    def apply(state: State, data: Any) = {
      val ls = data.asInstanceOf[Iterable[Tuple3[ResolutionProof[Clause],FormulaOccurrence,Iterable[Int]]]]
      List((state,ls.map(x => {
        (x._1,x._2,translate(x._2.formula,x._3.toList))
      })))
    }
    private def translate(f: HOLExpression, pos: List[Int]): List[Int] = {
      if (pos.isEmpty) pos
      else f match {
        case Neg(Equation(x,y)) if (pos.head == 1) => 1::1::translate (x, pos.tail)
        case Neg(Equation(x,y)) if (pos.head == 2) => 1::2::translate (y, pos.tail)
        case _ => pos.head::translate (getAtPosition(f, pos.head::Nil), pos.tail)
      }
    }
  }
}
