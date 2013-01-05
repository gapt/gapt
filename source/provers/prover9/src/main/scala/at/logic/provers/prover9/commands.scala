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
import _root_.at.logic.calculi.resolution.base.{ResolutionProof, Clause}
import _root_.at.logic.language.fol
import _root_.at.logic.language.fol._
import _root_.at.logic.language.hol.logicSymbols.ConstantStringSymbol
import _root_.at.logic.language.hol.replacements.getAtPosition
import _root_.at.logic.language.hol.{HOLVar, HOLExpression, HOLFormula}
import _root_.at.logic.language.lambda.substitutions.Substitution
import _root_.at.logic.language.lambda.symbols.VariableStringSymbol
import _root_.at.logic.language.lambda.types.Ti
import _root_.at.logic.parsing.language.tptp.TPTPFOLExporter
import _root_.at.logic.provers.atp.commands.guided.GetGuidedClausesCommand._
import _root_.at.logic.provers.atp.commands.guided.{AddGuidedClausesCommand, GetGuidedClausesCommand, AddGuidedResolventCommand, AddGuidedInitialClauseCommand}
import _root_.at.logic.provers.atp.commands.replay.ReplayCommand
import _root_.at.logic.provers.atp.commands.robinson.{ResolveCommand, VariantLiteralPositionCommand, VariantLiteralCommand, ParamodulationLiteralPositionCommand}
import _root_.at.logic.provers.atp.Definitions._
import at.logic.calculi.lk.base.FSequent
import at.logic.provers.atp.commands.base._
import at.logic.provers.atp.commands.sequents.{RefutationReachedCommand, fvarInvariantMSEquality, InsertResolventCommand, SetSequentsCommand}
import sys.process._
import java.io._
import scala.xml._
import scala.collection.immutable.Seq
import org.xml.sax.InputSource
import javax.xml.parsers.SAXParserFactory
import util.parsing.combinator.JavaTokenParsers
import util.matching.Regex
import collection.mutable.{ListBuffer, Map}
import at.logic.language.lambda.typedLambdaCalculus.{Var, LambdaExpression, App, Abs}
import collection.immutable

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
        //println(xml)
        // prover9 justifications. We translate the regular ones (factor, res and assumption) and replay the rest
        val AssumptionRE = new Regex("""\[(assumption)\]\.""")
        val FactorRE = new Regex("""\[factor\((\d+\w*),(\w+),(\w+)\)\]\.""")
        val ResolveRE = new Regex("""\[resolve\((\d+\w*),(\w+),(\d+\w*),(\w+)\)\]\.""")
        val ParaRE = new Regex("""\[para\((\d+\w*)\((\w+),(\d+)\),(\d+\w*)\((\w+),(\d+( d+)*)\)\)\]\.""")
        val CopyRE = new Regex("""\[copy\((\d+\w*)\).*\]\.""")
        cmnds = cmnds ++ assumption("0", List(Prover9TermParser.parseAll(Prover9TermParser.literal, "X=X").get)) // to support the xx rules


        val X = FOLFactory.createVar(new VariableStringSymbol("X"), Ti()).asInstanceOf[FOLVar]
        val Y = FOLFactory.createVar(new VariableStringSymbol("Y"), Ti()).asInstanceOf[FOLVar]
        val eq1 = Neg(Equation(X, Y))
        val eq2 = Equation(Y, X)
        cmnds = cmnds ++ assumption("999999", eq1::eq2::Nil) // symmetry
        //          val lit1 = MyParser.parseAll(MyParser.literal, "-X=Y").get
        //          val lit2 = MyParser.parseAll(MyParser.literal, "Y=X").get
        //          cmnds = cmnds ++ assumption("00", lit1::lit2::Nil) // symmetry

        var lastParents = new ListBuffer[String]() // this is used to monitor if the last rule by prover9 triggers a replay or not. If not, we must call replay with the parents here.
        (xml \\ "clause").foreach(e => {
          val cls = getLiterals(e)
          val id = (e\"@id").text
          lastParents = new ListBuffer[String]()
          cmnds = cmnds ++
            ((e\\"@jstring").text match {
              case AssumptionRE(_) => returnAndPrint(assumption(id, cls)) // here no need to set the lastParents as there are none
              case FactorRE(parent, lit1, lit2) => {lastParents += parent; returnAndPrint(factor(parent, lit1, lit2, id, cls))}
              //case ResolveRE(par1, lit1, par2, lit2) => returnAndPrint(resolve(par1, lit1, par2, lit2, id, cls))
              //case ParaRE(fPar, fLit, fPos, tPar, tLit, tPos, _) => returnAndPrint(paramodulate(fPar, fLit, fPos.toInt, tPar, tLit, tPos.split("""\s""").map(_.toInt), id, cls))
              //case CopyRE(pid) => {lastParents += pid; copy(pid, id)} //careful! copying may have an added paramodulation! -> commented out
              case _ => returnAndPrint(replay(getParents(e), id, cls))
            })
        })
        if (!lastParents.isEmpty) cmnds = cmnds ++ replay(lastParents, "-1", List()) // try to obtain the empty clause if last rule in prover9 refutation does not initiate a replay
      },
      stderr => {val err:String = scala.io.Source.fromInputStream(stderr).mkString; if (!err.isEmpty) throw new Prover9Exception(err)}
    )

    //      val p  = "tptp_to_ladr" #| "prover9" #| "prooftrans xml expand"
    val p  = "tptp_to_ladr" #| "prover9" #| "prooftrans xml"
    val proc = p.run(pio)
    val exitValue = proc.exitValue

    tptpIS.close()

    List((state, cmnds ++ List(RefutationReachedCommand[Clause]) ))
  }

  private def returnAndPrint[T](x:T) = {println("Scheduling P9 Command:"+x); x }

  // the second value is the literals permutation from prover9 order to fsequent (as we have positive and negative
  def getLiterals(e: Node): Seq[FOLFormula] = {
    if ((e \\ "literal").text.trim == "$F") List()
    else (e \\ "literal").map(l => Prover9TermParser.parseAll(Prover9TermParser.literal, l.text).get)
  }

  private def literals2FSequent(lits: Seq[FOLFormula]): FSequent = {
    FSequent(lits.filter(l => l match {
      case Neg(_) => true
      case _ => false})
      .map(l => l match {
      case Neg(f) => f
    }),
      lits.filter(l => l match {
        case Neg(_) => false
        case _ => true}))
  }
  val INTq_CHAR = 97

  private def getParents(e: Node): Iterable[String] = { println((e \\ "@parents").foldLeft("")((s:String, n:Node) => if (s.isEmpty) n.text else s + " " + n.text)  ); (e \\ "@parents").foldLeft("")((s:String, n:Node) =>if (s.isEmpty) n.text else s + " " + n.text).split(" ") }

  private def assumption(id: String, cls: Seq[FOLFormula]): TraversableOnce[Command[Clause]] = {
    println("assumption")
    List(AddGuidedInitialClauseCommand(id, cls), InsertResolventCommand[Clause])
  }
  // here we just attach the parent to the new clause id as all other rules try to factorize the parents anyway
  //factor is copy, because we do factor when we have a replay. So, we ignore factor
  private def factor(parentId: String, lit1: String, lit2: String, id: String, cls: Seq[FOLFormula]): TraversableOnce[Command[Clause]] = {
    println("factor")
    List(GetGuidedClausesCommand(List(parentId)),AddGuidedClausesCommand(List(id)))
  }
  private def copy(parentId: String, id: String): TraversableOnce[Command[Clause]] = {
    println("copy")
    List(GetGuidedClausesCommand(List(parentId)),AddGuidedClausesCommand(List(id)))
  }

  // we apply replay here because the order of literals might change in our proof
  private def resolve(par1Id: String, lit1: String, par2Id: String, lit2: String, id: String, cls: Seq[FOLFormula]): TraversableOnce[Command[Clause]] = {
    /*require(lit1.size == 1 && lit2.size == 1) // the parsing should be changed if the arity of functions is bigger than the english alphabet
    List(GetGuidedClausesLiterals(List((par1Id, lit1.head.toInt - INT_CHAR), (par2Id, lit2.head.toInt - INT_CHAR))), VariantLiteralCommand, ResolveCommand(FOLUnificationAlgorithm), AddGuidedResolventCommand(id))
    */
    //List(ReplayCommand(List(par1Id,par2Id,"0"), id, literals2FSequent(cls)), SpawnCommand())
    println("resolve")
    List(ReplayCommand(List(par1Id,par2Id,"0"), id, literals2FSequent(cls)), InsertResolventCommand[Clause] )
  }
  // we apply replay here because the order of literals might change in our proof
  private def paramodulate(fromParentId: String, fromLiteral: Seq[Char], fromPos: Int, toParentId: String, toLiteral: Seq[Char], toPos: Iterable[Int], id: String, cls: Seq[FOLFormula]): TraversableOnce[Command[Clause]] = {
    /*require(fromLiteral.size == 1 && toLiteral.size == 1) // the parsing should be changed if the arity of functions is bigger than the english alphabet
    List(GetGuidedClausesLiteralsPositions(List((fromParentId, fromLiteral.head.toInt - INT_CHAR, List(fromPos)), (toParentId, toLiteral.head.toInt - INT_CHAR, toPos))), VariantLiteralPositionCommand, ParamodulationLiteralPositionCommand(FOLUnificationAlgorithm), AddGuidedResolventCommand(id))*/
    //      List(ReplayCommand(List(fromParentId,toParentId, "0"), id, literals2FSequent(cls)), SpawnCommand())
    println("paramodulate")
    List(ReplayCommand(List(fromParentId,toParentId, "0"), id, literals2FSequent(cls)), InsertResolventCommand[Clause])
  }
  private def replay(parentIds: Iterable[String], id: String, cls: Seq[FOLFormula]): TraversableOnce[Command[Clause]] = {
    println("replay")
    //      List(ReplayCommand("0" :: parentIds.toList, id, literals2FSequent(cls)), SpawnCommand())
    List(ReplayCommand("0" :: parentIds.toList, id, literals2FSequent(cls)), InsertResolventCommand[Clause])
  }

}

//Prolog Style Term Parser
object Prover9TermParser extends Prover9TermParserA {
  override def conssymb: Parser[String] = """[a-z][a-zA-Z0-9_]*""".r
  override def varsymb: Parser[String] =  """[A-Z][a-zA-Z0-9_]*""".r

}

//LADR Style Term Parser
object Prover9TermParserLadrStyle extends Prover9TermParserA {
  override def conssymb: Parser[String] = """[a-tA-Z][a-zA-Z0-9_]*""".r
  override def varsymb: Parser[String] =  """[u-z][a-zA-Z0-9_]*""".r

}


abstract class Prover9TermParserA extends JavaTokenParsers {
  /* these two rules are abstract since the variable style decides the regexp for a variable */
  def conssymb : Parser[String]
  def varsymb : Parser[String]

  /* change this variable to to use prolog style variables (starting with upper case letters) or ladr style variables
  *  (starting with u-z)*/

  /* debug transformers
  def d(s:String,f:FOLFormula) : FOLFormula = { println(s+": "+f); f }    */

  /* The main entry point to the parser for prover9 formulas. To parse literals, use literal as the entry point. */
  def parseFormula(s:String) : FOLFormula = parseAll(formula, s) match {
    case Success(result, _) => result
    case NoSuccess(msg, input) =>
      throw new Exception("Error parsing prover9 formula '"+s+"' at position "+input.pos+". Error message: "+msg)
  }

  def pformula : Parser[FOLFormula] = parens(formula) | formula
  def formula: Parser[FOLFormula] = implication
  //precedence 800
  def implication: Parser[FOLFormula]  = (dis_or_con ~ ("<->"|"->"|"<-") ~ dis_or_con) ^^ { _ match {
    case f ~ "->"  ~ g => fol.Imp(f,g)
    case f ~ "<-"  ~ g => fol.Imp(g,f)
    case f ~ "<->" ~ g => fol.And(fol.Imp(f,g), fol.Imp(g,f))
  }} | dis_or_con

  def dis_or_con: Parser[FOLFormula] = (disjunction | conlit )
  //precedence 790
  def disjunction: Parser[FOLFormula]  = (conlit ~ ("|" ~> disjunction) ^^ {case f ~ g => fol.Or(f,g)}) | conlit
  //precedence 780
  def conlit: Parser[FOLFormula] =  (conjunction| qliteral )
  def conjunction: Parser[FOLFormula]  = ( qliteral ~ ("&" ~> conjunction)   ^^ { case f ~ g => fol.And(f,g) }) | qliteral
  //precedence 750
  def qliteral : Parser[FOLFormula] = allformula | exformula | literal2
  def allformula : Parser[FOLFormula] = parens(allformula_)
  def exformula : Parser[FOLFormula] = parens(exformula_)
  def allformula_ : Parser[FOLFormula]   = ("all"    ~> variable ~ ( allformula_ | exformula_ | literal2) ) ^^ { case v ~ f => fol.AllVar(v,f) }
  def exformula_ : Parser[FOLFormula]    = ("exists" ~> variable ~ ( allformula_ | exformula_ | literal2) ) ^^ { case v ~ f => fol.ExVar(v,f) }
  //precedence 300
  def literal2:Parser[FOLFormula] = parens(formula) | atomWeq | negation
  def negation:Parser[FOLFormula] = "-" ~> (parens(formula) | atomWeq)


  def parens[T](p:Parser[T]) : Parser[T] = "(" ~> p <~ ")"

  def literal: Parser[FOLFormula] = negeq | poseq | negatom | posatom
  def posatom: Parser[FOLFormula] = atom
  def negatom: Parser[FOLFormula] = "-" ~ atom  ^^ {case "-" ~ a => Neg(a)}
  def atomWeq: Parser[FOLFormula] =  negeq | poseq | atom
  def atom: Parser[FOLFormula] = atom1 | atom2
  def atom1: Parser[FOLFormula] = atomsymb ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Atom(new ConstantStringSymbol(x), params.asInstanceOf[List[FOLTerm]])}
  def atom2: Parser[FOLFormula] = atomsymb ^^ {case x => Atom(new ConstantStringSymbol(x), Nil)}
  def poseq: Parser[FOLFormula] = term ~ "=" ~ term ^^ {case t1 ~ "=" ~ t2 => Equation(t1,t2)}
  def negeq: Parser[FOLFormula] = term ~ "!=" ~ term ^^ {case t1 ~ "!=" ~ t2 => Neg(Equation(t1,t2))}
  def atomsymb: Parser[String] = """[a-zA-Z][a-zA-Z0-9_]*""".r
  def term: Parser[FOLTerm] = function | constant | variable
  def function: Parser[FOLTerm] = conssymb ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Function(new ConstantStringSymbol(x), params.asInstanceOf[List[FOLTerm]])}
  def constant: Parser[FOLConst] = conssymb ^^ {case x => FOLFactory.createVar(new ConstantStringSymbol(x), Ti()).asInstanceOf[FOLConst]}
  def variable: Parser[FOLVar] = varsymb ^^ {case x => FOLFactory.createVar(new VariableStringSymbol(x), Ti()).asInstanceOf[FOLVar]}

  def createNOp(fs:List[FOLFormula], constructor : (FOLFormula, FOLFormula) => FOLFormula ) : FOLFormula = {
    //if (fs.size < 2) failure("Binary operator needs to occur at least once!") else
    fs.reduceRight( (f:FOLFormula, g:FOLFormula) => constructor(f,g)   )
  }

  def normalizeFSequent(f:FSequent) =
    FSequent(f.antecedent.map(normalizeFormula[HOLFormula](_)),
      f.succedent.map(normalizeFormula[HOLFormula](_)))

  def normalizeFormula[T <: LambdaExpression](f:T) : T = normalizeFormula(f,0)._1
  def normalizeFormula[T <: LambdaExpression](f:T, i:Int) : (T, Int) = f match {
    case Var(name, exptype) => (f, i)
    case App(s, t) =>
      val (s_, i_) = normalizeFormula(s,i)
      val (t_, j) = normalizeFormula(t,i)
      (s.factory.createApp(s_, t_).asInstanceOf[T], j)
    case Abs(x, s) =>
      val x_ = x.factory.createVar(new VariableStringSymbol("v"+i), x.exptype)
      val sub = Substitution[LambdaExpression]((x, x_))
      val (s_, j) = normalizeFormula(sub(s).asInstanceOf[T], i+1)
      (s.factory.createAbs(x_, s_).asInstanceOf[T], j)
    case _ => throw new Exception("Unhandled expression type in variable normalization!")
  }

}


// in prover9, negated equations are considered to be one application and in gapt it is considered a negation of an equation, so two applications
case object Prover92GAPTPositionsCommand extends DataCommand[Clause] {
  def apply(state: State, data: Any) = {
    println("Prover92GAPTPositionsCommand")
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



//TODO: refactor shared code with Prover9Init
object InferenceExtractor {
  def apply(fn: String) : FSequent = {
    //println("==== Extracting Inferences ======")
    val buffer = new Array[ Byte ]( 1024 )
    val tptpIS = new FileInputStream(fn)
    var goals = List[FOLFormula]()
    var assumptions = List[FOLFormula]()
    //this was autodetection code for naming conventions, but apparently ivy has its own anyway
    val variablestyle_matcher = """prolog_style_variables""".r
    val str_p9 = scala.io.Source.fromInputStream( new FileInputStream( fn ) ).mkString

    val set_prolog_style_variables =
      !(for (line <- str_p9.split(System.getProperty("line.separator"));
           if ( variablestyle_matcher.findFirstIn(line).isDefined)) yield line).isEmpty

    println(if (set_prolog_style_variables) "prolog style variables!" else "normal style variables!")

    val parser = if (set_prolog_style_variables) Prover9TermParser else Prover9TermParserLadrStyle

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

        var lastParents = new ListBuffer[String]() // this is used to monitor if the last rule by prover9 triggers a replay or not. If not, we must call replay with the parents here.

        (xml \\ "clause").foreach(e => {
          //val cls = getLiterals(e)
          val inference_type = (e \\ "justification" \\ "@jstring")
          inference_type.text match {
            case "[assumption]." =>
              //println("assumption:"+literal);
              val formula : FOLFormula = fol.Or((e \\ "literal").map( x => parser.parseFormula(x.text)))
              assumptions = formula :: assumptions
            case "[goal]." =>
              //println("goal:"+literal);
              (e \\ "literal").foreach(literal =>
               goals = parser.parseFormula(literal.text)::goals
              )
            case _ => ; //println("skipping: "+inference_type.text); //ignore other rules
          }
          val id = (e\"@id").text
          println(inference_type)
          println()
          lastParents = new ListBuffer[String]()
        })



      },
      stderr => {val err:String = scala.io.Source.fromInputStream(stderr).mkString; if (!err.isEmpty) throw new Prover9Exception(err)}
    )

    //      val p  = "tptp_to_ladr" #| "prover9" #| "prooftrans xml expand"
    val p  = "prooftrans xml"
    val proc = p.run(pio)
    val exitValue = proc.exitValue

    tptpIS.close()
    /*
    println("assumptions:")
    assumptions map println
    println("goals:")
    goals map println
    println
    println("fsequent:")
    */
    val fs = createFSequent(assumptions, goals)
    /*      println(fs)
    println()
    println("==== End of Inferences ======") */
    fs
  }

  // the second value is the literals permutation from prover9 order to fsequent (as we have positive and negative
  def getLiterals(e: Node): Seq[FOLFormula] = {
    if ((e \\ "literal").text.trim == "$F") List()
    else (e \\ "literal").map(l => Prover9TermParser.parseAll(Prover9TermParser.literal, l.text).get)
  }

  /* fixed point of createFSequent_ */
  def createFSequent(assumptions : immutable.Seq[FOLFormula], goals : immutable.Seq[FOLFormula]) : FSequent = {
    val fs = createFSequent_(assumptions, goals)
    if ((assumptions.length >= fs.antecedent.length ) && (goals.length >= fs.succedent.length))
      fs
    else
      createFSequent(fs.antecedent.asInstanceOf[immutable.Seq[FOLFormula]], fs.succedent.asInstanceOf[immutable.Seq[FOLFormula]])
  }

  /* given a list of assumptions and goals, if a goal is of the form A -> B, put A into the
  *  antecedent and B into the succedent. if a goal is a disjunction B1,...,Bn, put B1 to Bn into the succedent
  *  instead. is an assumption is a conjunction A1,...,Am, put them into the antecedent instead.*/
  def createFSequent_(assumptions : immutable.Seq[FOLFormula], goals : immutable.Seq[FOLFormula]) = {
    val fs = goals.map(implications).foldLeft(FSequent(assumptions, Nil))((f:FSequent,g:FSequent) => f.compose(g))
    FSequent(fs.antecedent.asInstanceOf[immutable.Seq[FOLFormula]].map(conjunctions).flatten,
      fs.succedent.asInstanceOf[immutable.Seq[FOLFormula]].map(disjunctions).flatten)
  }

  def implications(f:FOLFormula) : FSequent = f match {
    case fol.Imp(f1,f2) => FSequent(conjunctions(f1),disjunctions(f2))
    case _ => FSequent(Nil, f::Nil)
  }

  def disjunctions(f:FOLFormula) : immutable.List[FOLFormula] = f match {
    case fol.Or(f1,f2) => disjunctions(f1) ++ disjunctions(f2)
    case _ => immutable.List[FOLFormula](f)
  }

  def conjunctions(f:FOLFormula) : List[FOLFormula] = f match {
    case fol.And(f1,f2) => disjunctions(f1) ++ disjunctions(f2)
    case _ => immutable.List[FOLFormula](f)
  }

}
}
