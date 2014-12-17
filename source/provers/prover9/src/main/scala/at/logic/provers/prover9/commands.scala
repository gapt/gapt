
package at.logic.provers.prover9.commands

import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.resolution.{ResolutionProof, Clause}
import at.logic.language.fol._
import at.logic.language.hol.replacements.getAtPosition
import at.logic.parsing.language.prover9.{Prover9TermParserA, Prover9TermParser, Prover9TermParserLadrStyle}
import at.logic.parsing.language.tptp.TPTPFOLExporter
import at.logic.provers.atp.Definitions._
import at.logic.provers.atp.commands.base._
import at.logic.provers.atp.commands.guided.GetGuidedClausesCommand._
import at.logic.provers.atp.commands.guided.{AddGuidedClausesCommand, GetGuidedClausesCommand, AddGuidedResolventCommand, AddGuidedInitialClauseCommand}
import at.logic.provers.atp.commands.replay.ReplayCommand
import at.logic.provers.atp.commands.robinson.{ResolveCommand, VariantLiteralPositionCommand, VariantLiteralCommand, ParamodulationLiteralPositionCommand}
import at.logic.provers.atp.commands.sequents.{RefutationReachedCommand, fvarInvariantMSEquality, InsertResolventCommand, SetSequentsCommand}
import at.logic.provers.prover9.Prover9Exception
import at.logic.utils.logging.Logger

import collection.mutable.{ListBuffer, Map}
import java.io._
import javax.xml.parsers.SAXParserFactory
import org.xml.sax.InputSource
import scala.xml._
import sys.process._
import util.matching.Regex
import util.parsing.combinator.JavaTokenParsers
import at.logic.utils.dssupport.ListSupport

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

case class Prover9InitCommand(override val clauses: Iterable[FSequent]) extends SetSequentsCommand[Clause](clauses) with Logger {
  override def loggerName = "Prover9Logger"

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


        val X = FOLVar("X")
        val Y = FOLVar("Y")
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

    val l = List((state, cmnds ++ List(RefutationReachedCommand[Clause]) ))
    info("Parsed proof to:")
    for (cmd <- l(0)._2) {
      info("  cmd: "+cmd)
    }
    l
  }

  private def returnAndPrint[T](x:T) = {/*println("Scheduling P9 Command:"+x);*/ x }

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

  private def getParents(e: Node): Iterable[String] = { /*println((e \\ "@parents").foldLeft("")((s:String, n:Node) => if (s.isEmpty) n.text else s + " " + n.text)  );*/ (e \\ "@parents").foldLeft("")((s:String, n:Node) =>if (s.isEmpty) n.text else s + " " + n.text).split(" ") }

  private def assumption(id: String, cls: Seq[FOLFormula]): TraversableOnce[Command[Clause]] = {
    //println("assumption")
    List(AddGuidedInitialClauseCommand(id, cls), InsertResolventCommand[Clause])
  }
  // here we just attach the parent to the new clause id as all other rules try to factorize the parents anyway
  //factor is copy, because we do factor when we have a replay. So, we ignore factor
  private def factor(parentId: String, lit1: String, lit2: String, id: String, cls: Seq[FOLFormula]): TraversableOnce[Command[Clause]] = {
    //println("factor")
    List(GetGuidedClausesCommand(List(parentId)),AddGuidedClausesCommand(List(id)))
  }
  private def copy(parentId: String, id: String): TraversableOnce[Command[Clause]] = {
    //println("copy")
    List(GetGuidedClausesCommand(List(parentId)),AddGuidedClausesCommand(List(id)))
  }

  // we apply replay here because the order of literals might change in our proof
  private def resolve(par1Id: String, lit1: String, par2Id: String, lit2: String, id: String, cls: Seq[FOLFormula]): TraversableOnce[Command[Clause]] = {
    /*require(lit1.size == 1 && lit2.size == 1) // the parsing should be changed if the arity of functions is bigger than the english alphabet
    List(GetGuidedClausesLiterals(List((par1Id, lit1.head.toInt - INT_CHAR), (par2Id, lit2.head.toInt - INT_CHAR))), VariantLiteralCommand, ResolveCommand(FOLUnificationAlgorithm), AddGuidedResolventCommand(id))
    */
    //List(ReplayCommand(List(par1Id,par2Id,"0"), id, literals2FSequent(cls)), SpawnCommand())
    //println("resolve")
    List(ReplayCommand(List(par1Id,par2Id,"0"), id, literals2FSequent(cls)), InsertResolventCommand[Clause] )
  }
  // we apply replay here because the order of literals might change in our proof
  private def paramodulate(fromParentId: String, fromLiteral: Seq[Char], fromPos: Int, toParentId: String, toLiteral: Seq[Char], toPos: Iterable[Int], id: String, cls: Seq[FOLFormula]): TraversableOnce[Command[Clause]] = {
    /*require(fromLiteral.size == 1 && toLiteral.size == 1) // the parsing should be changed if the arity of functions is bigger than the english alphabet
    List(GetGuidedClausesLiteralsPositions(List((fromParentId, fromLiteral.head.toInt - INT_CHAR, List(fromPos)), (toParentId, toLiteral.head.toInt - INT_CHAR, toPos))), VariantLiteralPositionCommand, ParamodulationLiteralPositionCommand(FOLUnificationAlgorithm), AddGuidedResolventCommand(id))*/
    //      List(ReplayCommand(List(fromParentId,toParentId, "0"), id, literals2FSequent(cls)), SpawnCommand())
    //println("paramodulate")
    List(ReplayCommand(List(fromParentId,toParentId, "0"), id, literals2FSequent(cls)), InsertResolventCommand[Clause])
  }
  private def replay(parentIds: Iterable[String], id: String, cls: Seq[FOLFormula]): TraversableOnce[Command[Clause]] = {
    //println("replay")
    //      List(ReplayCommand("0" :: parentIds.toList, id, literals2FSequent(cls)), SpawnCommand())
    List(ReplayCommand("0" :: parentIds.toList, id, literals2FSequent(cls)), InsertResolventCommand[Clause])
  }

}


// in prover9, negated equations are considered to be one application and in gapt it is considered a negation of an equation, so two applications
/* Used nowhere.
case object Prover92GAPTPositionsCommand extends DataCommand[Clause] {
  def apply(state: State, data: Any) = {
    //println("Prover92GAPTPositionsCommand")
    val ls = data.asInstanceOf[Iterable[Tuple3[ResolutionProof[Clause],FormulaOccurrence,Iterable[Int]]]]
    List((state,ls.map(x => {
      (x._1,x._2,translate(x._2.formula, x._3.toList))
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
*/



//TODO: refactor shared code with Prover9Init
object InferenceExtractor {
  private def debug(s:String) : Unit = { }

  def viaLADR(fn : String) : FSequent = {
    import scala.io.Source

    val variablestyle_matcher = """.*set.(prolog_style_variables).*""".r
    val rassumption = """(\d+) ([^#\.]+).*\[assumption\].""".r
    val rgoal = """(\d+) ([^#\.]+).*\[goal\].""".r
    val proof_start = """=+ (PROOF) =+""".r
    val proof_end = """=+ (end) of proof =+""".r
    // with_proof starts at 0, will be increased to 1 after matching proof_start and to 2 after proof_end
    // because there might be more than one proof in the file
    var within_proof = 0
    var parser : Prover9TermParserA = Prover9TermParserLadrStyle

    val str_ladr = Source.fromInputStream( new FileInputStream( fn ) ).mkString

    val (assumptions, goals) = str_ladr.split(System.getProperty("line.separator")).foldLeft((List[FOLFormula](), List[FOLFormula]()))((m, l) => {

       val (as,gs) = m;
       l match {
        case rassumption(id, formula ) => if (within_proof != 1) m else  (parser.parseFormula(formula)::as, gs)
        case rgoal(id, formula )       => if (within_proof != 1) m else  (as, parser.parseFormula(formula)::gs)
        case variablestyle_matcher(_) => parser = Prover9TermParser;  m
        case proof_start(_) => within_proof = 1; m
        case proof_end(_) => within_proof = 2; m
        case _ => m
      }
    })

    createFSequent(assumptions, goals)

  }


  def clausesViaLADR(fn : String) : FSequent = {
    import scala.io.Source

    val variablestyle_matcher = """.*set.(prolog_style_variables).*""".r
    val rassumption = """(\d+) ([^#\.]+).*\[assumption\].""".r
    val rgoal = """(\d+) ([^#\.]+).*\[goal\].""".r
    val deny = """(\d+) ([^#\.]+).*\[deny\((\d+)\)\].""".r
    val clausify = """(\d+) ([^#\.]+).*\[clausify\((\d+)\)\].""".r
    val proof_start = """=+ (PROOF) =+""".r
    val proof_end = """=+ (end) of proof =+""".r
    val searchclauses_start = """=+ (PROOF) =+""".r
    val searchclauses_end = """=+ (end) of proof =+""".r

    val rnonclause = """.*#\ label\(non_clause\)""".r
    // with_proof starts at 0, will be increased to 1 after matching proof_start and to 2 after proof_end
    // because there might be more than one proof in the file
    var within_proof = 0
    var parser : Prover9TermParserA = Prover9TermParserLadrStyle

    val str_ladr = Source.fromInputStream( new FileInputStream( fn ) ).mkString

    val (assumptions, goals, _clausifies, _denials) = str_ladr.split(System.getProperty("line.separator")).foldLeft(
      (List[FOLFormula](), List[FOLFormula](), List[String](), List[String]())) ((m, l) => {

       val (as,gs,cs, g) = m

       l match {
        case rassumption(id, formula ) if (within_proof == 1)  =>
          val f = parser.parseFormula(formula)
          rnonclause.findFirstIn(l) match {
            case None => //we add only clauses, formulas have to be clausified first
              //println("Assumption "+id+" is a clause!")
              (f::as, gs, cs, g)
            case Some(_) => //contains label non_clause i.e. formula
              //println("Assumption "+id+" is a non-clause, adding to nonclausal assumptions list!")
              (as, gs, id::cs, g)
          }

        case rgoal(id, formula )       if (within_proof == 1) =>
          val f = parser.parseFormula(formula)
          rnonclause.findFirstIn(l) match {
            case None => //we add only clauses, formulas have to be clausified first
//              println("Goal "+id+" is a clause!")
              (as, f::gs, cs, g)
            case Some(_) => //contains label non_clause i.e. formula
//              println("Goal "+id+" is a non-clause, adding to nonclausal goals list!")
              (as, gs, cs, id::g)
          }
        case deny(id, formula, goalid) if (within_proof == 1) && cs.contains(goalid)=>
//          println("Deny "+id+" of assumption "+goalid)
          val f = parser.parseFormula(formula)
          (f::as, gs, cs, g)
        case deny(id, formula, goalid)  if (within_proof == 1) && g.contains(goalid)=>
          if (g.contains(id)) println("!!!")
//          println("Deny "+id+" of goal "+goalid)
          val f = parser.parseFormula(formula)
          (as, f::gs, cs, g)
        case clausify(id, formula, goalid) if (within_proof == 1) && cs.contains(goalid)=>
//          println("Clausify "+id+" of assumption "+goalid)
          val f = parser.parseFormula(formula)
          (f::as, gs, cs, g)
        case clausify(id, formula, goalid) if (within_proof == 1) && g.contains(goalid)=>
//          println("Clausify "+id+" of goal "+goalid)
          val f = parser.parseFormula(formula)
          (as, f::gs, cs, g)
        case variablestyle_matcher(_) =>
          parser = Prover9TermParser
          m
        case proof_start(_) =>
          within_proof = 1
//          println("proofs start")
          m
        case proof_end(_) =>
          within_proof = 2
//          println("proofs end")
          m
        case _ =>
//          println("NONMATCH:"+l)
          m
      }
    })

//    println("clause assumptions:"+assumptions)
//    println("clause goals:"+goals)
//    println("nonclause assumptions:"+ _clausifies)
//    println("nonclause goals:"+ _denials)


    if (goals.isEmpty)
      createFSequent(assumptions, goals)
    else {
      val (positive_goals, negated_goals) : (List[FOLFormula], List[FOLFormula]) = goals.foldLeft((List[FOLFormula](), List[FOLFormula]()))( (pair, f) => {
        val (pg, ng) = pair
        f  match {
          case Neg(x) =>
            (pg, x :: ng)
          case _ =>
            (f :: pg, ng)
            //throw new Exception("Error extracting clause set from proof: Goals come from a [deny( )] statement and are negated. But "+g+" does not have an outermost negation!"  )
        }})

      createFSequent(assumptions ++ positive_goals, negated_goals)
    }


  }


  /* fixed point of createFSequent_ */
  def createFSequent(assumptions : Seq[FOLFormula], goals : Seq[FOLFormula]) : FSequent = {
    val fs = createFSequent_(assumptions, goals)
    if ((assumptions.length >= fs.antecedent.length ) && (goals.length >= fs.succedent.length))
      fs
    else
      createFSequent(fs.antecedent.asInstanceOf[Seq[FOLFormula]], fs.succedent.asInstanceOf[Seq[FOLFormula]])
  }

  /* given a list of assumptions and goals, if a goal is of the form A -> B, put A into the
  *  antecedent and B into the succedent. if a goal is a disjunction B1,...,Bn, put B1 to Bn into the succedent
  *  instead. is an assumption is a conjunction A1,...,Am, put them into the antecedent instead.*/
  def createFSequent_(assumptions : Seq[FOLFormula], goals : Seq[FOLFormula]) = {
    val fs = goals.map(implications).foldLeft(FSequent(assumptions, Nil))((f:FSequent,g:FSequent) => f.compose(g))
    FSequent(fs.antecedent.asInstanceOf[Seq[FOLFormula]].map(conjunctions).flatten,
      fs.succedent.asInstanceOf[Seq[FOLFormula]].map(disjunctions).flatten)
  }

  def implications(f:FOLFormula) : FSequent = f match {
    case Imp(f1,f2) => FSequent(conjunctions(f1),disjunctions(f2))
    case _ => FSequent(Nil, f::Nil)
  }

  def disjunctions(f:FOLFormula) : List[FOLFormula] = f match {
    case Or(f1,f2) => disjunctions(f1) ++ disjunctions(f2)
    case _ => List[FOLFormula](f)
  }

  def conjunctions(f:FOLFormula) : List[FOLFormula] = f match {
    case And(f1,f2) => disjunctions(f1) ++ disjunctions(f2)
    case _ => List[FOLFormula](f)
  }

}
