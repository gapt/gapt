package at.logic.parsing.language.xml

import _root_.at.logic.language.lambda.BetaReduction
import _root_.at.logic.language.lambda.symbols.VariableSymbolA
import _root_.at.logic.language.lambda.typedLambdaCalculus.{Var, LambdaExpression}
import scala.xml._
import dtd._
import at.logic.parsing.ExportingException
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.language.hol._
import at.logic.language.fol.{Atom => FOLAtom}
import at.logic.language.lambda.types.Ti
import logicSymbols.ConstantSymbolA

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 10/18/11
 * Time: 2:23 PM
 */

object XMLExporter {

  def apply(path: String, proofName: String, proof: LKProof) : Unit =
    apply(path, new ProofDatabase((proofName, proof)::Nil, Nil, Nil))

  def apply(path: String, pdb: ProofDatabase) : Unit = { //try {
    val output = <proofdatabase>
      <definitionlist/>
      { exportAxioms( pdb.axioms ) }
      { pdb.proofs.map(x => exportProof(x._1, x._2)) }
      { pdb.sequentLists.map(x => exportSequentList(x._1, x._2)) }
      <variabledefinitions/>
    </proofdatabase>
    val docType = DocType("proofdatabase", SystemID("http://www.logic.at/ceres/xml/4.0/proofdatabase.dtd"), Nil)
    val filename = if (path.endsWith(".xml")) path else path+".xml"
    XML.save(filename, output, "UTF-8", true, docType)
 // } catch {
 //   case e: Exception =>
//      throw new ExportingException("Can't save file: "+ path + "\n\n" + "Error:" + e.toString )
  }

  def exportAxioms(axioms : List[types.FSequent]) = if (axioms.isEmpty) <axiomset/>
    else <axiomset> { axioms.map(x => exportFSequent( x )) } </axiomset>

  def exportProof(name: String, proof : LKProof) =
    <proof symbol={ name } calculus="LK">
      { exportRule(proof) }
    </proof>

  def exportSequentList(name: String, sequentList: List[types.FSequent]) =
    <sequentlist symbol={ name }>
      { sequentList.map(x => exportFSequent( x )) }
    </sequentlist>

  def exportRule(proof: LKProof): Node = proof match {
    case p: UnaryLKProof =>
      val ruleType = getRuleType( p )
      <rule symbol={ p.name } type={ ruleType }>
      { exportSequent( p.root ) }
      { exportRule( p.uProof ) }
      { if (ruleType == "foralll2") exportLambdaSubstitution( ForallLeftRule.unapply(proof).get._5 ) }
      { if (ruleType == "existsr2") exportLambdaSubstitution( ExistsRightRule.unapply(proof).get._5 ) }
      </rule>
    case p: BinaryLKProof =>
      <rule symbol={ p.name } type={ getRuleType( p ) }>
      { exportSequent( p.root ) }
      { exportRule( p.uProof1 ) }
      { exportRule( p.uProof2 ) }
      </rule>
    case p: NullaryLKProof =>
      <rule symbol="axiom" type="axiom">
      { exportSequent( p.root ) }
      </rule>
  }

  def exportSequent(s: Sequent) = exportFSequent(s.toFSequent)

  def exportFSequent(fs: types.FSequent) =
    <sequent> { println(fs.toString) }
      <formulalist> { fs._1.map(x => exportFormula( x )) } </formulalist>
      <formulalist> { fs._2.map(x => exportFormula( x )) } </formulalist>
    </sequent>

  def exportFormula(formula: HOLFormula) : Node = formula match {
    case Equation(term1, term2) => println("Equation: "+term1.toString+", "+term2.toString)
      <constantatomformula type="or">
        { exportTerm(term1) }
        { exportTerm(term2) }
      </constantatomformula>
    case Neg(f) =>      println("Neg: "+f.toString)
      <conjunctiveformula type="neg">
        { exportFormula(f) }
      </conjunctiveformula>
    case And(f1, f2) =>     println("And: "+f1.toString+", "+f2.toString)
      <conjunctiveformula type="and">
        { exportFormula(f1) }
        { exportFormula(f2) }
      </conjunctiveformula>
    case Or(f1, f2) =>   println("Or: "+f1.toString+", "+f2.toString)
      <conjunctiveformula type="or">
        { exportFormula(f1) }
        { exportFormula(f2) }
      </conjunctiveformula>
    case Imp(f1, f2) =>  println("Impl: "+f1.toString+", "+f2.toString)
      <conjunctiveformula type="impl">
        { exportFormula(f1) }
        { exportFormula(f2) }
      </conjunctiveformula>
    case ExVar(x, f) => x.exptype match {
      case Ti() =>
        <quantifiedformula type="exists">
          <variable symbol={ x.name.toString } />
          { exportFormula(f) }
        </quantifiedformula>
      case _ =>
        <secondorderquantifiedformula type="exists2">
          <secondordervariable symbol={ x.name.toString } />
          { exportFormula(f) }
        </secondorderquantifiedformula>
    }
    case AllVar(x, f) => x.exptype match {
      case Ti() =>
        <quantifiedformula type="all">
          <variable symbol={ x.name.toString } />
          { exportFormula(f) }
        </quantifiedformula>
      case _ =>
        <secondorderquantifiedformula type="all2">
          <secondordervariable symbol={ x.name.toString } />
          { exportFormula(f) }
        </secondorderquantifiedformula>
    }
    case Atom(name : ConstantSymbolA, args) => println("FOLAtom: "+name.toString)
      if (args.isEmpty) <constantatomformula symbol={ name.toString }/>
      else <constantatomformula symbol={ name.toString }>
        { args.map(x => exportTerm( x )) }
      </constantatomformula>
    case Atom(name : VariableSymbolA, args) => println("Atom: "+name.toString)
      <variableatomformula>
        <secondordervariable symbol={ name.toString } />
        { args.map(x => exportTerm( x )) }
      </variableatomformula>
    case _ => throw new ExportingException("Can't match formula: " + formula.toString)
  }

  def exportTerm(term: HOLExpression) : Node = term match {
    case HOLVar(name, t) => t match {
      case Ti() => <variable symbol={ name.toString } />
      case _ => <secondordervariable symbol={ name.toString } />
    }
    case HOLConst(name, _) => <constant symbol={ name.toString } />
    case Function(name, args, _) =>
      <function symbol={ name.toString }>
        { args.map(x => exportTerm( x )) }
      </function>
    case _ => throw new ExportingException("Can't match term: " + term.toString)
  }

  def exportLambdaSubstitution(subst: HOLExpression) =
    <lambdasubstitution>
      { exportVariableList( subst.getFreeAndBoundVariables._2 ) }
      { exportFormula( subst.subTerms(1).asInstanceOf[HOLFormula] ) /*TODO: this line is hack, should be improved */ }
    </lambdasubstitution>

  def exportVariableList( vl : Set[Var]) =
    <variablelist>
      { vl.map(x => <variable symbol={ x.name.toString } />) }
    </variablelist>

  def getRuleType(proof: LKProof) = proof.rule match {
    case WeakeningLeftRuleType => "weakl"
    case WeakeningRightRuleType => "weakr"
    case ContractionLeftRuleType => "contrl"
    case ContractionRightRuleType => "contrr"
    case CutRuleType => "cut"

    case AndRightRuleType => "andr"
    case AndLeft1RuleType => "andl1"
    case AndLeft2RuleType => "andl2"
    case OrRight1RuleType => "orr1"
    case OrRight2RuleType => "orr2"
    case OrLeftRuleType => "orl"
    case ImpRightRuleType => "implr"
    case ImpLeftRuleType => "impll"
    case NegLeftRuleType => "negl"
    case NegRightRuleType => "negr"

    case ForallLeftRuleType => ForallLeftRule.unapply(proof).get._4.formula match {
      case AllVar(x, f) => x.exptype match {
        case Ti() => "foralll"
        case _ => "foralll2"
      }
    }
    case ForallRightRuleType => ForallRightRule.unapply(proof).get._4.formula match {
      case AllVar(x, f) => x.exptype match {
        case Ti() => "forallr"
        case _ => "forallr2"
      }
    }
    case ExistsLeftRuleType => ExistsLeftRule.unapply(proof).get._4.formula match {
      case ExVar(x, f) => x.exptype match {
        case Ti() => "existsl"
        case _ => "existsl2"
      }
    }
    case ExistsRightRuleType =>ExistsRightRule.unapply(proof).get._4.formula match {
      case ExVar(x, f) => x.exptype match {
        case Ti() => "existsr"
        case _ => "existsr2"
      }
    }

    case DefinitionLeftRuleType => "defl"
    case DefinitionRightRuleType => "defr"

    case EquationLeft1RuleType => "eql1"
    case EquationLeft2RuleType => "eql2"
    case EquationRight1RuleType => "eqr1"
    case EquationRight2RuleType => "eqr2"
  }
}