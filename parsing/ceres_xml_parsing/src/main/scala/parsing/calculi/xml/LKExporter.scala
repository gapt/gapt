/*
 * LKExporter.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */


package at.logic.parsing.calculus.xml

import scala.xml.dtd._

import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.parsing.ExportingException
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.lkExtractors._
import at.logic.calculi.lk.quantificationRules._
import at.logic.parsing.language.xml.HOLTermExporter
import at.logic.calculi.lksk.{Axiom => LKskAxiom,
WeakeningLeftRule => LKskWeakeningLeftRule,
WeakeningRightRule => LKskWeakeningRightRule,
ForallSkLeftRule, ForallSkRightRule, ExistsSkLeftRule, ExistsSkRightRule}
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.definitionRules._

trait LKExporter extends HOLTermExporter {
  def exportSequent(seq: Sequent) =
    <sequent>
      <formulalist>
        {seq.antecedent.map(x => exportTerm(x.asInstanceOf[HOLFormula]))}
      </formulalist>
      <formulalist>
        {seq.succedent.map(x => exportTerm(x.asInstanceOf[HOLFormula]))}
      </formulalist>
    </sequent>

  def exportSequentList(name: String, ls: List[Sequent]) =
    <sequentlist symbol={name}>
      {ls.map(x => exportSequent(x))}
    </sequentlist>

  def exportProof(name: String, proof: LKProof) : scala.xml.Elem =
    <proof symbol={name}>
      {exportProof( proof )}
    </proof>

  // TODO: add permutation inferences! at the moment, the inferences are
  // not formally correct (when regarded as lists instead of multisets)
  //
  // TODO: distinguish first-/second-order quantifier inferences
  def exportProof( proof: LKProof ) : scala.xml.Elem = proof match {
    // LKsk
    case LKskAxiom( seq ) => <rule type="axiom"> {exportSequent(seq.getSequent)} </rule>
    case LKskWeakeningLeftRule(parent, seq, _) => <rule type="weakl"> {exportSequent(seq.getSequent)} {exportProof( parent )} </rule>
    case LKskWeakeningRightRule(parent, seq, _) => <rule type="weakr"> {exportSequent(seq.getSequent)} {exportProof( parent )} </rule>
    case ForallSkLeftRule(parent, seq, _, _, _) => <rule type="foralll"> {exportSequent(seq.getSequent)} {exportProof( parent )} </rule>
    case ForallSkRightRule(parent, seq, _, _, _) => <rule type="forallr"> {exportSequent(seq.getSequent)} {exportProof( parent )} </rule>
    case ExistsSkLeftRule(parent, seq, _, _, _) => <rule type="existsl"> {exportSequent(seq.getSequent)} {exportProof( parent )} </rule>
    case ExistsSkRightRule(parent, seq, _, _, _) => <rule type="existsr"> {exportSequent(seq.getSequent)} {exportProof( parent )} </rule>

    // LK
    case Axiom( seq ) => <rule type="axiom"> {exportSequent(seq.getSequent)} </rule>
    case WeakeningLeftRule(parent, seq, _) => exportUnaryRule( parent, seq.getSequent, "weakl" )
    case WeakeningRightRule(parent, seq, _) => exportUnaryRule( parent, seq.getSequent, "weakr" )
    case ContractionLeftRule(parent, seq, _, _, _) => exportUnaryRule( parent, seq.getSequent, "contrr" )
    case ContractionRightRule(parent, seq, _, _, _) => exportUnaryRule( parent, seq.getSequent, "contrl" )
    case AndLeft1Rule(parent, seq, _, _) => exportUnaryRule( parent, seq.getSequent, "andl1" )
    case AndLeft2Rule(parent, seq, _, _) => exportUnaryRule( parent, seq.getSequent, "andl2" )
    case OrRight1Rule(parent, seq, _, _) => exportUnaryRule( parent, seq.getSequent, "orr1" )
    case OrRight2Rule(parent, seq, _, _) => exportUnaryRule( parent, seq.getSequent, "orr2" )
    case ImpRightRule(parent, seq, _, _, _) => exportUnaryRule( parent, seq.getSequent, "implr" )
    case NegLeftRule(parent, seq, _, _) => exportUnaryRule( parent, seq.getSequent, "notl" )
    case NegRightRule(parent, seq, _, _) => exportUnaryRule( parent, seq.getSequent, "notr" )
    case ForallLeftRule(parent, seq, _, _, _) => exportUnaryRule( parent, seq.getSequent, "foralll" )
    case ExistsRightRule(parent, seq, _, _, _) => exportUnaryRule( parent, seq.getSequent, "existsr" )
    case ForallRightRule(parent, seq, _, _, _) => exportUnaryRule( parent, seq.getSequent, "forallr" )
    case ExistsLeftRule(parent, seq, _, _, _) => exportUnaryRule( parent, seq.getSequent, "existsl" )
    case DefinitionLeftRule(parent, seq, _, _) => exportUnaryRule( parent, seq.getSequent, "existsl" )
    case DefinitionRightRule(parent, seq, _, _) => exportUnaryRule( parent, seq.getSequent, "defr" )

    case CutRule(p1, p2, seq, _, _) => exportBinaryRule(p1, p2, seq.getSequent, "cut")
    case AndRightRule(p1, p2, seq, _, _, _) => exportBinaryRule(p1, p2, seq.getSequent, "andr")
    case OrLeftRule(p1, p2, seq, _, _, _) => exportBinaryRule(p1, p2, seq.getSequent, "orl")
    case ImpLeftRule(p1, p2, seq, _, _, _) => exportBinaryRule(p1, p2, seq.getSequent, "impll")
    case EquationLeft1Rule(p1, p2, seq, _, _, _) => exportBinaryRule(p1, p2, seq.getSequent, "eql1")
    case EquationLeft2Rule(p1, p2, seq, _, _, _) => exportBinaryRule(p1, p2, seq.getSequent, "eql2")
    case EquationRight1Rule(p1, p2, seq, _, _, _) => exportBinaryRule(p1, p2, seq.getSequent, "eqr1")
    case EquationRight2Rule(p1, p2, seq, _, _, _) => exportBinaryRule(p1, p2, seq.getSequent, "eqr2")
  }

  def exportUnaryRule( parent: LKProof, conc: Sequent, rt: String ) =
    <rule type={rt}> {exportSequent( conc )} {exportProof( parent )} </rule>

  def exportBinaryRule( p1: LKProof, p2: LKProof, conc: Sequent, rt: String ) =
    <rule type={rt}> {exportSequent( conc )} {exportProof( p1 )} {exportProof( p2 )} </rule>
}

object saveXML {
  def apply( proofs: List[Pair[String, LKProof]], sequentlists: List[Pair[String, List[Sequent]]], filename: String ) =
  {
    val exporter = new LKExporter{}
    val p_xmls = proofs.map( p => exporter.exportProof(p._1, p._2) )
    val s_xmls = sequentlists.map( p => exporter.exportSequentList(p._1, p._2) )
    val output =
      <proofdatabase>
        <definitionlist/>
        <axiomset/>
        { p_xmls }
        { s_xmls }
        <variabledefinitions/>
      </proofdatabase>
    scala.xml.XML.saveFull(filename, output, "UTF-8", true,
        DocType( "proofdatabase", SystemID( "http://www.logic.at/ceres/xml/5.0/proofdatabase.dtd" ) , Nil ) )
  }
}
