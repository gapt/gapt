/*
 * LKExporter.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.calculus.xml

import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.quantifiers._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.parsing.ExportingException
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.lkExtractors._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.parsing.language.xml.HOLTermExporter

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

  def exportSequentList(ls: List[Sequent]) =
    <sequentlist>
      {ls.map(x => exportSequent(x))}
    </sequentlist>
}
