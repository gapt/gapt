package at.logic.algorithms.cutIntroduction

import at.logic.language.fol._

object normalForms {
  def apply( terms: Seq[FOLTerm], nonTerminals: Seq[FOLVar] ): Seq[FOLTerm] = {
    val tgd = new TreeGrammarDecompositionPWM( terms toList, nonTerminals.length )
    tgd.suffKeys()
    val renameToOurNonTerminals = Substitution( tgd.nonTerminals zip nonTerminals )
    tgd.keyList map { k => renameToOurNonTerminals( k ) } toSeq
  }
}

object TratGrammar {
  type Production = ( FOLVar, FOLTerm )
}

case class TratGrammar( axiom: FOLVar, productions: Seq[TratGrammar.Production] ) {
  val nonTerminals = productions map ( _._1 ) distinct

  def productions( nonTerminal: FOLVar ): Seq[TratGrammar.Production] = productions filter ( _._1 == nonTerminal )
  def rightHandSides( nonTerminal: FOLVar ) = productions( nonTerminal ) map ( _._2 )

  override def toString = s"($axiom, {${productions map { case ( d, t ) => s"$d -> $t" } mkString ", "}})"
}

case class GrammarMinimizationFormula( g: TratGrammar ) {
  import TratGrammar._

  def productionIsIncluded( p: Production ) = FOLVar( s"p,$p" )

  def termUsesProduction( t: FOLTerm, p: Production ) = FOLVar( s"tp,$t,$p" )
  def restForTerm( t: FOLTerm, n: FOLVar, rest: FOLVar ) = FOLVar( s"r,$t,$n=$rest" )

  def generatesTerm( t: FOLTerm ) = {

  }
}