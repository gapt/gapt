package at.logic.algorithms.cutIntroduction

import at.logic.algorithms.matching.FOLMatchingAlgorithm
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

  def productionIsIncluded( p: Production ) = Atom( s"p,$p" )

  def termUsesProduction( t: FOLTerm, p: Production ) = Atom( s"tp,$t,$p" )
  def restForTerm( t: FOLTerm, n: FOLVar, rest: FOLTerm ) = Atom( s"r,$t,$n=$rest" )

  def generatesTerm( t: FOLTerm ) = {
    val cs = List.newBuilder[FOLFormula]

    cs += restForTerm( t, g.axiom, t )

    Utils.subterms( t ) foreach { rest =>
      g.productions foreach {
        case p @ ( d, rhs ) =>
          FOLMatchingAlgorithm.matchTerm( rest, rhs, freeVariables( rhs ) ) match {
            case Some( matching ) =>
              cs += Imp( And( restForTerm( t, d, rest ), termUsesProduction( t, p ) ),
                And( matching.folmap map {
                  case ( v, smallerRest ) =>
                    restForTerm( t, v, smallerRest.asInstanceOf[FOLTerm] )
                } toList ) )
            case None => ()
          }
      }
    }

    g.nonTerminals foreach { d =>
      val prods = g.productions( d )
      cs += Or( prods map { p => termUsesProduction( t, p ) } toList )

      for ( p <- prods ) cs += Imp( termUsesProduction( t, p ), productionIsIncluded( p ) )

      for ( p <- prods; q <- prods ) cs += Or( Neg( termUsesProduction( t, p ) ), Neg( termUsesProduction( t, q ) ) )
    }

    And( cs result )
  }

  def coversLanguage( lang: Seq[FOLTerm] ) = And( lang map generatesTerm toList )
}