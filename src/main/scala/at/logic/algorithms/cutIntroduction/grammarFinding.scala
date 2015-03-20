package at.logic.algorithms.cutIntroduction

import at.logic.algorithms.matching.FOLMatchingAlgorithm
import at.logic.language.fol._
import at.logic.provers.maxsat.{ MaxSATSolver, MaxSAT }

object normalFormsWrtSubsets {
  def apply( terms: Seq[FOLTerm], nonTerminals: Seq[FOLVar] ): Seq[FOLTerm] = {
    val tgd = new TreeGrammarDecompositionPWM( terms toList, nonTerminals.length )
    tgd.suffKeys()
    val renameToOurNonTerminals = Substitution( tgd.nonTerminals zip nonTerminals )
    ( tgd.keyList map { k => renameToOurNonTerminals( k ) } toSeq ) ++ Utils.subterms( terms toList )
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
  def valueOfNonTerminal( t: FOLTerm, n: FOLVar, rest: FOLTerm ) = Atom( s"v,$t,$n=$rest" )

  def generatesTerm( t: FOLTerm ) = {
    val cs = List.newBuilder[FOLFormula]

    cs += valueOfNonTerminal( t, g.axiom, t )

    // possible values must decompose correctly
    val possibleValues = Utils.subterms( t )
    for ( value <- possibleValues; nt <- g nonTerminals )
      cs += Imp( valueOfNonTerminal( t, nt, value ),
        Or( g.productions( nt ) map {
          case p @ ( _, rhs ) =>
            FOLMatchingAlgorithm.matchTerm( rhs, value, List() ) match {
              case Some( matching ) =>
                And( productionIsIncluded( p ),
                  And( matching.folmap map {
                    case ( v, smallerRest ) =>
                      valueOfNonTerminal( t, v, smallerRest.asInstanceOf[FOLTerm] )
                  } toList ) )
              case None => BottomC
            }
        } toList ) )

    // values are unique
    for ( d <- g nonTerminals; v1 <- possibleValues; v2 <- possibleValues if v1 != v2 )
      cs += Or( Neg( valueOfNonTerminal( t, d, v1 ) ), Neg( valueOfNonTerminal( t, d, v2 ) ) )

    And( cs result )
  }

  def coversLanguage( lang: Seq[FOLTerm] ) = And( lang map generatesTerm toList )
}

object normalFormsTratGrammar {
  def apply( lang: Seq[FOLTerm], n: Int ) = {
    val rhsNonTerminals = ( 1 until n ).inclusive map { i => FOLVar( s"α_$i" ) }
    val nfs = normalFormsWrtSubsets( lang, rhsNonTerminals )
    val nonTerminals = FOLVar( "τ" ) +: rhsNonTerminals
    TratGrammar( nonTerminals( 0 ), nfs flatMap { nf =>
      freeVariables( nf ) match {
        case Nil => nonTerminals map { v => v -> nf }
        case fvs =>
          val lowestIndex = fvs.map( nonTerminals.indexOf( _ ) ).min
          ( 0 until lowestIndex ) map { v => nonTerminals( v ) -> nf }
      }
    } )
  }
}

object minimizeGrammar {
  def apply( g: TratGrammar, lang: Seq[FOLTerm] ): TratGrammar = {
    val formula = GrammarMinimizationFormula( g )
    val hard = formula.coversLanguage( lang )
    val soft = g.productions map { p => Neg( formula.productionIsIncluded( p ) ) -> 1 }
    new MaxSAT( MaxSATSolver.ToySolver ).solvePWM( List( hard ), soft toList ) match {
      case Some( interp ) => TratGrammar( g.axiom,
        g.productions filter { p => interp.interpretAtom( formula.productionIsIncluded( p ) ) } )
      case None => throw new TreeGrammarDecompositionException( "Grammar does not cover language." )
    }
  }
}

object findMinimalGrammar {
  def apply( lang: Seq[FOLTerm], numberOfNonTerminals: Int ) = {
    val polynomialSizedCoveringGrammar = normalFormsTratGrammar( lang, numberOfNonTerminals )
    minimizeGrammar( polynomialSizedCoveringGrammar, lang )
  }
}