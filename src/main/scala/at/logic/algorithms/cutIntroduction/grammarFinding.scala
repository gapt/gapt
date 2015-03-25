package at.logic.algorithms.cutIntroduction

import at.logic.algorithms.matching.FOLMatchingAlgorithm
import at.logic.language.fol._
import at.logic.language.fol.replacements.{ Replacement, getAllPositionsFOL }
import at.logic.language.hol.HOLPosition
import at.logic.language.lambda.symbols.SymbolA
import at.logic.provers.maxsat.MaxSATSolver.MaxSATSolver
import at.logic.provers.maxsat.{ MaxSATSolver, MaxSAT }
import at.logic.utils.dssupport.ListSupport

object FunctionOrConstant {
  def unapply( term: FOLTerm ): Option[( SymbolA, List[FOLTerm] )] = term match {
    case Function( s, args ) => Some( ( s, args ) )
    case c: FOLConst         => Some( ( c.sym, Nil ) )
  }
}

object SameRootSymbol {
  def unapply( terms: Seq[FOLTerm] ): Option[( SymbolA, List[List[FOLTerm]] )] =
    unapply( terms toList )

  def unapply( terms: List[FOLTerm] ): Option[( SymbolA, List[List[FOLTerm]] )] = terms match {
    case FunctionOrConstant( s, as ) :: Nil => Some( ( s, as map ( List( _ ) ) ) )
    case FunctionOrConstant( s, as ) :: SameRootSymbol( t, bs ) if s == t =>
      Some( ( s, ( as, bs ).zipped map ( _ :: _ ) ) )
    case _ => None
  }
}

object antiUnificator {
  def apply( terms: Seq[FOLTerm] ): FOLTerm = terms match {
    case SameRootSymbol( s, as ) => Function( s, as map apply )
    case _                       => FOLVar( s"β[${terms mkString ","}]" )
  }
}

object characteristicPartition {
  def apply( term: FOLTerm ): List[List[List[Int]]] = {
    getAllPositionsFOL( term ).groupBy( _._2 ).values.map( _.map( _._1 ) ).toList
  }
}

object normalForms {
  def apply( lang: Seq[FOLTerm], nonTerminals: Seq[FOLVar] ): Seq[FOLTerm] = {
    val nfs = Set.newBuilder[FOLTerm]
    ListSupport.boundedPower( lang toList, nonTerminals.size + 1 ) foreach { subset =>
      val au = antiUnificator( subset )
      val charP = characteristicPartition( au )
      val possibleSubsts = nonTerminals.foldLeft[List[List[( FOLVar, List[List[Int]] )]]]( List( Nil ) ) {
        case ( substs, nonTerminal ) =>
          substs flatMap { subst =>
            subst :: ( charP map ( setOfPos => ( nonTerminal, setOfPos ) :: subst ) )
          }
      }
      possibleSubsts foreach { subst =>
        var nf = au
        subst foreach {
          case ( v, setOfPos ) =>
            setOfPos foreach { pos =>
              try {
                if ( nf.isDefinedAt( HOLPosition( pos ) ) )
                  nf = new Replacement( pos, v )( nf ).asInstanceOf[FOLTerm]
              } catch {
                // FIXME: Replacements are buggy...
                case _: IllegalArgumentException => ()
              }
            }
        }
        if ( freeVariables( nf ).forall( nonTerminals.contains( _ ) ) ) nfs += nf
      }
    }
    nfs.result.toList
  }
}

object tratNormalForms {
  def apply( terms: Seq[FOLTerm], nonTerminals: Seq[FOLVar] ): Seq[FOLTerm] = {
    normalForms( Utils.subterms( terms toList ) toSeq, nonTerminals )
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
    val nfs = tratNormalForms( lang, rhsNonTerminals )
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
  def apply( g: TratGrammar, lang: Seq[FOLTerm], maxSATSolver: MaxSATSolver = MaxSATSolver.ToySAT ): TratGrammar = {
    val formula = GrammarMinimizationFormula( g )
    val hard = formula.coversLanguage( lang )
    val soft = g.productions map { p => Neg( formula.productionIsIncluded( p ) ) -> 1 }
    new MaxSAT( maxSATSolver ).solvePWM( List( hard ), soft toList ) match {
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