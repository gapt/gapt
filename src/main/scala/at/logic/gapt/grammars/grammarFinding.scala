package at.logic.gapt.grammars

import at.logic.gapt.expr._
import at.logic.gapt.language.fol.algorithms.FOLMatchingAlgorithm
import at.logic.gapt.language.fol.{ FOLSubstitution, Utils }
import at.logic.gapt.provers.maxsat.{ MaxSATSolver, MaxSat4j }
import at.logic.gapt.utils.dssupport.ListSupport

import scala.collection.mutable

object SameRootSymbol {
  def unapply( terms: Seq[FOLTerm] ): Option[( String, List[List[FOLTerm]] )] =
    unapply( terms toList )

  def unapply( terms: List[FOLTerm] ): Option[( String, List[List[FOLTerm]] )] = terms match {
    case FOLFunction( s, as ) :: Nil => Some( ( s, as map ( List( _ ) ) ) )
    case FOLFunction( s, as ) :: SameRootSymbol( t, bs ) if s == t =>
      Some( ( s, ( as, bs ).zipped map ( _ :: _ ) ) )
    case _ => None
  }
}

private class antiUnificator {
  private var varIndex = 0
  private val vars = mutable.Map[Seq[FOLTerm], FOLVar]()
  private def getVar( terms: Seq[FOLTerm] ) =
    vars.getOrElseUpdate( terms, { varIndex += 1; FOLVar( s"β$varIndex" ) } )

  def apply( terms: Seq[FOLTerm] ): FOLTerm = terms match {
    case SameRootSymbol( s, as ) => FOLFunction( s, as map apply )
    case _                       => getVar( terms )
  }
}

object antiUnificator {
  def apply( terms: Seq[FOLTerm] ): FOLTerm = new antiUnificator().apply( terms )
}

object normalizeNonTerminals {
  def apply( term: FOLTerm ): FOLTerm = {
    val renaming: Seq[( FOLVar, FOLTerm )] =
      freeVariables( term ).distinct.zipWithIndex map { case ( v, i ) => v -> FOLVar( s"β$i" ) }
    FOLSubstitution( renaming )( term )
  }
}

object characteristicPartition {
  def apply( term: FOLTerm ): List[List[LambdaPosition]] =
    LambdaPosition.getPositions( term, _.isInstanceOf[FOLTerm] ).groupBy( term.get ).values.toList
}

object normalForms {
  def apply( lang: Seq[FOLTerm], nonTerminals: Seq[FOLVar] ): Seq[FOLTerm] = {
    val antiUnifiers = ListSupport.boundedPower( lang toList, nonTerminals.size + 1 )
      .map( terms => normalizeNonTerminals( antiUnificator( terms ) ) ).toSet
    val nfs = Set.newBuilder[FOLTerm]
    antiUnifiers foreach { au =>
      val charP = characteristicPartition( au )
      val possibleSubsts = nonTerminals.foldLeft[List[List[( FOLVar, List[LambdaPosition] )]]]( List( Nil ) ) {
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
              if ( nf.isDefinedAt( pos ) )
                nf = LambdaPosition.replace( nf, pos, v ).asInstanceOf[FOLTerm]
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

object VectTratGrammar {
  type NonTerminalVect = List[FOLVar]
  type Production = ( NonTerminalVect, List[FOLTerm] )
}

case class VectTratGrammar( axiom: FOLVar, nonTerminals: Seq[VectTratGrammar.NonTerminalVect], productions: Seq[VectTratGrammar.Production] ) {
  import VectTratGrammar._

  def productions( nonTerminalVect: NonTerminalVect ): Seq[Production] = productions filter ( _._1 == nonTerminalVect )
  def rightHandSides( nonTerminal: NonTerminalVect ) = productions( nonTerminal ) map ( _._2 )

  productions foreach {
    case p @ ( a, t ) =>
      require( nonTerminals contains a, s"unknown non-terminal vector $a in $p" )
      val i = nonTerminals.indexOf( a )
      val allowedNonTerminals = nonTerminals.drop( i + 1 ).flatten.toSet
      t.flatMap( freeVariables( _ ) ) foreach { fv =>
        require( allowedNonTerminals contains fv, s"acyclicity violated in $p: $fv not in $allowedNonTerminals" )
      }
  }
  require( nonTerminals contains Seq( axiom ), s"axiom is unknown non-terminal vector $axiom" )

  def language: Set[FOLTerm] = {
    var lang = Set[FOLTerm]( axiom )
    nonTerminals.foreach { a =>
      val P_a = productions(a)
      if (P_a.nonEmpty)
        lang = P_a.flatMap { p =>
          lang.map(FOLSubstitution(p.zipped toSeq).apply)
        } toSet
    }
    lang filter ( freeVariables( _ ).isEmpty )
  }
}

object TratGrammar {
  type Production = ( FOLVar, FOLTerm )

  def asVectTratGrammarProduction( p: Production ): VectTratGrammar.Production =
    List( p._1 ) -> List( p._2 )

  def apply( axiom: FOLVar, productions: Seq[TratGrammar.Production] ): TratGrammar = {
    val nonTerminals = ( axiom +: ( productions flatMap { p => p._1 :: freeVariables( p._2 ) } ) ).distinct
    TratGrammar( axiom, nonTerminals, productions )
  }
}

case class TratGrammar( axiom: FOLVar, nonTerminals: Seq[FOLVar], productions: Seq[TratGrammar.Production] ) {
  import TratGrammar._

  def productions( nonTerminal: FOLVar ): Seq[Production] = productions filter ( _._1 == nonTerminal )
  def rightHandSides( nonTerminal: FOLVar ) = productions( nonTerminal ) map ( _._2 )

  productions foreach {
    case p @ ( a, t ) =>
      require( nonTerminals contains a, s"unknown non-terminal $a in $p" )
      val allowedNonTerminals = nonTerminals.drop( nonTerminals.indexOf( a ) + 1 ).toSet
      freeVariables( t ) foreach { fv =>
        require( allowedNonTerminals contains fv, s"acyclicity violated in $p: $fv not in $allowedNonTerminals" )
      }
  }
  require( nonTerminals contains axiom, s"axiom is unknown non-terminal $axiom" )

  override def toString = s"($axiom, {${productions map { case ( d, t ) => s"$d -> $t" } mkString ", "}})"

  def toVectTratGrammar: VectTratGrammar = VectTratGrammar(
    axiom, nonTerminals map ( List( _ ) ),
    productions map asVectTratGrammarProduction )

  def language: Set[FOLTerm] = toVectTratGrammar language
}

class TermGenerationFormula( g: VectTratGrammar, t: FOLTerm ) {
  import VectTratGrammar._

  def vectProductionIsIncluded( p: Production ): FOLFormula = FOLAtom( s"$p" )
  def valueOfNonTerminal( n: FOLVar, value: FOLTerm ): FOLFormula = FOLAtom( s"$n=$value" )

  val Omega = FOLConst( "Ω" )

  def formula: FOLFormula = {
    val cs = List.newBuilder[FOLFormula]

    // TODO: assert that Omega does not occur in g or t

    // value of axiom must be t
    cs += valueOfNonTerminal( g.axiom, t )

    // possible values must decompose correctly
    val singleVariableAssignmentsToHandle = mutable.Queue( g.axiom -> t )
    g.nonTerminals foreach { ntVect =>
      if ( ntVect.size > 1 ) ntVect foreach { nt => singleVariableAssignmentsToHandle.enqueue( nt -> Omega ) }
    }

    var possibleSingleVariableAssignments = Map[FOLVar, Set[FOLTerm]]().withDefaultValue( Set() )
    var alreadyHandledAssignments = Set[( NonTerminalVect, List[FOLTerm] )]()
    singleVariableAssignmentsToHandle.dequeueAll {
      case ( newNT, newValue ) =>
        val containingNonTerminalVect = g.nonTerminals.find( _.contains( newNT ) ).get
        val possibleAssignments = containingNonTerminalVect.foldRight( List[List[FOLTerm]]( Nil ) ) {
          case ( nt, assgs ) if nt == newNT => assgs.map( newValue :: _ )
          case ( nt, assgs )                => assgs flatMap { assg => possibleSingleVariableAssignments( nt ) map ( _ :: assg ) }
        }
        possibleAssignments foreach { assignment =>
          if ( !( alreadyHandledAssignments contains ( containingNonTerminalVect -> assignment ) ) )
            cs += Imp( And( containingNonTerminalVect.zip( assignment ) map { case ( nt, value ) => valueOfNonTerminal( nt, value ) } ),
              Or( g.productions( containingNonTerminalVect ) map {
                case p @ ( _, rhss ) =>
                  And( containingNonTerminalVect.zip( assignment ).zip( rhss ) map {
                    case ( ( nt, value ), rhs ) if value == Omega => Top()
                    case ( ( nt, value ), rhs ) =>
                      FOLMatchingAlgorithm.matchTerms( rhs, value ) match {
                        case Some( matching ) =>
                          And( vectProductionIsIncluded( p ),
                            And( matching.folmap map {
                              case ( v, smallerValue: FOLTerm ) =>
                                singleVariableAssignmentsToHandle enqueue ( v -> smallerValue )
                                valueOfNonTerminal( v, smallerValue )
                            } toList ) )
                        case None => Bottom()
                      }
                  } )
              } toList ) )

          alreadyHandledAssignments += containingNonTerminalVect -> assignment
        }
        possibleSingleVariableAssignments = possibleSingleVariableAssignments.updated( newNT, possibleSingleVariableAssignments( newNT ) + newValue )

        true // remove this value from the queue
    }

    // values are unique
    for ( ( d, v1s ) <- possibleSingleVariableAssignments; ( d2, v2s ) <- possibleSingleVariableAssignments; v1 <- v1s; v2 <- v2s if d == d2 && v1 != v2 )
      cs += Or( Neg( valueOfNonTerminal( d, v1 ) ), Neg( valueOfNonTerminal( d, v2 ) ) )

    // values exist
    for ( ( d, vs ) <- possibleSingleVariableAssignments if vs contains Omega )
      cs += Or( vs map ( valueOfNonTerminal( d, _ ) ) toList )

    And( cs result )
  }
}

class VectGrammarMinimizationFormula( g: VectTratGrammar ) {
  import VectTratGrammar._

  def vectProductionIsIncluded( p: Production ) = FOLAtom( s"$p" )
  def valueOfNonTerminal( t: FOLTerm, n: FOLVar, rest: FOLTerm ) = FOLAtom( s"$t:$n=$rest" )

  def generatesTerm( t: FOLTerm ) = new TermGenerationFormula( g, t ) {
    override def vectProductionIsIncluded( p: Production ) =
      VectGrammarMinimizationFormula.this.vectProductionIsIncluded( p )
    override def valueOfNonTerminal( n: FOLVar, value: FOLTerm ) =
      VectGrammarMinimizationFormula.this.valueOfNonTerminal( t, n, value )
  }.formula

  def coversLanguage( lang: Seq[FOLTerm] ) = And( lang map generatesTerm toList )
}

class GrammarMinimizationFormula( g: TratGrammar ) extends VectGrammarMinimizationFormula( g toVectTratGrammar ) {
  def productionIsIncluded( p: TratGrammar.Production ) = FOLAtom( s"p,$p" )
  override def vectProductionIsIncluded( p: VectTratGrammar.Production ) = productionIsIncluded( p._1( 0 ), p._2( 0 ) )
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
  def apply( g: TratGrammar, lang: Seq[FOLTerm], maxSATSolver: MaxSATSolver = new MaxSat4j() ): TratGrammar = {
    val formula = new GrammarMinimizationFormula( g )
    val hard = formula.coversLanguage( lang )
    val atomsInHard = atoms( hard )
    val soft = g.productions map formula.productionIsIncluded filter atomsInHard.contains map ( Neg( _ ) -> 1 )
    maxSATSolver.solveWPM( List( hard ), soft toList ) match {
      case Some( interp ) => TratGrammar( g.axiom,
        g.productions filter { p => interp.interpret( formula.productionIsIncluded( p ) ) } )
      case None => throw new Exception( "Grammar does not cover language." )
    }
  }
}

object findMinimalGrammar {
  def apply( lang: Seq[FOLTerm], numberOfNonTerminals: Int, maxSATSolver: MaxSATSolver = new MaxSat4j ) = {
    val polynomialSizedCoveringGrammar = normalFormsTratGrammar( lang, numberOfNonTerminals )
    minimizeGrammar( polynomialSizedCoveringGrammar, lang, maxSATSolver )
  }
}