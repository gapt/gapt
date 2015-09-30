package at.logic.gapt.grammars

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ FOLSubTerms, FOLMatchingAlgorithm }
import at.logic.gapt.expr.hol.lcomp
import at.logic.gapt.expr.hol.simplify
import at.logic.gapt.expr.hol.toNNF
import at.logic.gapt.provers.maxsat.{ MaxSATSolver, MaxSat4j }
import at.logic.gapt.utils.dssupport.ListSupport
import at.logic.gapt.utils.logging.metrics

import scala.collection.{ GenTraversable, mutable }

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

object termSize {
  def apply( t: FOLTerm ): Int = t match {
    case FOLFunction( _, as ) => 1 + as.map( apply ).sum
    case FOLVar( _ )          => 1
  }
}

object nfsSubsumedByAU {
  def apply( au: FOLTerm, nts: Set[FOLVar] ): Set[FOLTerm] = apply( au, nts, nts,
    LambdaPosition.getPositions( au, _.isInstanceOf[FOLTerm] ).
      groupBy( au( _ ).asInstanceOf[FOLTerm] ).toList.
      sortBy { case ( st, _ ) => termSize( st ) }.
      map( _._2 ) )

  private def apply( au: FOLTerm, ntsToDo: Set[FOLVar], nts: Set[FOLVar], allPositions: List[List[LambdaPosition]] ): Set[FOLTerm] = allPositions match {
    case positions :: otherPositions =>
      positions.flatMap { au.get( _ ) }.headOption.
        map( _.asInstanceOf[FOLTerm] ).
        filterNot( freeVariables( _ ) subsetOf nts ).
        map { st =>
          ntsToDo flatMap { nt =>
            var generalization = au
            for ( pos <- positions ) generalization = generalization.replace( pos, nt ).asInstanceOf[FOLTerm]
            apply( generalization, ntsToDo - nt, nts, otherPositions )
          }
        }.getOrElse( Set() ) ++ apply( au, ntsToDo, nts, otherPositions )
    case Nil if freeVariables( au ) subsetOf nts => Set( au )
    case _                                       => Set()
  }
}

object normalForms {
  def apply( lang: GenTraversable[FOLTerm], nonTerminals: Seq[FOLVar] ): Set[FOLTerm] = {
    lang foreach { term => require( freeVariables( term ) isEmpty ) }

    val antiUnifiers = ListSupport.boundedPower( lang toList, nonTerminals.size + 1 ).
      map( antiUnificator( _ ) ).toSet[FOLTerm]
    antiUnifiers flatMap { au => nfsSubsumedByAU( au, nonTerminals.toSet ) }
  }
}

class TermGenerationFormula( g: VectTratGrammar, t: FOLTerm ) {
  import VectTratGrammar._

  def vectProductionIsIncluded( p: Production ): FOLFormula = FOLAtom( s"$p" )
  def valueOfNonTerminal( n: FOLVar, value: FOLTerm ): FOLFormula = FOLAtom( s"$n=$value" )

  def formula: FOLFormula = {
    val notASubTerm = rename( FOLConst( "⊥" ), constants( t ).toList )

    // we try not generate the formulas for all subterms, but only for those which are needed
    val matchingsToHandle = mutable.Queue[Map[FOLVar, FOLTerm]]()

    def Match( t: List[FOLTerm], s: List[FOLTerm] ) =
      FOLMatchingAlgorithm.matchTerms( s zip t filter { _._2 != notASubTerm } ) match {
        case Some( matching ) =>
          matchingsToHandle += matching.folmap
          And( matching.folmap.toSeq map {
            case ( beta, r ) =>
              valueOfNonTerminal( beta, r )
          } )
        case None => Bottom()
      }

    def Case( ntVect: NonTerminalVect, t: List[FOLTerm] ) =
      And( ( ntVect, t ).zipped map valueOfNonTerminal ) --> Or( g.productions( ntVect ).toSeq map {
        case p @ ( _, s ) =>
          vectProductionIsIncluded( p ) & Match( t, s )
      } )

    val possibleSingleVariableAssignments = mutable.Map[FOLVar, Set[FOLTerm]]().withDefaultValue( Set() )

    val cs = Seq.newBuilder[FOLFormula]

    // value of axiom must be t
    cs += valueOfNonTerminal( g.axiom, t )

    // add base cases for subterm discovery
    matchingsToHandle += Map( g.axiom -> t )

    val alreadyHandledAssignments = mutable.Set[( NonTerminalVect, List[FOLTerm] )]()
    if ( g.nonTerminals.size == 2 ) {
      matchingsToHandle dequeueAll { newPartialAssg =>
        val assignment = if ( newPartialAssg contains g.axiom )
          List( g.axiom ) -> List( newPartialAssg( g.axiom ) )
        else
          g.nonTerminals( 1 ) -> g.nonTerminals( 1 ).map( newPartialAssg.getOrElse( _, notASubTerm ) )

        if ( !( alreadyHandledAssignments contains assignment )
          && assignment._2.exists( _ != notASubTerm ) )
          cs += simplify( Case( assignment._1, assignment._2 ) )

        alreadyHandledAssignments += assignment

        assignment.zipped foreach { possibleSingleVariableAssignments( _ ) += _ }

        true // remove this value from the queue
      }
    } else {
      matchingsToHandle ++=
        g.nonTerminals.filter( _.size > 1 ).flatten.map( _ -> notASubTerm ).map( Map( _ ) )

      val alreadyHandledAssignments = mutable.Set[( NonTerminalVect, List[FOLTerm] )]()
      matchingsToHandle dequeueAll { newSingleVarAssgs =>
        newSingleVarAssgs foreach { newSingleVarAssg =>
          val ( newNT, newValue ) = newSingleVarAssg
          val containingNonTerminalVect = g.nonTerminals.find( _ contains newNT ).get
          val possibleAssignments = containingNonTerminalVect.foldRight( List[List[FOLTerm]]( Nil ) ) {
            case ( nt, assgs ) if nt == newNT => assgs.map( newValue :: _ )
            case ( nt, assgs )                => assgs flatMap { assg => possibleSingleVariableAssignments( nt ) map ( _ :: assg ) }
          }
          possibleAssignments foreach { assignment =>
            if ( !( alreadyHandledAssignments contains ( containingNonTerminalVect -> assignment ) )
              && assignment.exists( _ != notASubTerm ) )
              cs += simplify( Case( containingNonTerminalVect, assignment ) )

            alreadyHandledAssignments += containingNonTerminalVect -> assignment
          }
          possibleSingleVariableAssignments( newNT ) += newValue
        }

        true // remove this value from the queue
      }
    }

    for ( ( d, vs ) <- possibleSingleVariableAssignments )
      if ( vs contains notASubTerm )
        cs += exactly oneOf ( vs.toSeq map { valueOfNonTerminal( d, _ ) } )
      else
        cs += atMost oneOf ( vs.toSeq map { valueOfNonTerminal( d, _ ) } )

    And( cs.result() )
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

  def coversLanguage( lang: Traversable[FOLTerm] ) = And( lang map generatesTerm toList )
}

class GrammarMinimizationFormula( g: TratGrammar ) extends VectGrammarMinimizationFormula( g toVectTratGrammar ) {
  def productionIsIncluded( p: TratGrammar.Production ) = FOLAtom( s"p,$p" )
  override def vectProductionIsIncluded( p: VectTratGrammar.Production ) = productionIsIncluded( p._1( 0 ), p._2( 0 ) )
}

object normalFormsProofGrammar {
  def apply( lang: Set[FOLTerm], n: Int ) = {
    val rhsNonTerminals = ( 1 until n ).inclusive map { i => FOLVar( s"α_$i" ) }
    val topLevelNFs = normalForms( lang, rhsNonTerminals ).filter( !_.isInstanceOf[FOLVar] )
    val argumentNFs = normalForms( FOLSubTerms( lang flatMap { case FOLFunction( _, as ) => as } ), rhsNonTerminals.tail )
    val axiom = FOLVar( "τ" )
    TratGrammar( axiom, axiom +: rhsNonTerminals, topLevelNFs.map( axiom -> _ ) ++ argumentNFs.flatMap { nf =>
      val fvs = freeVariables( nf )
      val lowestIndex = ( fvs.map( rhsNonTerminals.indexOf( _ ) ) + rhsNonTerminals.size ).min
      ( 0 until lowestIndex ) map { i => rhsNonTerminals( i ) -> nf }
    } )
  }
}

object minimizeGrammar {
  def apply( g: TratGrammar, lang: Set[FOLTerm], maxSATSolver: MaxSATSolver = new MaxSat4j ): TratGrammar = {
    val formula = new GrammarMinimizationFormula( g )
    val hard = formula.coversLanguage( lang )
    val atomsInHard = atoms( hard )
    val soft = g.productions map formula.productionIsIncluded filter atomsInHard.contains map ( Neg( _ ) -> 1 )
    maxSATSolver.solveWPM( List( hard ), soft toList ) match {
      case Some( interp ) => TratGrammar( g.axiom, g.nonTerminals,
        g.productions filter { p => interp.interpret( formula.productionIsIncluded( p ) ) } )
      case None => throw new Exception( "Grammar does not cover language." )
    }
  }
}

object findMinimalGrammar {
  def apply( lang: Traversable[FOLTerm], numberOfNonTerminals: Int, maxSATSolver: MaxSATSolver = new MaxSat4j ) = {
    val polynomialSizedCoveringGrammar = normalFormsProofGrammar( lang toSet, numberOfNonTerminals )
    minimizeGrammar( polynomialSizedCoveringGrammar, lang toSet, maxSATSolver )
  }
}

object takeN {
  def apply[A]( n: Int, from: Set[A] ): Seq[List[A]] = n match {
    case 0 => Seq( Nil )
    case _ =>
      takeN( n - 1, from ) flatMap { rest =>
        from.map( _ :: rest )
      }
  }
}

object normalFormsProofVectGrammar {
  import VectTratGrammar._

  def apply( lang: Set[FOLTerm], arities: Seq[Int] ): VectTratGrammar = {
    val rhsNonTerminals = arities.zipWithIndex map { case ( arity, i ) => ( 0 until arity ).map( j => FOLVar( s"α_${i}_$j" ) ).toList }
    apply( lang, FOLVar( "τ" ), rhsNonTerminals )
  }

  def apply( lang: Set[FOLTerm], axiom: FOLVar, nonTermVects: Seq[NonTerminalVect] ): VectTratGrammar = {
    val topLevelNFs = normalForms( lang, nonTermVects flatten ).filter( !_.isInstanceOf[FOLVar] )
    val argumentNFs = normalForms( FOLSubTerms( lang flatMap { case FOLFunction( _, as ) => as } ), nonTermVects.tail flatten )

    VectTratGrammar( axiom, List( axiom ) +: nonTermVects,
      topLevelNFs.map( List( axiom ) -> List( _ ) ) ++
        nonTermVects.zipWithIndex.flatMap {
          case ( a, i ) =>
            val allowedNonTerms = nonTermVects.drop( i + 1 ).flatten.toSet
            val allowedRHS = argumentNFs filter { nf => freeVariables( nf ) subsetOf allowedNonTerms }
            takeN( a.size, allowedRHS ).map( a -> _ )
        } )
  }
}

object minimizeVectGrammar {
  def apply( g: VectTratGrammar, lang: Set[FOLTerm], maxSATSolver: MaxSATSolver = new MaxSat4j ): VectTratGrammar = {
    val formula = new VectGrammarMinimizationFormula( g )
    val hard = metrics.time( "minform" ) { formula.coversLanguage( lang ) }
    metrics.value( "minform_lcomp", lcomp( simplify( toNNF( hard ) ) ) )
    val atomsInHard = atoms( hard )
    val soft = g.productions map formula.vectProductionIsIncluded filter atomsInHard.contains map ( Neg( _ ) -> 1 )
    metrics.time( "maxsat" ) { maxSATSolver.solveWPM( List( hard ), soft toList ) } match {
      case Some( interp ) => VectTratGrammar( g.axiom, g.nonTerminals,
        g.productions filter { p => interp.interpret( formula.vectProductionIsIncluded( p ) ) } )
      case None => throw new Exception( "Grammar does not cover language." )
    }
  }
}

object findMinimalVectGrammar {
  def apply( lang: Set[FOLTerm], aritiesOfNonTerminals: Seq[Int], maxSATSolver: MaxSATSolver = new MaxSat4j ) = {
    val polynomialSizedCoveringGrammar = metrics.time( "nfgrammar" ) { normalFormsProofVectGrammar( lang, aritiesOfNonTerminals ) }
    metrics.value( "nfgrammar", polynomialSizedCoveringGrammar.size )
    minimizeVectGrammar( polynomialSizedCoveringGrammar, lang, maxSATSolver )
  }
}
