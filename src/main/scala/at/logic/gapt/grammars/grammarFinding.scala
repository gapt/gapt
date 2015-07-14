package at.logic.gapt.grammars

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ FOLSubTerms, Utils, FOLMatchingAlgorithm }
import at.logic.gapt.expr.hol.lcomp
import at.logic.gapt.expr.hol.simplify
import at.logic.gapt.expr.hol.toNNF
import at.logic.gapt.provers.maxsat.{ MaxSATSolver, MaxSat4j }
import at.logic.gapt.utils.dssupport.ListSupport
import at.logic.gapt.utils.logging.metrics

import scala.collection.{ GenTraversable, Set, mutable }

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
  def apply( lang: GenTraversable[FOLTerm], nonTerminals: Seq[FOLVar] ): Seq[FOLTerm] = {
    lang foreach { term => require( freeVariables( term ) isEmpty ) }

    val antiUnifiers = ListSupport.boundedPower( lang toList, nonTerminals.size + 1 ).
      map( antiUnificator( _ ) ).toSet[FOLTerm]
    antiUnifiers.flatMap { au => nfsSubsumedByAU( au, nonTerminals.toSet ) }.toSeq
  }
}

class TermGenerationFormula( g: VectTratGrammar, t: FOLTerm ) {
  import VectTratGrammar._

  def vectProductionIsIncluded( p: Production ): FOLFormula = FOLAtom( s"$p" )
  def valueOfNonTerminal( n: FOLVar, value: FOLTerm ): FOLFormula = FOLAtom( s"$n=$value" )

  def formula: FOLFormula = {
    val cs = List.newBuilder[FOLFormula]

    val Omega = rename( FOLConst( "Ω" ), constants( t ).toList )

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
          if ( !( alreadyHandledAssignments contains ( containingNonTerminalVect -> assignment ) )
            && assignment.exists( _ != Omega ) )
            cs += Imp(
              And( containingNonTerminalVect.zip( assignment ) map { case ( nt, value ) => valueOfNonTerminal( nt, value ) } ),
              Or( g.productions( containingNonTerminalVect ) map {
                case p @ ( _, rhss ) =>
                  And( containingNonTerminalVect.zip( assignment ).zip( rhss ) map {
                    case ( ( nt, value ), rhs ) if value == Omega => Top()
                    case ( ( nt, value ), rhs ) =>
                      FOLMatchingAlgorithm.matchTerms( rhs, value ) match {
                        case Some( matching ) =>
                          And(
                            vectProductionIsIncluded( p ),
                            And( matching.folmap map {
                              case ( v, smallerValue: FOLTerm ) =>
                                singleVariableAssignmentsToHandle enqueue ( v -> smallerValue )
                                valueOfNonTerminal( v, smallerValue )
                            } toList )
                          )
                        case None => Bottom()
                      }
                  } )
              } toList )
            )

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

object normalFormsProofGrammar {
  def apply( lang: Seq[FOLTerm], n: Int ) = {
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
  def apply( g: TratGrammar, lang: Seq[FOLTerm], maxSATSolver: MaxSATSolver = new MaxSat4j ): TratGrammar = {
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
  def apply( lang: Seq[FOLTerm], numberOfNonTerminals: Int, maxSATSolver: MaxSATSolver = new MaxSat4j ) = {
    val polynomialSizedCoveringGrammar = normalFormsProofGrammar( lang, numberOfNonTerminals )
    minimizeGrammar( polynomialSizedCoveringGrammar, lang, maxSATSolver )
  }
}

object takeN {
  def apply[A]( n: Int, from: Seq[A] ): Seq[List[A]] = n match {
    case 0 => Seq( Nil )
    case _ =>
      takeN( n - 1, from ) flatMap { rest =>
        from.map( _ :: rest )
      }
  }
}

object normalFormsProofVectGrammar {
  import VectTratGrammar._

  def apply( lang: Seq[FOLTerm], arities: Seq[Int] ): VectTratGrammar = {
    val rhsNonTerminals = arities.zipWithIndex map { case ( arity, i ) => ( 0 until arity ).map( j => FOLVar( s"α_${i}_$j" ) ).toList }
    apply( lang, FOLVar( "τ" ), rhsNonTerminals )
  }

  def apply( lang: Seq[FOLTerm], axiom: FOLVar, nonTermVects: Seq[NonTerminalVect] ): VectTratGrammar = {
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
  def apply( g: VectTratGrammar, lang: Seq[FOLTerm], maxSATSolver: MaxSATSolver = new MaxSat4j ): VectTratGrammar = {
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
  def apply( lang: Seq[FOLTerm], aritiesOfNonTerminals: Seq[Int], maxSATSolver: MaxSATSolver = new MaxSat4j ) = {
    val polynomialSizedCoveringGrammar = metrics.time( "nfgrammar" ) { normalFormsProofVectGrammar( lang, aritiesOfNonTerminals ) }
    metrics.value( "nfgrammar", polynomialSizedCoveringGrammar.size )
    minimizeVectGrammar( polynomialSizedCoveringGrammar, lang, maxSATSolver )
  }
}
