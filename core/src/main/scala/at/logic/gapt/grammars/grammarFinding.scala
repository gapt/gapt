package at.logic.gapt.grammars

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubTerms
import at.logic.gapt.expr.fol.thresholds._
import at.logic.gapt.expr.hol.{ atoms, lcomp, simplify, toNNF }
import at.logic.gapt.provers.maxsat.{ MaxSATSolver, bestAvailableMaxSatSolver }
import at.logic.gapt.utils.ListSupport
import at.logic.gapt.utils.logging.metrics

import scala.collection.{ GenTraversable, mutable }

object subsetLGGs {
  def apply( terms: Traversable[LambdaExpression], maxSize: Int ): Set[LambdaExpression] = {
    val lggs = Set.newBuilder[LambdaExpression]

    def findLGGs( currentLGG: LambdaExpression, terms: List[LambdaExpression], maxSize: Int ): Unit =
      if ( maxSize > 0 && terms.nonEmpty ) {
        val ( t :: rest ) = terms

        val newLGG = if ( currentLGG == null ) t else leastGeneralGeneralization( currentLGG, t )._1
        lggs += newLGG
        if ( !newLGG.isInstanceOf[Var] ) findLGGs( newLGG, rest, maxSize - 1 )

        findLGGs( currentLGG, rest, maxSize )
      }

    findLGGs( null, terms.toList, maxSize )

    lggs.result()
  }
}

object stsSubsumedByLGG {
  def apply( lgg: LambdaExpression, nts: Set[Var] ): Set[LambdaExpression] = apply( lgg, nts, nts,
    LambdaPosition.getPositions( lgg, _.exptype.isInstanceOf[TBase] ).
      groupBy( lgg( _ ) ).toList.
      sortBy { case ( st, _ ) => expressionSize( st ) }.
      map( _._2 ) )

  private def apply( lgg: LambdaExpression, ntsToDo: Set[Var], nts: Set[Var], allPositions: List[List[LambdaPosition]] ): Set[LambdaExpression] = allPositions match {
    case positions :: otherPositions =>
      positions.flatMap { lgg.get( _ ) }.headOption.
        filterNot( freeVariables( _ ) subsetOf nts ).
        map { st =>
          ntsToDo filter { _.exptype == st.exptype } flatMap { nt =>
            var generalization = lgg
            for ( pos <- positions ) generalization = generalization.replace( pos, nt )
            apply( generalization, ntsToDo - nt, nts, otherPositions )
          }
        }.getOrElse( Set() ) ++ apply( lgg, ntsToDo, nts, otherPositions )
    case Nil if freeVariables( lgg ) subsetOf nts => Set( lgg )
    case _                                        => Set()
  }
}

object stableTerms {
  def apply( lang: Traversable[FOLTerm], nonTerminals: Seq[FOLVar] )( implicit dummyImplicit: DummyImplicit ): Set[FOLTerm] =
    apply( lang: Traversable[LambdaExpression], nonTerminals ).map( _.asInstanceOf[FOLTerm] )

  def apply( lang: Traversable[LambdaExpression], nonTerminals: Seq[Var] ): Set[LambdaExpression] = {
    val lggs = subsetLGGs( lang, nonTerminals.size + 1 )
    lggs flatMap { stsSubsumedByLGG( _, nonTerminals.toSet ) }
  }
}

class TermGenerationFormula( g: VTRATG, t: LambdaExpression ) {
  import VTRATG._

  def vectProductionIsIncluded( p: Production ) = HOLAtom( "prodinc", p._1 ++ p._2 )
  def valueOfNonTerminal( n: Var, value: LambdaExpression ) = HOLAtom( "ntval", n, value )

  def formula: HOLFormula = {
    val notASubTerm = rename( FOLConst( "⊥" ), constants( t ) )

    // we try not generate the formulas for all subterms, but only for those which are needed
    val possibleAssignments = mutable.Set[( Int, List[LambdaExpression] )]()
    val containingNTIdx = g.nonTerminals.zipWithIndex.flatMap { case ( ns, i ) => ns map { _ -> i } }.toMap
    val handledPAs = mutable.Set[Map[Var, LambdaExpression]]()
    def discoverAssignments( pa: Map[Var, LambdaExpression] ): Unit =
      if ( pa.nonEmpty && !handledPAs.contains( pa ) ) {
        val lowestNTVectIdx = pa.keys.map( containingNTIdx ).min
        val lowestNTVect = g.nonTerminals( lowestNTVectIdx )
        g.productions( lowestNTVect ) foreach { p =>
          val pairs = for ( ( nt, s ) <- p.zipped; t <- pa.get( nt ) ) yield s -> t
          syntacticMatching( pairs toList, pa ) foreach { matching =>
            discoverAssignments( matching.map -- lowestNTVect )
          }
        }
        possibleAssignments += ( lowestNTVectIdx -> lowestNTVect.map { pa.getOrElse( _, notASubTerm ) } )
        handledPAs += pa
      }
    for ( ( ntv, i ) <- g.nonTerminals.zipWithIndex ) possibleAssignments += ( i -> ntv.map { _ => notASubTerm } )
    discoverAssignments( Map( g.axiom -> t ) )
    val possibleValues = Map() ++ handledPAs.toSet.flatten.groupBy( _._1 ).mapValues( _.map( _._2 ) )

    def Match( ntIdx: Int, t: List[LambdaExpression], s: List[LambdaExpression] ) =
      syntacticMatching( s zip t filter { _._2 != notASubTerm } ) match {
        case Some( matching ) =>
          And( matching.map.toSeq map {
            case ( beta, r ) if possibleValues( beta ) contains r =>
              valueOfNonTerminal( beta, r )
            case _ => Bottom()
          } )
        case None => Bottom()
      }

    def Case( ntIdx: Int, t: List[LambdaExpression] ) =
      if ( t forall { _ == notASubTerm } ) Top()
      else And( ( g.nonTerminals( ntIdx ), t ).zipped map valueOfNonTerminal ) --> Or( g.productions( g.nonTerminals( ntIdx ) ).toSeq map {
        case p @ ( _, s ) =>
          vectProductionIsIncluded( p ) & Match( ntIdx, t, s )
      } )

    val cs = Seq.newBuilder[HOLFormula]

    // value of axiom must be t
    cs += valueOfNonTerminal( g.axiom, t )

    possibleAssignments foreach { assignment =>
      cs += simplify( Case( assignment._1, assignment._2 ) )
    }

    for ( ( x, ts ) <- possibleValues )
      cs += atMost oneOf ( ts + notASubTerm ).toSeq.map { valueOfNonTerminal( x, _ ) }

    for ( ( i, assignments ) <- possibleAssignments groupBy { _._1 } )
      cs += exactly oneOf ( assignments.toSeq map { assignment => And( ( g.nonTerminals( i ), assignment._2 ).zipped map valueOfNonTerminal ) } )

    And( cs.result() )
  }
}

class VectGrammarMinimizationFormula( g: VTRATG ) {
  import VTRATG._

  def productionIsIncluded( p: Production ) = HOLAtom( "prodinc", p._1 ++ p._2 )
  def valueOfNonTerminal( t: LambdaExpression, n: Var, rest: LambdaExpression ) = HOLAtom( "ntval", t, n, rest )

  def generatesTerm( t: LambdaExpression ) = new TermGenerationFormula( g, t ) {
    override def vectProductionIsIncluded( p: Production ) =
      VectGrammarMinimizationFormula.this.productionIsIncluded( p )
    override def valueOfNonTerminal( n: Var, value: LambdaExpression ) =
      VectGrammarMinimizationFormula.this.valueOfNonTerminal( t, n, value )
  }.formula

  def coversLanguage( lang: Traversable[LambdaExpression] ) = And( lang map generatesTerm )
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

object stableProofVectGrammar {
  import VTRATG._

  def apply( lang: Set[FOLTerm], arities: Seq[Int] ): VTRATG = {
    val rhsNonTerminals = arities.zipWithIndex map {
      case ( arity, i ) =>
        ( 0 until arity ).map( j => FOLVar( s"x_${i}_$j" ) ).toList
    }
    apply( lang, FOLVar( "x0" ), rhsNonTerminals )
  }

  def apply( lang: Set[FOLTerm], axiom: FOLVar, nonTermVects: Seq[NonTerminalVect] ): VTRATG = {
    val topLevelNFs = stableTerms( lang, nonTermVects flatten ).filter( !_.isInstanceOf[FOLVar] )
    val argumentNFs = stableTerms( FOLSubTerms( lang flatMap { case FOLFunction( _, as ) => as } ), nonTermVects.tail flatten )

    VTRATG( axiom, List( axiom ) +: nonTermVects,
      topLevelNFs.map( List( axiom ) -> List( _ ) ) ++
        nonTermVects.zipWithIndex.flatMap {
          case ( a, i ) =>
            val allowedNonTerms = nonTermVects.drop( i + 1 ).flatten.toSet
            val allowedRHS = argumentNFs filter { st => freeVariables( st ) subsetOf allowedNonTerms }
            takeN( a.size, allowedRHS ).map( a -> _ )
        } )
  }
}

object minimizeVectGrammar {
  def apply( g: VTRATG, lang: Set[LambdaExpression], maxSATSolver: MaxSATSolver = bestAvailableMaxSatSolver,
             weight: VTRATG.Production => Int = _ => 1 ): VTRATG = {
    val formula = new VectGrammarMinimizationFormula( g )
    val hard = metrics.time( "minform" ) { formula.coversLanguage( lang ) }
    metrics.value( "minform_lcomp", lcomp( simplify( toNNF( hard ) ) ) )
    val atomsInHard = atoms( hard )
    val soft = for {
      p <- g.productions
      atom = formula productionIsIncluded p
      if atomsInHard contains atom
    } yield -atom -> weight( p )
    metrics.time( "maxsat" ) { maxSATSolver.solve( hard, soft ) } match {
      case Some( interp ) => VTRATG( g.axiom, g.nonTerminals,
        g.productions filter { p => interp.interpret( formula.productionIsIncluded( p ) ) } )
      case None => throw new Exception( "Grammar does not cover language." )
    }
  }
}

object findMinimalVectGrammar {
  def apply( lang: Set[FOLTerm], aritiesOfNonTerminals: Seq[Int],
             maxSATSolver: MaxSATSolver             = bestAvailableMaxSatSolver,
             weight:       VTRATG.Production => Int = _ => 1 ) = {
    val polynomialSizedCoveringGrammar = metrics.time( "stabgrammar" ) { stableProofVectGrammar( lang.toSet, aritiesOfNonTerminals ) }
    metrics.value( "stabgrammar", polynomialSizedCoveringGrammar.size )
    minimizeVectGrammar( polynomialSizedCoveringGrammar, lang.toSet, maxSATSolver, weight )
  }
}
