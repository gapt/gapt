package at.logic.gapt.grammars

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.folSubTerms
import at.logic.gapt.expr.fol.thresholds._
import at.logic.gapt.expr.hol.{ atoms, lcomp, simplify, toNNF }
import at.logic.gapt.provers.maxsat.{ MaxSATSolver, bestAvailableMaxSatSolver }
import at.logic.gapt.utils.metrics

import scala.collection.{ GenTraversable, mutable }

object subsetLGGs {
  def apply( terms: Traversable[LambdaExpression], maxSize: Int ): Set[LambdaExpression] = {
    val lggs = Set.newBuilder[LambdaExpression]

    def findLGGs( currentLGG: LambdaExpression, terms: List[LambdaExpression], maxSize: Int ): Unit =
      if ( maxSize > 0 && terms.nonEmpty ) {
        val ( t :: rest ) = terms

        val newLGG = if ( currentLGG == null ) t else leastGeneralGeneralization.fast( currentLGG, t )._1
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

class VtratgTermGenerationFormula( g: VTRATG, t: LambdaExpression ) {
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
    discoverAssignments( Map( g.startSymbol -> t ) )
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

    // value of startSymbol must be t
    cs += valueOfNonTerminal( g.startSymbol, t )

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

  def generatesTerm( t: LambdaExpression ) = new VtratgTermGenerationFormula( g, t ) {
    override def vectProductionIsIncluded( p: Production ) =
      VectGrammarMinimizationFormula.this.productionIsIncluded( p )
    override def valueOfNonTerminal( n: Var, value: LambdaExpression ) =
      VectGrammarMinimizationFormula.this.valueOfNonTerminal( t, n, value )
  }.formula

  def coversLanguage( lang: Traversable[LambdaExpression] ) = And( lang map generatesTerm )
}

object stableVTRATG {
  import VTRATG._

  def apply( lang: Set[LambdaExpression], arities: VtratgParameter ): VTRATG = {
    val termType = lang.headOption.map( _.exptype ).getOrElse( Ti )
    val rhsNonTerminals =
      for ( ( tys, i ) <- arities.nonTerminalTypes.zipWithIndex )
        yield for ( ( ty, j ) <- tys.toList.zipWithIndex )
        yield Var( if ( tys.size <= 1 ) s"x_${i + 1}" else s"x_${i + 1}_$j", ty )
    apply( lang, Var( "x_0", termType ), rhsNonTerminals )
  }

  def apply( lang: Set[LambdaExpression], startSymbol: Var, nonTermVects: Seq[NonTerminalVect] ): VTRATG = {
    val subTermsPerType = folSubTerms( lang ).groupBy( _.exptype )
    val startSymbolNFs = stableTerms( lang, nonTermVects flatten )
    val argumentNFsPerType = nonTermVects.flatten.map( _.exptype ).distinct.map { t =>
      t -> stableTerms( subTermsPerType( t ), nonTermVects.tail.flatten )
    }.toMap

    import cats.syntax.all._, cats.instances.all._

    VTRATG( startSymbol, List( startSymbol ) +: nonTermVects,
      startSymbolNFs.map( List( startSymbol ) -> List( _ ) ) ++
        nonTermVects.zipWithIndex.flatMap {
          case ( a, i ) =>
            val allowedNonTerms = nonTermVects.drop( i + 1 ).flatten.toSet
            a.traverse( v => argumentNFsPerType( v.exptype ).view.filter( freeVariables( _ ).subsetOf( allowedNonTerms ) ).toList ).map( a -> _ )
        } )
  }
}

object minimizeVTRATG {
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
      case Some( interp ) => VTRATG( g.startSymbol, g.nonTerminals,
        g.productions filter { p => interp.interpret( formula.productionIsIncluded( p ) ) } )
      case None => throw new Exception( "Grammar does not cover language." )
    }
  }
}

case class VtratgParameter( nonTerminalTypes: Seq[Seq[TBase]] )
object VtratgParameter {
  implicit def forFolTratg( numberNonTerminals: Int ): VtratgParameter =
    ( 1 to numberNonTerminals ).map( _ => 1 )
  implicit def forFolVtratg( vectorArities: Seq[Int] ): VtratgParameter =
    vectorArities.map( i => ( 1 to i ).map( _ => Ti ) )
  implicit def forManySortedTratg( nonTerminalTypes: Seq[TBase] ): VtratgParameter =
    nonTerminalTypes.map( Seq( _ ) )
  implicit def forManySortedVtratg( nonTerminalTypeVectors: Seq[Seq[TBase]] ): VtratgParameter =
    VtratgParameter( nonTerminalTypeVectors )
}

object findMinimalVTRATG {
  def apply( lang: Set[LambdaExpression], aritiesOfNonTerminals: VtratgParameter,
             maxSATSolver: MaxSATSolver             = bestAvailableMaxSatSolver,
             weight:       VTRATG.Production => Int = _ => 1 ) = {
    val polynomialSizedCoveringGrammar = metrics.time( "stabgrammar" ) { stableVTRATG( lang, aritiesOfNonTerminals ) }
    metrics.value( "stabgrammar", polynomialSizedCoveringGrammar.size )
    minimizeVTRATG( polynomialSizedCoveringGrammar, lang, maxSATSolver, weight )
  }
}
