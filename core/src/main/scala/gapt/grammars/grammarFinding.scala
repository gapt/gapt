package gapt.grammars

import gapt.expr._
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Formula
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.fol.flatSubterms
import gapt.expr.formula.fol.thresholds._
import gapt.expr.formula.hol.{ atoms, lcomp }
import gapt.expr.subst.PreSubstitution
import gapt.expr.ty.TBase
import gapt.expr.ty.Ti
import gapt.expr.util.LambdaPosition
import gapt.expr.util.constants
import gapt.expr.util.expressionSize
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.expr.util.syntacticMatching
import gapt.logic.hol.simplify
import gapt.logic.hol.toNNF
import gapt.provers.maxsat.{ MaxSATSolver, bestAvailableMaxSatSolver }
import gapt.utils.{ Logger, UNone, UOption, USome }

import scala.collection.{ Iterable, mutable }

object subsetLGGs {
  def apply( terms: Iterable[Expr], maxSize: Int ): Set[Expr] = {
    val lggs = Set.newBuilder[Expr]

    def findLGGs( currentLGG: UOption[Expr], terms: List[Expr], maxSize: Int ): Unit =
      if ( maxSize > 0 && terms.nonEmpty ) {
        val t :: rest = terms

        val newLGG = currentLGG match {
          case USome( lgg ) => leastGeneralGeneralization.fast( lgg, t )._1
          case _            => t
        }
        lggs += newLGG
        if ( !newLGG.isInstanceOf[Var] ) findLGGs( USome( newLGG ), rest, maxSize - 1 )

        findLGGs( currentLGG, rest, maxSize )
      }

    findLGGs( UNone(), terms.toList, maxSize )

    lggs.result()
  }
}

object stsSubsumedByLGG {
  def apply( lgg: Expr, nts: Set[Var] ): Set[Expr] = apply( lgg, nts, nts,
    LambdaPosition.filterPositions( _.ty.isInstanceOf[TBase] )( lgg ).
      groupBy( lgg( _ ) ).toList.
      sortBy { case ( st, _ ) => expressionSize( st ) }.
      map( _._2 ) )

  private def apply( lgg: Expr, ntsToDo: Set[Var], nts: Set[Var], allPositions: List[List[LambdaPosition]] ): Set[Expr] = allPositions match {
    case positions :: otherPositions =>
      positions.flatMap { lgg.get( _ ) }.headOption.
        filterNot( freeVariables( _ ) subsetOf nts ).
        map { st =>
          ntsToDo filter { _.ty == st.ty } flatMap { nt =>
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
  def apply( lang: Iterable[FOLTerm], nonTerminals: Seq[FOLVar] )( implicit dummyImplicit: DummyImplicit ): Set[FOLTerm] =
    apply( lang: Iterable[Expr], nonTerminals ).map( _.asInstanceOf[FOLTerm] )

  def apply( lang: Iterable[Expr], nonTerminals: Seq[Var] ): Set[Expr] = {
    val lggs = subsetLGGs( lang, nonTerminals.size + 1 )
    lggs flatMap { stsSubsumedByLGG( _, nonTerminals.toSet ) }
  }
}

class VtratgTermGenerationFormula( g: VTRATG, t: Expr ) {
  import VTRATG._

  def vectProductionIsIncluded( p: Production ) = Atom( "prodinc", p._1 ++ p._2 )
  def valueOfNonTerminal( n: Var, value: Expr ) = Atom( "ntval", n, value )

  def formula: Formula = {
    val notASubTerm = rename( FOLConst( "∞" ), constants( t ) )

    // we try not generate the formulas for all subterms, but only for those which are needed
    val possibleAssignments = mutable.Set[( Int, List[Expr] )]()
    val containingNTIdx = g.nonTerminals.zipWithIndex.flatMap { case ( ns, i ) => ns map { _ -> i } }.toMap
    val handledPAs = mutable.Set[Map[Var, Expr]]()
    def discoverAssignments( pa: Map[Var, Expr] ): Unit =
      if ( pa.nonEmpty && !handledPAs.contains( pa ) ) {
        val lowestNTVectIdx = pa.keys.map( containingNTIdx ).min
        val lowestNTVect = g.nonTerminals( lowestNTVectIdx )
        g.productions( lowestNTVect ) foreach { p =>
          val pairs = for ( ( nt, s ) <- p._1.lazyZip( p._2 ); t <- pa.get( nt ) ) yield s -> t
          syntacticMatching( pairs.toList, PreSubstitution( pa ) ) foreach { matching =>
            discoverAssignments( matching.map -- lowestNTVect )
          }
        }
        possibleAssignments += ( lowestNTVectIdx -> lowestNTVect.map { pa.getOrElse( _, notASubTerm ) } )
        handledPAs += pa
      }
    for ( ( ntv, i ) <- g.nonTerminals.zipWithIndex ) possibleAssignments += ( i -> ntv.map { _ => notASubTerm } )
    discoverAssignments( Map( g.startSymbol -> t ) )
    val possibleValues = Map() ++ handledPAs.toSet.flatten.groupBy( _._1 ).view.mapValues( _.map( _._2 ) ).toMap

    def Match( ntIdx: Int, t: List[Expr], s: List[Expr] ) =
      syntacticMatching( s zip t filter { _._2 != notASubTerm } ) match {
        case Some( matching ) =>
          And( matching.map.toSeq map {
            case ( beta, r ) if possibleValues( beta ) contains r =>
              valueOfNonTerminal( beta, r )
            case _ => Bottom()
          } )
        case None => Bottom()
      }

    def Case( ntIdx: Int, t: List[Expr] ) =
      if ( t forall { _ == notASubTerm } ) Top()
      else And( ( g.nonTerminals( ntIdx ).lazyZip( t ) ).map( valueOfNonTerminal ) ) --> Or( g.productions( g.nonTerminals( ntIdx ) ).toSeq map {
        case p @ ( _, s ) =>
          vectProductionIsIncluded( p ) & Match( ntIdx, t, s )
      } )

    val cs = Seq.newBuilder[Formula]

    // value of startSymbol must be t
    cs += valueOfNonTerminal( g.startSymbol, t )

    possibleAssignments foreach { assignment =>
      cs += simplify( Case( assignment._1, assignment._2 ) )
    }

    for ( ( x, ts ) <- possibleValues )
      cs += atMost oneOf ( ts + notASubTerm ).toSeq.map { valueOfNonTerminal( x, _ ) }

    for ( ( i, assignments ) <- possibleAssignments groupBy { _._1 } )
      cs += exactly oneOf ( assignments.toSeq map { assignment => And( g.nonTerminals( i ).lazyZip( assignment._2 ).map( valueOfNonTerminal ) ) } )

    And( cs.result() )
  }
}

class VectGrammarMinimizationFormula( g: VTRATG ) {
  import VTRATG._

  def productionIsIncluded( p: Production ) = Atom( "prodinc", p._1 ++ p._2 )
  def valueOfNonTerminal( t: Expr, n: Var, rest: Expr ) = Atom( "ntval", t, n, rest )

  def generatesTerm( t: Expr ) = new VtratgTermGenerationFormula( g, t ) {
    override def vectProductionIsIncluded( p: Production ) =
      VectGrammarMinimizationFormula.this.productionIsIncluded( p )
    override def valueOfNonTerminal( n: Var, value: Expr ) =
      VectGrammarMinimizationFormula.this.valueOfNonTerminal( t, n, value )
  }.formula

  def coversLanguage( lang: Iterable[Expr] ) = And( lang map generatesTerm )
}

object stableVTRATG {
  import VTRATG._

  def apply( lang: Set[Expr], arities: VtratgParameter ): VTRATG = {
    val termType = lang.headOption.map( _.ty ).getOrElse( Ti )
    val rhsNonTerminals =
      for ( ( tys, i ) <- arities.nonTerminalTypes.zipWithIndex )
        yield for ( ( ty, j ) <- tys.toList.zipWithIndex )
        yield Var( if ( tys.size <= 1 ) s"x_${i + 1}" else s"x_${i + 1}_$j", ty )
    apply( lang, Var( "x_0", termType ), rhsNonTerminals )
  }

  def apply( lang: Set[Expr], startSymbol: Var, nonTermVects: Seq[NonTerminalVect] ): VTRATG = {
    val subTermsPerType = flatSubterms( lang ).groupBy( _.ty )
    val startSymbolNFs = stableTerms( lang, nonTermVects flatten )
    val argumentNFsPerType = nonTermVects.flatten.map( _.ty ).distinct.map { t =>
      t -> stableTerms( subTermsPerType( t ), nonTermVects.tail.flatten )
    }.toMap

    import cats.syntax.all._, cats.instances.all._

    VTRATG( startSymbol, List( startSymbol ) +: nonTermVects,
      startSymbolNFs.map( List( startSymbol ) -> List( _ ) ) ++
        nonTermVects.zipWithIndex.flatMap {
          case ( a, i ) =>
            val allowedNonTerms = nonTermVects.drop( i + 1 ).flatten.toSet
            a.traverse( v => argumentNFsPerType( v.ty ).view.filter( freeVariables( _ ).subsetOf( allowedNonTerms ) ).toList ).map( a -> _ )
        } )
  }
}

object minimizeVTRATG {
  val logger = Logger( "minimizeVTRATG" )

  def apply( g: VTRATG, lang: Set[Expr], maxSATSolver: MaxSATSolver = bestAvailableMaxSatSolver,
             weight: VTRATG.Production => Int = _ => 1 ): VTRATG = {
    val formula = new VectGrammarMinimizationFormula( g )
    val hard = logger.time( "minform" ) { formula.coversLanguage( lang ) }
    logger.metric( "minform_lcomp", lcomp( simplify( toNNF( hard ) ) ) )
    val atomsInHard = atoms( hard )
    val soft = for {
      p <- g.productions
      atom = formula productionIsIncluded p
      if atomsInHard contains atom
    } yield -atom -> weight( p )
    logger.time( "maxsat" ) { maxSATSolver.solve( hard, soft ) } match {
      case Some( interp ) => VTRATG( g.startSymbol, g.nonTerminals,
        g.productions.filter { p => interp( formula.productionIsIncluded( p ) ) } )
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
  val logger = minimizeVTRATG.logger

  def apply( lang: Set[Expr], aritiesOfNonTerminals: VtratgParameter,
             maxSATSolver: MaxSATSolver             = bestAvailableMaxSatSolver,
             weight:       VTRATG.Production => Int = _ => 1 ) = {
    val polynomialSizedCoveringGrammar = logger.time( "stabgrammar" ) { stableVTRATG( lang, aritiesOfNonTerminals ) }
    logger.metric( "stabgrammar", polynomialSizedCoveringGrammar.size )
    minimizeVTRATG( polynomialSizedCoveringGrammar, lang, maxSATSolver, weight )
  }
}
