package at.logic.gapt.grammars.deltatable

import at.logic.gapt.cutintro.DeltaTableMethod
import at.logic.gapt.expr._
import at.logic.gapt.grammars.{ findMinimalVectGrammar, VectTratGrammar, antiUnifier }

import scala.collection.mutable

object deltaTable {
  type Row = Set[( LambdaExpression, Set[LambdaExpression] )]

  def createTable( termSet: Set[LambdaExpression], maxArity: Option[Int] = None ): Map[Set[Substitution], Row] = {
    // invariant:
    // deltatable(S) contains (u, T) ==> u S = T && |S| = |T|
    val deltatable = mutable.Map[Set[Substitution], Row]().withDefaultValue( Set() )

    deltatable( Set( Substitution() ) ) = for ( t <- termSet ) yield t -> Set( t )

    for ( i <- 1 until termSet.size ) {
      for ( ( s, decomps ) <- deltatable.toMap; ( u, terms ) <- decomps if terms.size == i ) {
        for ( t <- termSet.toSet diff terms ) {
          val terms_ = terms + t
          val u_ = antiUnifier( terms_.toSeq )
          if ( !u_.isInstanceOf[Var] && maxArity.forall { freeVariables( u_ ).size <= _ } ) {
            val s_ = for ( t_ <- terms_ ) yield syntacticMatching( u_, t_ ).get

            require( s_.map { _( u_ ) } == terms_ )

            deltatable( s_ ) = deltatable( s_ ) + ( u_ -> terms_ )
          }
        }
      }

      subsumptionRemoval( deltatable )
    }

    deltatable.toMap
  }

  def keySubsumption( a: Set[Substitution], b: Set[Substitution] ): Set[Map[Var, Var]] =
    keySubsumption( a map { _.map }, b map { _.map }, Map() )

  def keySubsumption[K1, K2, V]( a: Set[Map[K1, V]], b: Set[Map[K2, V]], alreadyFixed: Map[K1, K2] ): Set[Map[K1, K2]] = {
    if ( a.size > b.size ) return Set()
    if ( a.head.size > b.head.size ) return Set()

    val nextKs = a.head.keySet diff alreadyFixed.keySet
    if ( nextKs isEmpty ) return Set( alreadyFixed )

    val chosenK = nextKs.head
    val chosenV = a.head( chosenK )

    for {
      ( corrK, `chosenV` ) <- b.flatten
      newAlreadyFixed = alreadyFixed + ( chosenK -> corrK )
      if a.map { _ filterKeys newAlreadyFixed.keySet } subsetOf b.map { newAlreadyFixed mapValues _ }
      solution <- keySubsumption( a, b, newAlreadyFixed )
    } yield solution
  }

  def subsumptionRemoval( table: mutable.Map[Set[Substitution], Row] ): Unit = {
    val max = table.keys.map { _.size }.max
    for {
      k1 <- table.keySet
      if k1.size == max
      if table contains k1
      ( k2, r2 ) <- table
      if k2.size >= max - 1
      if k1 != k2
      varMap <- keySubsumption( k2, k1 ).take( 1 )
    } {
      val subst = Substitution( varMap )
      table( k1 ) = table( k1 ) union ( r2 map { case ( u, ts ) => subst( u ) -> ts } )
      if ( k1.size == k2.size && k1.head.map.size == k2.head.map.size ) table -= k2 // varMap is a bijection
    }

    // merge inside rows
    for ( ( k, r ) <- table ) table( k ) = r.groupBy { _._1 }.mapValues { _.flatMap { _._2 } }.toSet
  }

  def findGrammarFromDeltaTable( termSet: Set[LambdaExpression], deltatable: Map[Set[Substitution], Row] ): ( Set[LambdaExpression], Set[Substitution] ) = {
    var minSize = termSet.size

    val allGrammars = for ( ( s, decomps ) <- deltatable.toSeq ) yield {
      val missingTerms = termSet diff ( decomps flatMap { _._2 } )
      val patchedDecomps = decomps union ( missingTerms map { t => t -> Set( t ) } )

      def minimizeGrammar( termSet: Set[LambdaExpression], grammar: Row, alreadyIncluded: Row ): Option[Row] =
        if ( termSet isEmpty ) {
          minSize = math.min( alreadyIncluded.size + s.size, minSize )
          Some( alreadyIncluded )
        } else if ( alreadyIncluded.size + s.size >= minSize ) {
          None
        } else if ( grammar isEmpty ) {
          throw new IllegalArgumentException
        } else {
          val focus = grammar minBy { _._2.size }
          if ( grammar exists { sg => focus._2.subsetOf( sg._2 ) && focus._2 != sg._2 } )
            return minimizeGrammar( termSet, grammar - focus, alreadyIncluded )
          val isInc = minimizeGrammar( termSet diff focus._2, grammar - focus, alreadyIncluded + focus )
          val restLang = grammar - focus flatMap { _._2 }
          if ( termSet subsetOf restLang ) {
            val isNotInc = minimizeGrammar( termSet, grammar - focus, alreadyIncluded )
            val possibilities = Seq( isInc, isNotInc ).flatten
            if ( possibilities.isEmpty ) None else Some( possibilities minBy { _.size } )
          } else {
            isInc
          }
        }
      val minDecomps = minimizeGrammar( termSet, patchedDecomps, Set() )

      minDecomps.map { _.map { _._1 } -> s }
    }

    allGrammars.flatten minBy { g => g._1.size + g._2.size }
  }

  def grammarToVTRATG( us: Set[LambdaExpression], s: Set[Substitution] ): VectTratGrammar = {
    val alpha = freeVariables( us ).toList.sortBy { _.toString }.asInstanceOf[List[FOLVar]]
    val tau = rename( FOLVar( "tau" ), alpha )
    VectTratGrammar( tau, Seq( List( tau ), alpha ),
      ( for ( subst <- s ) yield alpha -> alpha.map { subst( _ ).asInstanceOf[FOLTerm] } )
        union ( for ( u <- us ) yield List( tau ) -> List( u.asInstanceOf[FOLTerm] ) ) )
  }

  def main( args: Array[String] ) = {
    //    val n = 9
    //    val terms = for (i <- 0 to n) yield FOLFunction("f", Numeral(i))

    //    val terms = FOLInstanceTermEncoding( SquareEdges2DimExampleProof( 10 ) )._1

    def iter( suc: String, zero: String )( i: Int ): FOLTerm =
      if ( i == 0 ) FOLConst( zero ) else FOLFunction( suc, iter( suc, zero )( i - 1 ) )
    val n = 9
    val terms1 = 0 until n map iter( "f", "c" ) map { FOLFunction( "r", _ ) }
    val terms2 = 0 until n map iter( "g", "d" ) map { FOLFunction( "s", _ ) }
    val terms = terms1 ++ terms2

    val deltatable = createTable( terms.toSet )

    val actualMinGrammar = findMinimalVectGrammar( terms.toSet, Seq( 1 ) )

    val origDTableGrammar = DeltaTableMethod( false ).findGrammars( terms.toSet ).get

    val ( us, s ) = findGrammarFromDeltaTable( terms.toSet, deltatable )
    val vtratg = grammarToVTRATG( us, s )
    println( deltatable )
    println( vtratg )
  }
}