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

    for ( i <- 1 until termSet.size if maxArity forall { i <= _ } ) {
      for ( ( s, decomps ) <- deltatable.toMap; ( u, terms ) <- decomps if terms.size == i ) {
        for ( t <- termSet.toSet diff terms ) {
          val terms_ = terms + t
          val u_ = antiUnifier( terms_.toSeq )
          if ( !u_.isInstanceOf[Var] ) {
            val s_ = for ( t_ <- terms_ ) yield syntacticMatching( u_, t_ ).get

            require( s_.map { _( u_ ) } == terms_ )

            deltatable( s_ ) = deltatable( s_ ) + ( u_ -> terms_ )
          }
        }
      }
    }

    deltatable.toMap
  }

  def keySubsumption( a: Set[Substitution], b: Set[Substitution], alreadyFixed: Map[Var, Var] ): Option[Map[Var, Var]] = {
    if ( a forall { _.isIdentity } ) return Some( alreadyFixed )
    ???
  }

  def minimizeGrammar( termSet: Set[LambdaExpression], grammar: Row ): Row =
    if ( termSet isEmpty ) {
      Set()
    } else if ( grammar isEmpty ) {
      throw new IllegalArgumentException
    } else {
      val focus = grammar minBy { _._2.size }
      if ( grammar exists { sg => focus._2.subsetOf( sg._2 ) && focus._2 != sg._2 } )
        return minimizeGrammar( termSet, grammar - focus )
      val isInc = minimizeGrammar( termSet diff focus._2, grammar - focus ) + focus
      val restLang = grammar - focus flatMap { _._2 }
      if ( termSet subsetOf restLang ) {
        val isNotInc = minimizeGrammar( termSet, grammar - focus )
        Seq( isInc, isNotInc ) minBy { _.size }
      } else {
        isInc
      }
    }

  def findGrammarFromDeltaTable( termSet: Set[LambdaExpression], deltatable: Map[Set[Substitution], Row] ): ( Set[LambdaExpression], Set[Substitution] ) = {
    val allGrammars = for ( ( s, decomps ) <- deltatable.toSeq ) yield {
      val missingTerms = termSet diff ( decomps flatMap { _._2 } )
      val patchedDecomps = decomps union ( missingTerms map { t => t -> Set( t ) } )
      val minDecomps = minimizeGrammar( termSet, patchedDecomps )

      minDecomps.map { _._1 } -> s
    }

    val sorted = allGrammars sortBy { g => g._1.size + g._2.size }

    allGrammars minBy { g => g._1.size + g._2.size }
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