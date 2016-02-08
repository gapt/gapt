package at.logic.gapt.grammars.deltatable

import at.logic.gapt.cutintro.{ GrammarFindingMethod, DeltaTableMethod }
import at.logic.gapt.expr._
import at.logic.gapt.grammars.VectTratGrammar
import at.logic.gapt.utils.time

import scala.collection.mutable

object deltaTable {
  type Row = Set[( LambdaExpression, Set[LambdaExpression] )]
  type SimpleGrammar = ( LambdaExpression, Set[Substitution] )

  def antiUnifier( a: LambdaExpression, b: LambdaExpression ): ( LambdaExpression, collection.Map[Var, LambdaExpression], collection.Map[Var, LambdaExpression] ) = {
    val vars = mutable.Map[( LambdaExpression, LambdaExpression ), Var]()
    val subst1 = mutable.Map[Var, LambdaExpression]()
    val subst2 = mutable.Map[Var, LambdaExpression]()

    var i = 0
    def au( a: LambdaExpression, b: LambdaExpression ): LambdaExpression = {
      val Apps( fa, as ) = a
      val Apps( fb, bs ) = b
      if ( fa == fb ) {
        fa( ( as, bs ).zipped map au: _* )
      } else {
        vars.getOrElseUpdate( a -> b, {
          i = i + 1
          val v = Var( s"x$i", a.exptype )
          subst1( v ) = a
          subst2( v ) = b
          v
        } )
      }
    }

    ( au( a, b ), subst1, subst2 )
  }

  def antiUnifier1( a: LambdaExpression, b: LambdaExpression ): ( LambdaExpression, collection.Map[Var, LambdaExpression], collection.Map[Var, LambdaExpression] ) = {
    def au1FromAU( au: LambdaExpression ): ( LambdaExpression, Option[LambdaExpression] ) = au match {
      case Var( _, ty ) => ( Var( "x", ty ), Some( au ) )
      case c: Const     => ( c, None )
      case Apps( f, as ) =>
        val ( as_, s_ ) = as.map( au1FromAU ).unzip
        if ( s_.flatten.distinct.size <= 1 ) {
          f( as_ : _* ) -> s_.flatten.headOption
        } else {
          Var( "x", au.exptype ) -> Some( au )
        }
    }

    val ( au, subst1, subst2 ) = antiUnifier( a, b )
    au1FromAU( au ) match {
      case ( au1, None ) => ( au1, Map(), Map() )
      case ( au1, Some( repl ) ) =>
        val v = freeVariables( au1 ).head
        ( au1, Map( v -> Substitution( subst1 )( repl ) ), Map( v -> Substitution( subst2 )( repl ) ) )
    }
  }

  def antiUnifier1b( a: LambdaExpression, b: LambdaExpression ): ( LambdaExpression, collection.Map[Var, LambdaExpression], collection.Map[Var, LambdaExpression] ) = {
    def au( a: LambdaExpression, b: LambdaExpression ): ( LambdaExpression, Option[( LambdaExpression, LambdaExpression )] ) = {
      val Apps( fa, as ) = a
      val Apps( fb, bs ) = b
      if ( fa == fb ) {
        val ( as_, s_ ) = ( as, bs ).zipped.map( au ).unzip
        if ( s_.flatten.distinct.size <= 1 ) {
          ( fa( as_ : _* ), s_.flatten.headOption )
        } else {
          ( Var( "x", a.exptype ), Some( ( a, b ) ) )
        }
      } else {
        ( Var( "x", a.exptype ), Some( ( a, b ) ) )
      }
    }

    au( a, b ) match {
      case ( au1, None ) => ( au1, Map(), Map() )
      case ( au1, Some( ( substA, substB ) ) ) =>
        val v = freeVariables( au1 ).head
        ( au1, Map( v -> substA ), Map( v -> substB ) )
    }
  }

  def createTable( termSet: Set[LambdaExpression], maxArity: Option[Int] = None ): Map[Set[Substitution], Row] = {
    val termsList = termSet.toBuffer

    // invariant:  deltatable(u,S) == (T,i)  ==>  u S = T  &&  |S| = |T|
    val deltatable = mutable.Map[SimpleGrammar, ( Set[LambdaExpression], Int )]()

    for ( ( t, i ) <- termsList.zipWithIndex )
      deltatable( t -> Set( Substitution() ) ) = Set( t ) -> i

    for ( prevTermsLen <- 1 until termSet.size ) {
      for ( ( ( u, s ), ( terms, lastIndex ) ) <- deltatable.toSeq if terms.size == prevTermsLen ) {
        for ( newIndex <- ( lastIndex + 1 ) until termsList.size; t = termsList( newIndex ) ) {
          val ( u_, substU, substT ) = antiUnifier( u, t )
          if ( !u_.isInstanceOf[Var] && maxArity.forall { substU.size <= _ } ) {
            val s_ = s.map { subst => Substitution( substU mapValues { subst( _ ) } ) } + Substitution( substT )
            val terms_ = terms + t
            deltatable( u_ -> s_ ) = terms_ -> newIndex
          }
        }
      }
    }

    deltatable groupBy { _._1._2 } mapValues { _ map { case ( ( u, s ), ( terms, _ ) ) => u -> terms } toSet }
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

  def tableSubsumption( table: Map[Set[Substitution], Row] ): Map[Set[Substitution], Row] =
    for ( ( s1, row1 ) <- table ) yield if ( s1.head.map.size <= 1 ) s1 -> row1 else {
      var newRow = row1.to[mutable.Set]
      for {
        ( s2, row2 ) <- table
        if s2.head.map.nonEmpty // do not add ground terms
        subs <- keySubsumption( s2, s1 )
        subst = Substitution( subs )
        ( u2, t2 ) <- row2
      } newRow += subst( u2 ) -> t2
      newRow = newRow.groupBy { _._1 }.mapValues { _ flatMap { _._2 } toSet }.to[mutable.Set]
      for {
        e1 @ ( u1, t1 ) <- newRow
        e2 @ ( u2, t2 ) <- newRow
        if newRow contains e1
        if e1 != e2
        if t2 subsetOf t1
      } newRow -= e2
      s1 -> newRow.toSet
    }

  def findGrammarFromDeltaTable( termSet: Set[LambdaExpression], deltatable: Map[Set[Substitution], Row] ): ( Set[LambdaExpression], Set[Substitution] ) = {
    var minSize = termSet.size
    val minGrammars = mutable.Buffer[( Set[LambdaExpression], Set[Substitution] )]()

    def minimizeGrammar(
      termSet:         Set[LambdaExpression],
      grammar:         Row,
      alreadyIncluded: Set[LambdaExpression],
      s:               Set[Substitution]
    ): Unit =
      if ( termSet isEmpty ) {
        val grammarSize = alreadyIncluded.size + s.size
        if ( grammarSize < minSize ) {
          minSize = grammarSize
          minGrammars += ( alreadyIncluded -> s )
        }
      } else if ( alreadyIncluded.size + s.size >= minSize ) {
        // Ignore this branch.
      } else if ( grammar isEmpty ) {
        throw new IllegalArgumentException
      } else {
        val focus = grammar maxBy { _._2.size }

        minimizeGrammar(
          termSet diff focus._2,
          grammar map { x => x._1 -> x._2.diff( focus._2 ) } filter { _._2.nonEmpty },
          alreadyIncluded + focus._1, s
        )

        val restLang = grammar - focus flatMap { _._2 }
        if ( termSet subsetOf restLang ) {
          minimizeGrammar( termSet, grammar - focus, alreadyIncluded, s )
        }
      }

    for ( ( s, decomps ) <- deltatable ) {
      val coveredTerms = decomps flatMap { _._2 }
      minimizeGrammar( coveredTerms, decomps, termSet diff coveredTerms, s )
    }

    for {
      g1 @ ( u1, s1 ) <- minGrammars
      g2 @ ( u2, s2 ) <- minGrammars
      if g1 != g2
      subst <- keySubsumption( s1, s2 )
      u = u2 ++ u1.map { Substitution( subst )( _ ) }
      s = s2
      row = for ( t <- u ) yield t -> s.map { _( t ) }.intersect( termSet )
    } minimizeGrammar( termSet, row, Set(), s )

    minGrammars minBy { g => g._1.size + g._2.size }
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
    val n = 12
    val terms1 = 0 until n map iter( "f", "c" ) map { FOLFunction( "r", _ ) }
    val terms2 = 0 until n map iter( "g", "d" ) map { FOLFunction( "s", _ ) }
    val terms = terms1 ++ terms2

    val deltatable = createTable( terms.toSet )

    //    val actualMinGrammar = findMinimalVectGrammar( terms.toSet, Seq( 1 ) )
    //
    //    val origDTableGrammar = DeltaTableMethod( false ).findGrammars( terms.toSet ).get

    val ( us, s ) = findGrammarFromDeltaTable( terms.toSet, deltatable )
    val vtratg = grammarToVTRATG( us, s )
    //    println( deltatable )
    println( vtratg )

    time {
      for ( i <- 1 to 5 ) {
        val ( u, s ) = findGrammarFromDeltaTable( terms.toSet, createTable( terms.toSet ) )
        grammarToVTRATG( u, s )
      }
    }
    time { for ( i <- 1 to 5 ) DeltaTableMethod( false ).findGrammars( terms.toSet ).get }
    Thread sleep 4000
    ()
  }
}

case class DeltaTableMethodNew(
    singleQuantifier: Boolean,
    tableSubsumption: Boolean,
    keyLimit:         Option[Int]
) extends GrammarFindingMethod {
  override def findGrammars( lang: Set[FOLTerm] ): Option[VectTratGrammar] = {
    val langSet = lang.toSet[LambdaExpression]

    var dtable = deltaTable.createTable( langSet, keyLimit )

    if ( tableSubsumption ) dtable = deltaTable.tableSubsumption( dtable )

    val ( us, s ) = deltaTable.findGrammarFromDeltaTable( langSet, dtable )

    Some( deltaTable.grammarToVTRATG( us, s ) )
  }

  def name = toString
}