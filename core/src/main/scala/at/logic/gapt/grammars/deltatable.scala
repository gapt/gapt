package at.logic.gapt.grammars

import at.logic.gapt.cutintro.GrammarFindingMethod
import at.logic.gapt.expr._

import scala.collection.mutable

object deltaTableAlgorithm {
  type Row = Set[( LambdaExpression, Set[LambdaExpression] )]

  def createTable(
    termSet:        Set[LambdaExpression],
    maxArity:       Option[Int]           = None,
    singleVariable: Boolean               = false
  ): Map[Set[Substitution], Row] = {
    // invariant:  deltatable(S) contains (u,T)  ==>  u S = T  &&  |S| = |T|
    val deltatable = mutable.Map[Set[Substitution], List[( LambdaExpression, Set[LambdaExpression] )]]().
      withDefaultValue( Nil )

    def populate(
      remainingTerms: List[LambdaExpression],
      currentLGG:     LambdaExpression,
      currentCover:   Set[LambdaExpression],
      currentSubst:   Set[Substitution]
    ): Unit = if ( remainingTerms.nonEmpty ) {
      val ( newTerm :: rest ) = remainingTerms

      val ( newLGG, substCurLGG, substNewTerm ) =
        if ( currentLGG == null ) ( newTerm, Map[Var, LambdaExpression](), Map[Var, LambdaExpression]() )
        else if ( singleVariable ) leastGeneralGeneralization1( currentLGG, newTerm )
        else leastGeneralGeneralization( currentLGG, newTerm )

      if ( !newLGG.isInstanceOf[Var] && maxArity.forall { substCurLGG.size <= _ } ) {
        val newSubst = currentSubst.map { subst => Substitution( substCurLGG mapValues { subst( _ ) } ) } + Substitution( substNewTerm )
        val newCover = currentCover + newTerm
        deltatable( newSubst ) ::= ( newLGG -> newCover )
        populate( rest, newLGG, newCover, newSubst )
      }

      populate( rest, currentLGG, currentCover, currentSubst )
    }

    populate( termSet.toList, null, Set(), Set() )

    deltatable.mapValues { _.toSet }.toMap
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

  def mergeSubsumedRows( table: Map[Set[Substitution], Row] ): Map[Set[Substitution], Row] =
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

  def findGrammarFromDeltaTable(
    termSet:                Set[LambdaExpression],
    deltatable:             Map[Set[Substitution], Row],
    subsumeMinimalGrammars: Boolean
  ): ( Set[LambdaExpression], Set[Substitution] ) = {
    var minSize = termSet.size + 1
    val minGrammars = mutable.Buffer[( Set[LambdaExpression], Set[Substitution] )]()

    def minimizeRow(
      termSet:         Set[LambdaExpression],
      row:             Row,
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
      } else if ( row isEmpty ) {
        throw new IllegalArgumentException
      } else {
        val pivot = row maxBy { _._2.size }

        // Case 1, pivot is included.
        minimizeRow(
          termSet diff pivot._2,
          row map { x => x._1 -> x._2.diff( pivot._2 ) } filter { _._2.nonEmpty },
          alreadyIncluded + pivot._1,
          s
        )

        // Case 2, pivot is not included.
        val restRow = row filterNot { _._2 subsetOf pivot._2 }
        val restLang = restRow flatMap { _._2 }
        if ( termSet subsetOf restLang )
          minimizeRow( termSet, restRow, alreadyIncluded, s )
      }

    for ( ( s, decomps ) <- deltatable.toSeq sortBy { -_._1.toSeq.flatMap { _.map.values }.map { expressionSize( _ ) }.sum } ) {
      val coveredTerms = decomps flatMap { _._2 }
      minimizeRow( coveredTerms, decomps, termSet diff coveredTerms, s )
    }

    if ( subsumeMinimalGrammars ) for {
      g1 @ ( u1, s1 ) <- minGrammars
      g2 @ ( u2, s2 ) <- minGrammars
      if g1 != g2
      subst <- keySubsumption( s1, s2 )
      u = u2 ++ u1.map { Substitution( subst )( _ ) }
      s = s2
      row = for ( t <- u ) yield t -> s.map { _( t ) }.intersect( termSet )
    } minimizeRow( termSet, row, Set(), s )

    if ( minGrammars isEmpty ) termSet -> Set()
    else minGrammars minBy { g => g._1.size + g._2.size }
  }

  def grammarToVTRATG( us: Set[LambdaExpression], s: Set[Substitution] ): VectTratGrammar = {
    val alpha = freeVariables( us ).toList.sortBy { _.toString }.asInstanceOf[List[FOLVar]]
    val tau = rename( FOLVar( "x0" ), alpha )
    VectTratGrammar( tau, Seq( List( tau ), alpha ),
      ( for ( subst <- s ) yield alpha -> alpha.map { subst( _ ).asInstanceOf[FOLTerm] } )
        union ( for ( u <- us ) yield List( tau ) -> List( u.asInstanceOf[FOLTerm] ) ) )
  }

}

case class DeltaTableMethod(
    singleQuantifier:   Boolean     = false,
    subsumedRowMerging: Boolean     = false,
    keyLimit:           Option[Int] = None
) extends GrammarFindingMethod {
  import deltaTableAlgorithm._

  override def findGrammars( lang: Set[FOLTerm] ): Option[VectTratGrammar] = {
    val langSet = lang.toSet[LambdaExpression]

    var dtable = createTable( langSet, keyLimit, singleQuantifier )

    if ( subsumedRowMerging ) dtable = mergeSubsumedRows( dtable )

    val ( us, s ) = findGrammarFromDeltaTable( langSet, dtable, false )

    Some( grammarToVTRATG( us, s ) )
  }

  def name = {
    val n = new StringBuilder
    n append ( if ( singleQuantifier ) "1" else "many" )
    n append "_dtable"
    if ( subsumedRowMerging ) n append "_ss"
    for ( l <- keyLimit ) n append s"_lim$l"
    n append "_new"
    n.result()
  }
}