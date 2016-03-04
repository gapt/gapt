package at.logic.gapt.grammars.reforest

import at.logic.gapt.expr._
import at.logic.gapt.grammars._
import at.logic.gapt.proofs.lk.DefinitionElimination

import scala.collection.mutable

abstract class Feature
case class Digram( c1: Const, i: Int, c2: Const ) extends Feature
case class RigidTrigram( c: Const, i: Int, j: Int ) extends Feature

case class ReforestState(
    axiom:          Const,
    rules:          Map[LambdaExpression, Set[LambdaExpression]],
    highestNTIndex: Int
) {

  def stats: Map[Feature, Int] = {
    val s = mutable.Map[Feature, Int]().withDefaultValue( 0 )

    def visit( f: Const, as: Seq[LambdaExpression] ): Unit = {
      for ( ( a, i ) <- as.zipWithIndex; ( b, j ) <- as.zipWithIndex if i < j if a == b ) {
        s( RigidTrigram( f, i, j ) ) += 1
      }
      for ( ( Apps( g: Const, bs ), i ) <- as.zipWithIndex ) {
        visit( g, bs )
        s( Digram( f, i, g ) ) += 1
      }
    }

    for ( rhss <- rules.values; Apps( f: Const, as ) <- rhss ) visit( f, as )

    s.toMap
  }

  def abbreviate( feature: Feature ): ReforestState = feature match {
    case feature: Digram       => abbreviate( feature )
    case feature: RigidTrigram => abbreviate( feature )
  }

  def abbreviate( digram: Digram ): ReforestState = {
    val FunctionType( rettype, ts1 ) = digram.c1.exptype
    val FunctionType( _, ts2 ) = digram.c2.exptype
    val argtypes = ts1.take( digram.i ) ++ ts2 ++ ts1.drop( digram.i + 1 )
    val newNT = Const( s"B$highestNTIndex", FunctionType( rettype, argtypes ) )
    val newNTArgs = for ( ( t, i ) <- argtypes.zipWithIndex ) yield Var( s"x$i", t )

    def abbr( t: LambdaExpression ): LambdaExpression = t match {
      case Apps( digram.c1, as1_ ) =>
        // Innermost-first rewriting is really important here!
        val as1 = as1_ map abbr
        as1( digram.i ) match {
          case Apps( digram.c2, as2 ) =>
            newNT( as1.take( digram.i ) ++ as2 ++ as1.drop( digram.i + 1 ) map abbr: _* )
          case _ => digram.c1( as1 map abbr: _* )
        }
      case Apps( f, as ) => f( as map abbr: _* )
    }

    copy(
      rules = Map( newNT( newNTArgs: _* ) -> Set( digram.c1( newNTArgs.take( digram.i )
      ++ Seq( digram.c2( newNTArgs.slice( digram.i, digram.i + ts2.size ): _* ) )
      ++ newNTArgs.drop( digram.i + ts2.size ): _* ) ) ) ++
      rules.mapValues { _ map abbr },
      highestNTIndex = highestNTIndex + 1
    )
  }

  def abbreviate( rigidTrigram: RigidTrigram ): ReforestState = {
    val FunctionType( rettype, ts ) = rigidTrigram.c.exptype
    val argtypes = ts.take( rigidTrigram.j ) ++ ts.drop( rigidTrigram.j + 1 )
    val newNT = Const( s"B$highestNTIndex", FunctionType( rettype, argtypes ) )
    val newNTArgs = for ( ( t, i ) <- argtypes.zipWithIndex ) yield Var( s"x$i", t )

    def abbr( t: LambdaExpression ): LambdaExpression = t match {
      case Apps( rigidTrigram.c, as ) if as( rigidTrigram.i ) == as( rigidTrigram.j ) =>
        newNT( as.take( rigidTrigram.j ) ++ as.drop( rigidTrigram.j + 1 ) map abbr: _* )
      case Apps( f, as ) => f( as map abbr: _* )
    }

    copy(
      rules = Map( newNT( newNTArgs: _* ) -> Set( rigidTrigram.c(
      newNTArgs.take( rigidTrigram.j ) ++
        Seq( newNTArgs( rigidTrigram.i ) ) ++
        newNTArgs.drop( rigidTrigram.j ): _*
    ) ) ) ++
      rules.mapValues { _ map abbr },
      highestNTIndex = highestNTIndex + 1
    )
  }

  def decompose( nonTerminal: LambdaExpression ): ReforestState = {
    val rhss = rules( nonTerminal ).to[mutable.Set]

    require( freeVariables( nonTerminal ).isEmpty ) // TODO

    val maxArity = rhss.map { case Apps( c: Const, as ) => as.size }.max
    val argtypes = ( 0 until maxArity ) map { _ => Ti } // TODO
    val newNT = Const( s"B$highestNTIndex", FunctionType( Ti, argtypes ) )
    val newArgs = for ( ( t, i ) <- argtypes.zipWithIndex ) yield Var( s"x$i", t )

    val args1 = mutable.Set[Seq[LambdaExpression]]()
    val newRHS1s = mutable.Set[LambdaExpression]()
    val newRHS2s = mutable.Set[LambdaExpression]()

    for ( Apps( f, Seq() ) <- rhss ) {
      rhss -= f
      newRHS1s += f
    }
    for ( rhs @ Apps( f, as ) <- rhss.toSet if as.size == argtypes.size ) {
      args1 += as
      newRHS2s += f( newArgs: _* )
      rhss -= rhs
    }

    def subsume( as: Seq[LambdaExpression], bs: Seq[LambdaExpression] ): Option[Seq[Int]] =
      if ( as diff bs isEmpty ) Some {
        for ( a <- as ) yield bs indexOf a
      }
      else None

    while ( rhss.nonEmpty ) {
      for ( rhs @ Apps( f, as ) <- rhss.toSet; subs <- args1.flatMap { subsume( as, _ ) }.headOption ) {
        newRHS2s += f( subs map { newArgs( _ ) }: _* )
        rhss -= rhs
      }

      if ( rhss.nonEmpty ) {
        val rhs @ Apps( f, as ) = rhss.maxBy { case Apps( _, args ) => args.size }
        args1 += as ++ Stream.continually( FOLConst( "c" ) ).take( maxArity - as.size )
      }
    }

    for ( as <- args1 ) newRHS1s += newNT( as: _* )

    copy(
      rules = rules + ( nonTerminal -> newRHS1s.toSet ) + ( newNT( newArgs: _* ) -> newRHS2s.toSet ),
      highestNTIndex = highestNTIndex + 1
    )
  }

  def decomposeUsingDeltaTable( nonTerminal: LambdaExpression ): ReforestState = {
    require( freeVariables( nonTerminal ).isEmpty ) // TODO

    var dtable = deltaTableAlgorithm.createTable( rules( nonTerminal ) )
    dtable = deltaTableAlgorithm.mergeSubsumedRows( dtable )
    val ( us, ss ) = deltaTableAlgorithm.findGrammarFromDeltaTable( rules( nonTerminal ), dtable,
      subsumeMinimalGrammars = false )

    if ( ss isEmpty ) return this

    val newArgs = ss.head.domain.toSeq.sortBy { _.toString }
    val newNT = Const( s"B$highestNTIndex", FunctionType( nonTerminal.exptype, newArgs map { _.exptype } ) )

    copy(
      rules = rules + ( nonTerminal -> ss.map { s => newNT( s( newArgs ): _* ) } ) + ( newNT( newArgs: _* ) -> us ),
      highestNTIndex = highestNTIndex + 1
    )
  }

  def expand( nts: Traversable[LambdaExpression] ): ReforestState = {
    for ( nt <- nts ) require( rules( nt ).size == 1 )
    val simpl = DefinitionElimination( nts map { nt => nt -> rules( nt ).head } toMap )

    copy( rules = rules -- nts mapValues { _ map { simpl( _ ) } } )
  }

  def expandUseless: ReforestState = {
    val constFreq = mutable.Map[Const, Int]().withDefaultValue( 0 )
    def visit( t: LambdaExpression ): Unit = t match {
      case Apps( f: Const, as ) =>
        constFreq( f ) += 1
        as foreach visit
      case _ =>
    }
    for ( rhss <- rules.values; rhs <- rhss ) visit( rhs )

    expand( rules.collect {
      case ( nt @ Apps( f: Const, _ ), rhs ) if rhs.size == 1 && constFreq( f ) <= 1 => nt
    } )
  }

  def expandDeterministic: ReforestState =
    expand( for ( ( nt, rhs ) <- rules if rhs.size == 1 ) yield nt )

  def prodSize: Int = rules.values map { _.size } sum

  override def toString =
    ( for ( ( lhs, rhss ) <- rules; rhs <- rhss ) yield s"$lhs -> $rhs\n" ).toSeq.sorted.mkString

  def toRecursionScheme: RecursionScheme =
    RecursionScheme( axiom, for ( ( nt, rhss ) <- rules.toSet; rhs <- rhss ) yield Rule( nt, rhs ) )

  def toVTRATG: VectTratGrammar = recSchemToVTRATG( toRecursionScheme )

}

object Reforest {
  def start( lang: Traversable[LambdaExpression] ): ReforestState =
    ReforestState(
      axiom = FOLConst( "A" ),
      rules = Map( FOLConst( "A" ) -> lang.toSet ),
      highestNTIndex = 0
    )

  def compress( s: ReforestState ): ReforestState = {
    val stats = s.stats
    val ( feat, freq ) = stats.maxBy { _._2 }
    if ( freq > 1 ) compress( s abbreviate feat )
    else s
  }

  def full( start: ReforestState ): ReforestState = {
    def f( s: ReforestState ): ReforestState = {
      for ( ( nt @ Apps( _, Seq() ), rhss ) <- s.rules if rhss.size > 1 ) {
        val next = s.decompose( nt )
        val simpl = compress( next.expandDeterministic )
        if ( simpl.prodSize < s.prodSize ) return f( simpl )
      }

      s.expandDeterministic
    }

    f( compress( start ) )
  }
}
