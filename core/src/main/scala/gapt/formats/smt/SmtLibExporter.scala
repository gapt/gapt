package gapt.formats.smt

import gapt.expr._
import gapt.proofs.HOLSequent
import gapt.provers.Session.Runners._
import gapt.provers.Session._

object SmtLibExporter {

  /**
   *  Takes a sequent and generates the SMT-LIB benchmark as a string.
   *
   * @param s Sequent to export.
   * @return SMT-LIB benchmark.
   */
  def apply( s: HOLSequent, lineWidth: Int = 80 ): ( String, Map[TBase, TBase], Map[Const, Const] ) = {
    val p = for {
      _ <- setLogic( "QF_UF" )
      _ <- declareSymbolsIn( s.elements )
      _ <- assert( s.map( identity, -_ ).elements.toList )
      _ <- checkSat
    } yield ()

    val benchmarkRecorder = new BenchmarkRecorder( lineWidth )

    benchmarkRecorder.run( p )

    ( benchmarkRecorder.getBenchmark(), benchmarkRecorder.typeRenaming.map.toMap, benchmarkRecorder.termRenaming.map.toMap )
  }

  def bup( bup: Formula, lineWidth: Int = 80 ): String = {
    val Ex.Block( rels, matrix ) = bup
    val query =
      PropAtom( rename.awayFrom( containedNames( bup ) ).fresh( "q" ) )
    val groundRels = rels.map { case Var( n, t ) => Const( n, t ) } :+ query
    val clauses0 = matrix match {
      case And.nAry( sequents ) =>
        sequents.map {
          case All.Block( _, Imp( body, head @ Apps( x, _ ) ) ) if rels.contains( x ) =>
            body -> Some( head )
          case All.Block( _, Imp( body, head ) ) =>
            ( body & -head ) -> None
        }
    }

    val vars = freeVariables( clauses0.map( _._1 ) ++ clauses0.flatMap( _._2 ) ).diff( rels.toSet )
    val groundVars = vars.map { case Var( n, t ) => Const( n, t ) }
    val clauses = Substitution( ( rels zip groundRels ) ++ ( vars zip groundVars ) )( clauses0 )

    import gapt.formats.lisp._
    val rec = new BenchmarkRecorder( lineWidth )
    rec.run( setOption( "fp.engine", "spacer" ) )
    rec.run( declareSymbolsIn( bup ) )
    for ( c @ Const( _, FunctionType( _, tys ), _ ) <- groundRels )
      rec.run( ask( LFun( "declare-rel", rec.convert( c ),
        LList( tys.map( rec.typeRenaming( _ ).asInstanceOf[TBase].name ).map( LSymbol ) ) ) ) )
    for ( c @ Const( _, ty: TBase, _ ) <- groundVars )
      rec.run( ask( LFun( "declare-var", rec.convert( c ), LSymbol( rec.typeRenaming( ty ).name ) ) ) )
    for ( ( body, head ) <- clauses )
      rec.run( ask( LFun( "rule", rec.convert( body --> head.getOrElse( query ) ) ) ) )
    rec.run( ask( LFun( "query", rec.convert( query ), LKeyword( "print-certificate" ), LSymbol( "true" ) ) ) )
    rec.getBenchmark()
  }
}
