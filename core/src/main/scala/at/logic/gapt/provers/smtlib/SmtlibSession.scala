package at.logic.gapt.provers.smtlib

import java.io.{ InputStreamReader, BufferedReader, PrintWriter }
import java.lang.ProcessBuilder.Redirect

import at.logic.gapt.expr._
import at.logic.gapt.formats.lisp._
import at.logic.gapt.provers.IncrementalProvingSession

import scala.collection.mutable

abstract class SmtlibSession extends IncrementalProvingSession {
  var debug = false

  def tell( input: SExpression ): Unit
  def ask( input: SExpression ): SExpression
  def close()

  def sendSuccess( input: SExpression ): Unit = tell( input )

  def setLogic( logic: String ) = sendSuccess( LFun( "set-logic", LAtom( logic ) ) )
  def setOption( option: String, args: String* ) = sendSuccess( LFun( "set-option", ( option +: args ) map LAtom: _* ) )

  object typeRenaming {
    val map = mutable.Map[TBase, TBase]()

    private var i = 0
    def apply( t: TBase ): TBase = map.getOrElseUpdate( t, t match {
      case To => TBase( "Bool" )
      case _  => i += 1; TBase( s"t$i" )
    } )

    def apply( t: Ty ): Ty = t match {
      case base: TBase  => apply( base )
      case `->`( a, b ) => apply( a ) -> apply( b )
    }
  }

  object termRenaming {
    val map = mutable.Map[Const, Const]()

    private var i = 0
    def apply( c: Const ): Const = map.getOrElseUpdate( c, {
      i += 1
      Const( s"f$i", typeRenaming( c.exptype ) )
    } )
  }

  def convert( expr: LambdaExpression, boundVars: Map[Var, String] = Map() ): SExpression = expr match {
    case Top()       => LAtom( "true" )
    case Bottom()    => LAtom( "false" )
    case Neg( a )    => LFun( "not", convert( a, boundVars ) )
    case And( a, b ) => LFun( "and", convert( a, boundVars ), convert( b, boundVars ) )
    case Or( a, b )  => LFun( "or", convert( a, boundVars ), convert( b, boundVars ) )
    case Imp( a, b ) => LFun( "=>", convert( a, boundVars ), convert( b, boundVars ) )
    case Eq( a, b )  => LFun( "=", convert( a, boundVars ), convert( b, boundVars ) )
    case c: Const    => LAtom( termRenaming( c ).name )
    case All( x @ Var( _, ty: TBase ), a ) =>
      val smtVar = s"x${boundVars.size}"
      LFun( "forall", LList( LFun( smtVar, LAtom( typeRenaming( ty ).name ) ) ), convert( a, boundVars + ( x -> smtVar ) ) )
    case Ex( x @ Var( _, ty: TBase ), a ) =>
      val smtVar = s"x${boundVars.size}"
      LFun( "exists", LList( LFun( smtVar, LAtom( typeRenaming( ty ).name ) ) ), convert( a, boundVars + ( x -> smtVar ) ) )
    case v: Var => LAtom( boundVars( v ) )
    case Apps( c: Const, args ) =>
      LFun( termRenaming( c ).name, args map { convert( _, boundVars ) }: _* )
  }

  def declareSymbolsIn( expressions: TraversableOnce[LambdaExpression] ): Unit = {
    val cs = expressions.toSet[LambdaExpression] flatMap { constants( _ ) } filter {
      case EqC( _ )           => false
      case _: LogicalConstant => false
      case _                  => true
    }
    val ts = cs flatMap { c => baseTypes( c.exptype ) } filter {
      case To => false
      case _  => true
    }

    ts foreach declareSort
    cs foreach declareFun
  }

  def declareSort( sort: TBase ) =
    sendSuccess( LFun( "declare-sort", LAtom( typeRenaming( sort ).name ), LAtom( 0.toString ) ) )
  def declareFun( fun: Const ) = termRenaming( fun ) match {
    case Const( name, FunctionType( TBase( retType ), argTypes ) ) =>
      sendSuccess( LFun( "declare-fun", LAtom( name ),
        LList( argTypes map { case TBase( argType ) => LAtom( argType ) }: _* ),
        LAtom( retType ) ) )
  }

  def assert( f: HOLFormula ) = sendSuccess( LFun( "assert", convert( f ) ) )
  def assert( f: HOLFormula, label: String ) =
    sendSuccess( LFun( "assert", LFun( "!", convert( f ), LAtom( ":named" ), LAtom( label ) ) ) )

  def checkSat(): Boolean = ask( LFun( "check-sat" ) ) match {
    case LAtom( "sat" )   => true
    case LAtom( "unsat" ) => false
  }

  def produceUnsatCores() = setOption( ":produce-unsat-cores", "true" )
  def getUnsatCore(): Seq[String] = ask( LFun( "get-unsat-core" ) ) match {
    case LList( labels @ _* ) => labels map { case LAtom( l ) => l }
  }

  def push() = sendSuccess( LFun( "push", LAtom( "1" ) ) )
  def pop() = sendSuccess( LFun( "pop", LAtom( "1" ) ) )
}

class BenchmarkRecordingSession extends SmtlibSession {
  private val nLine = sys.props( "line.separator" )

  private val benchmark = new StringBuilder
  def getBenchmark() = benchmark.result()

  override def tell( input: SExpression ) = benchmark append input append nLine

  override def ask( input: SExpression ) = {
    tell( input )
    input match {
      case LFun( "check-sat" )      => LAtom( "unsat" )
      case LFun( "get-unsat-core" ) => LList()
    }
  }

  override def close() = ()
}

abstract class ExternalSmtlibProgram extends SmtlibSession {
  def command: Seq[String]

  val process = new ProcessBuilder( command: _* ).redirectError( Redirect.INHERIT ).start()
  val in = new PrintWriter( process.getOutputStream )
  val out = new BufferedReader( new InputStreamReader( process.getInputStream ) )

  override def tell( input: SExpression ) = {
    if ( debug ) println( input )
    in println input
  }

  override def ask( input: SExpression ) = {
    if ( debug ) println( input )
    in println input
    in.flush()
    val res = out.readLine()
    if ( debug ) println( s"-> $res" )
    require( res != null, s"SMT solver terminated unexpectedly on $input" )
    SExpressionParser.parseString( res ).head
  }

  override def close() = process.destroy()
}
