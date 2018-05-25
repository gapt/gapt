package gapt.provers.smtlib

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool
import de.uni_freiburg.informatik.ultimate.logic._
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol
import gapt.expr._
import gapt.formats.lisp.{ LFun, LList, LSymbol }
import gapt.provers.IncrementalProver
import gapt.provers.Session.Runners.SessionRunner
import gapt.provers.Session._
import gapt.utils.{ Logger, NameGenerator }
import cats.implicits._
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy

import scala.collection.mutable

class SmtInterpol(
    val logic:                      String,
    override val treatUnknownAsSat: Boolean = false ) extends IncrementalProver {

  override def runSession[A]( program: Session[A] ) =
    new SmtInterpolSession().run( setLogic( logic ) >> program )
}
object SmtInterpol extends SmtInterpol( "QF_UF", false )

object SmtInterpolLogger extends Logger( "SMTInterpol" ) { l =>
  object proxy extends LogProxy {
    def setLoglevel( level: Int ): Unit = ()
    def getLoglevel: Int = 0

    def isFatalEnabled: Boolean = true
    def fatal( msg: String, params: AnyRef* ): Unit =
      l.warn( ( msg +: params ).mkString( " " ) )
    def fatal( msg: scala.Any ): Unit =
      fatal( msg.toString, Seq(): _* )

    def outOfMemory( msg: String ): Unit = throw new OutOfMemoryError

    def isErrorEnabled: Boolean = true
    def error( msg: String, params: AnyRef* ): Unit =
      l.warn( ( msg +: params ).mkString( " " ) )
    def error( msg: scala.Any ): Unit =
      error( msg.toString, Seq(): _* )

    def isWarnEnabled: Boolean = true
    def warn( msg: String, params: AnyRef* ): Unit =
      l.warn( ( msg +: params ).mkString( " " ) )
    def warn( msg: scala.Any ): Unit =
      warn( msg.toString, Seq(): _* )

    def isInfoEnabled: Boolean = false
    def info( msg: String, params: AnyRef* ): Unit = ()
    def info( msg: scala.Any ): Unit = ()

    def isDebugEnabled: Boolean = false
    def debug( msg: String, params: AnyRef* ): Unit = ()
    def debug( msg: scala.Any ): Unit = ()

    def isTraceEnabled: Boolean = false
    def trace( msg: String, params: AnyRef* ): Unit = ()
    def trace( msg: scala.Any ): Unit = ()

    def canChangeDestination: Boolean = false
    def changeDestination( newDest: String ): Unit = ()
    def getDestination: String = ""
  }
}

class SmtInterpolSession( script: Script ) extends SessionRunner {
  def this() = this( new SMTInterpol( SmtInterpolLogger.proxy ) )

  val nameGen = new NameGenerator( Set() )
  val funNames = mutable.Map[String, String]()
  val sortNames = mutable.Map[String, String]()

  sortNames( To.name ) = "Bool"

  // hardcoded in SMTInterpol as interpreted functions
  for ( reserved <- Seq( "Int", "<=", "select" ) )
    nameGen.fresh( reserved )

  private def declare[A]( n0: String, ns: mutable.Map[String, String], f: String => A ): A =
    try {
      val n = nameGen.fresh( n0 )
      val r = f( n )
      ns( n0 ) = n
      r
    } catch { case _: SMTLIBException => declare( n0, ns, f ) }

  import SessionCommand._
  protected def interpretCommand[A]( command: SessionCommand[A] ): A = command match {
    case Push => script.push( 1 )
    case Pop  => script.pop( 1 )
    case DeclareSort( sort ) =>
      declare( sort.name, sortNames, script.declareSort( _, sort.params.size ) )
    case DeclareFun( Const( fun, FunctionType( retType, argTypes ), _ ) ) =>
      val argSorts = argTypes.map( sort ).toArray
      val retSort = sort( retType )
      declare( fun, funNames, script.declareFun( _, argSorts, retSort ) )
    case Assert( formula ) =>
      script.assertTerm( term( formula ) )
      ()
    case AssertLabelled( formula, label ) =>
      script.assertTerm( script.annotate( term( formula ), new Annotation( ":named", label ) ) )
      ()
    case CheckSat =>
      script.checkSat() match {
        case LBool.SAT     => Right( true )
        case LBool.UNSAT   => Right( false )
        case LBool.UNKNOWN => Left( LFun( "unknown" ) )
      }
    case SetLogic( logic ) =>
      script.setLogic( logic )
    case SetOption( option, List( args ) ) =>
      script.setOption( ":" + option, args )
    case Ask( LFun( "get-unsat-core" ) ) =>
      LList( script.getUnsatCore.map { case t: ApplicationTerm => LSymbol( t.getFunction.getName ) }.toList )
    case Ask( input ) =>
      throw new UnsupportedOperationException( input.toString )
    case Tell( input ) =>
      throw new UnsupportedOperationException( input.toString )
  }

  val varName = mutable.Map[Var, Term]()
  def term( e: Expr ): Term =
    e match {
      case Top()       => script.term( "true" )
      case Bottom()    => script.term( "false" )
      case Neg( a )    => script.term( "not", term( a ) )
      case Imp( a, b ) => script.term( "=>", term( a ), term( b ) )
      case Or( a, b )  => script.term( "or", term( a ), term( b ) )
      case And( a, b ) => script.term( "and", term( a ), term( b ) )
      case v @ Var( n, t ) =>
        varName.getOrElseUpdate( v, script.variable( nameGen.fresh( n ), sort( t ) ) )
      case Eq( a, b )  => script.term( "=", term( a ), term( b ) )
      case All( _, _ ) => ???
      case Ex( _, _ )  => ???
      case Apps( Const( c, _, _ ), args ) =>
        script.term( funNames( c ), args.map( term ): _* )
    }

  def sort( t: Ty ): Sort =
    t match {
      case TBase( n, ps ) => script.sort( sortNames( n ), ps.map( sort ): _* )
      case TVar( n )      => script.sort( sortNames( n ) )
      case TArr( _, _ )   => ???
    }

}
