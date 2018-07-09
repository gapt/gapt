package gapt.provers.smtlib

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool
import de.uni_freiburg.informatik.ultimate.logic._
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol
import gapt.expr._
import gapt.formats.lisp.{ LFun, LList, LSymbol }
import gapt.provers.{ IncrementalProver, groundFreeVariables }
import gapt.provers.Session.Runners.SessionRunner
import gapt.provers.Session._
import gapt.utils.{ Logger, Maybe, NameGenerator, Tree }
import cats.implicits._
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy
import gapt.proofs.Context

import scala.collection.mutable

class SmtInterpol(
    val logic:                      String,
    override val treatUnknownAsSat: Boolean = false ) extends IncrementalProver {

  override def runSession[A]( program: Session[A] ) =
    new SmtInterpolSession().run( setLogic( logic ) >> program )

  override def getInterpolant( tree: Tree[Formula] )( implicit ctx: Maybe[Context] ): Option[Tree[Formula]] = {
    val fvs = freeVariables( tree.postOrder )
    if ( fvs.nonEmpty ) return {
      val groundingMap = groundFreeVariables.getGroundingMap( fvs, constants( tree.postOrder ) )
      TermReplacement.hygienic(
        getInterpolant( Substitution( groundingMap )( tree ) ),
        groundingMap.map( _.swap ).toMap )
    }

    val session = new SmtInterpolSession
    session.run( setOption( "produce-proofs", "true" ) >> setLogic( logic ) )
    session.run( declareSymbolsIn( containedNames( tree ) ) )
    val labels = tree.map( _ => session.nameGen.freshWithIndex( "IP" ) )
    labels.zip( tree ).foreach { case ( l, f ) => session.run( assert( f, l ) ) }
    session.run( checkUnsat ) match {
      case Right( true ) =>
        val startOfSubtree = mutable.Buffer[Int]()
        val terms = mutable.Buffer[Term]()
        def g( t: Tree[String] ): Unit = {
          val start = terms.size
          for ( c <- t.children ) g( c )
          terms += session.script.term( t.value )
          startOfSubtree += start
        }
        g( labels )
        val is = session.script.getInterpolants( terms.toArray, startOfSubtree.toArray )
        val isMap = labels.postOrder.zip( is.map( session.expr( _ ).asInstanceOf[Formula] ) ).toMap
        Some( labels.map( isMap.getOrElse( _, Bottom() ) ) )
      case _ =>
        None
    }
  }
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

class SmtInterpolSession( val script: Script ) extends SessionRunner {
  def this() = this( new SMTInterpol( SmtInterpolLogger.proxy ) )

  val nameGen = new NameGenerator( Set() )
  val funNames = mutable.Map[Const, String]()
  val sortNames = mutable.Map[Ty, String]()
  val funNamesInv = mutable.Map[String, Const]()
  val sortNamesInv = mutable.Map[String, Ty]()

  sortNames( To ) = "Bool"

  // hardcoded in SMTInterpol as interpreted functions
  for ( reserved <- Seq( "Int", "<=", "select", "+", "*", "0" ) )
    nameGen.fresh( reserved )

  private def declare[T]( n0: String, t: T,
                          ns:  mutable.Map[T, String],
                          ins: mutable.Map[String, T],
                          f:   String => Unit ): Unit =
    try {
      val n = nameGen.fresh( n0 )
      f( n )
      ns( t ) = n
      ins( n ) = t
    } catch { case _: SMTLIBException => declare( n0, t, ns, ins, f ) }

  import SessionCommand._
  protected def interpretCommand[A]( command: SessionCommand[A] ): A = command match {
    case Push => script.push( 1 )
    case Pop  => script.pop( 1 )
    case DeclareSort( sort ) =>
      declare( sort.name, sort, sortNames, sortNamesInv, script.declareSort( _, sort.params.size ) )
    case DeclareFun( c @ Const( fun, FunctionType( retType, argTypes ), _ ) ) =>
      val argSorts = argTypes.map( sort ).toArray
      val retSort = sort( retType )
      declare( fun, c, funNames, funNamesInv, script.declareFun( _, argSorts, retSort ) )
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
      case Apps( c: Const, args ) =>
        script.term( funNames( c ), args.map( term ): _* )
    }

  def sort( t: Ty ): Sort =
    script.sort( sortNames( t ) )

  def expr( t: Term ): Expr =
    t match {
      case t: ApplicationTerm =>
        val ps = t.getParameters.view.map( expr ).toList
        t.getFunction.getName match {
          case "true"  => Top()
          case "false" => Bottom()
          case "=" =>
            val Seq( a, b ) = ps
            if ( a.ty == To ) a <-> b else a === b
          case "or"  => Or.nAry( ps: _* )
          case "and" => And.nAry( ps: _* )
          case "=>" =>
            val Seq( a, b ) = ps
            a --> b
          case "ite" =>
            val Seq( a, b, c ) = ps
            ( a --> b ) & ( -a --> c )
          case "not" =>
            val Seq( p ) = ps
            Neg( p )
          case n =>
            funNamesInv( n )( ps )
        }
    }

}
