package at.logic.gapt.provers

import java.io.{ BufferedReader, InputStreamReader, PrintWriter }
import java.lang.ProcessBuilder.Redirect

import at.logic.gapt.expr._
import at.logic.gapt.formats.StringInputFile
import at.logic.gapt.formats.lisp._
import at.logic.gapt.proofs.{ HOLSequent, Sequent }
import at.logic.gapt.provers.smtlib.ExternalSmtlibProgram
import cats.free.Free.liftF
import cats.free._
import cats.implicits._
import cats.{ Id, ~> }

import scala.collection.mutable

/**
 * Created by sebastian on 24.11.16.
 */

/**
 * Implementation of proof sessions via the cats free monad. See [[http://typelevel.org/cats/datatypes/freemonad.html]].
 */
object Session {

  /**
   * Trait for individual session commands.
   * @tparam A The return type of the command.
   */
  sealed trait SessionCommand[A]

  private object SessionCommand {

    /**
     * Closes the session.
     */
    case object Close extends SessionCommand[Unit]

    /**
     * Pushes the current assertions and declarations on the stack.
     */
    case object Push extends SessionCommand[Unit]

    /**
     * Pops the stack, eliminating all assertions and declarations since the last push.
     */
    case object Pop extends SessionCommand[Unit]

    /**
     * Declares a function.
     */
    case class DeclareFun( fun: Const ) extends SessionCommand[Unit]

    /**
     * Declares a sort.
     */
    case class DeclareSort( sort: TBase ) extends SessionCommand[Unit]

    /**
     * Asserts a formula.
     */
    case class Assert( formula: HOLFormula ) extends SessionCommand[Unit]

    /**
     * Asserts a formula with a label.
     */
    case class AssertLabelled( formula: HOLFormula, label: String ) extends SessionCommand[Unit]

    /**
     * Checks whether the current set of declarations and assertions is satisfiable.
     */
    case object CheckSat extends SessionCommand[Boolean]

    /**
     * Sets the logic to be used for the session.
     */
    case class SetLogic( logic: String ) extends SessionCommand[Unit]

    /**
     * Sets an option to a value.
     */
    case class SetOption( option: String, args: List[String] ) extends SessionCommand[Unit]

    /**
     * Submits an SExpression and receives one in return.
     */
    case class Ask( input: SExpression ) extends SessionCommand[SExpression]

    /**
     * Submits an SExpression without a return.
     */
    case class Tell( input: SExpression ) extends SessionCommand[Unit]
  }

  type Session[A] = Free[SessionCommand, A]

  import SessionCommand._

  /*
   * Smart constructors that lift the operations of SessionCommand into the free monad.
   */

  /**
   * Closes the session.
   */
  def close = liftF( Close )

  /**
   * Pushes the current assertions and declarations on the stack.
   */
  def push = liftF( Push )

  /**
   * Pops the stack, eliminating all assertions and declarations since the last push.
   */
  def pop = liftF( Pop )

  /**
   * Asserts a formula.
   */
  def assert( f: HOLFormula ) = liftF( Assert( f ) )

  /**
   * Asserts a formula with a label.
   */
  def assert( f: HOLFormula, label: String ) = liftF( AssertLabelled( f, label ) )

  /**
   * Checks whether the current set of declarations and assertions is satisfiable.
   */
  def checkSat: Session[Boolean] = liftF( CheckSat )

  /**
   * Sets the logic to be used for the session.
   */
  def setLogic( logic: String ) = liftF( SetLogic( logic ) )

  /**
   * Sets an option to a value.
   */
  def setOption( option: String, args: String* ) = liftF( SetOption( option, args.toList ) )

  /**
   * Declares a sort.
   */
  def declareSort( sort: TBase ) = liftF( DeclareSort( sort ) )

  /**
   * Declares a function.
   */
  def declareFun( fun: Const ) = liftF( DeclareFun( fun ) )

  /**
   * Submits an SExpression and receives one in return.
   */
  def ask( input: SExpression ) = liftF( Ask( input ) )

  /**
   * Submits an SExpression without a return.
   */
  def tell( input: SExpression ) = liftF( Tell( input ) )

  /**
   * Asserts a list of formulas.
   */
  def assert( formulas: List[HOLFormula] ): Session[Unit] = formulas.traverseU_( assert )

  /**
   * Pushes the stack, then runs f, then pops the stack.
   */
  def withScope[A]( f: Session[A] ): Session[A] = wrap( push, pop )( f )

  /**
   * Encloses the session `f` between `before` and `after`.
   */
  def wrap[A]( before: Session[Unit], after: Session[Unit] )( f: Session[A] ) = for {
    _ <- before
    x <- f
    _ <- after
  } yield x

  /**
   * Declares all symbols (sorts and functions) in a list of LambdaExpressions.
   */
  def declareSymbolsIn( expressions: TraversableOnce[LambdaExpression] ): Session[Unit] = {
    val cs = expressions.toSet[LambdaExpression] flatMap { constants( _ ) } filter {
      case EqC( _ )           => false
      case _: LogicalConstant => false
      case _                  => true
    }
    val ts = cs flatMap { c => baseTypes( c.exptype ) } filter {
      case To => false
      case _  => true
    }

    for {
      _ <- ts.toList.traverseU_( declareSort )
      _ <- cs.toList.traverseU_( declareFun )
    } yield ()
  }

  /**
   * Declares all symbols (sorts and functions) in a list of LambdaExpressions.
   */
  def declareSymbolsIn( expressions: LambdaExpression* )( implicit d: DummyImplicit ): Session[Unit] = declareSymbolsIn( expressions.toList )

  /**
   * Contains various functions for interpreting a value of type Session.
    *
    * A "compiler" is a natural transformation from SessionCommand to Id; i.e. a function that can transform any
    * SessionCommand[A] to an Id[A] (= A).
    *
    * Given such a transformation comp: SessionCommand ~> Id, you can use it to interpret a session program p via
    * p.foldMap(comp).
   */
  object Compilers {

    /**
     * A compiler that interprets a Session by communicating with an SMTLib process. The process is left abstract --
     * it might not be an external program.
     *
     * Subclasses must implement the tell, ask, and close functions.
     */
    abstract class SMTLibSessionCompiler extends ( SessionCommand ~> Id ) {
      def tell( input: SExpression ): Unit
      def ask( input: SExpression ): SExpression
      def close(): Unit

      def apply[A]( command: SessionCommand[A] ): Id[A] = command match {
        case Close               => close()
        case Push                => apply( Tell( LFun( "push", LAtom( "1" ) ) ) )
        case Pop                 => apply( Tell( LFun( "pop", LAtom( "1" ) ) ) )
        case DeclareSort( sort ) => apply( Tell( LFun( "declare-sort", LAtom( typeRenaming( sort ).name ), LAtom( 0.toString ) ) ) )
        case DeclareFun( fun ) => termRenaming( fun ) match {
          case Const( name, FunctionType( TBase( retType ), argTypes ) ) =>
            apply( Tell( LFun( "declare-fun", LAtom( name ),
              LList( argTypes map { case TBase( argType ) => LAtom( argType ) }: _* ),
              LAtom( retType ) ) ) )
        }
        case Assert( formula )                => apply( Tell( LFun( "assert", convert( formula ) ) ) )

        case AssertLabelled( formula, label ) => apply( Tell( LFun( "assert", LFun( "!", convert( formula ), LAtom( ":named" ), LAtom( label ) ) ) ) )
        case CheckSat => ask( LFun( "check-sat" ) ) match {
          case LAtom( "sat" )   => true
          case LAtom( "unsat" ) => false
        }
        case SetLogic( logic )         => apply( Tell( LFun( "set-logic", LAtom( logic ) ) ) )
        case SetOption( option, args ) => apply( Tell( LFun( "set-option", ( option +: args ) map LAtom: _* ) ) )
        case Ask( input )              => ask( input )
        case Tell( input )             => tell( input )
      }
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

    }

    /**
     * An SMTLibSessionCompiler that actually communicates with an external program.
     *
     * Subclasses need to implement the command function.
     */
    abstract class ExternalSMTLibSessionCompiler extends SMTLibSessionCompiler {
      def command: Seq[String]
      val process = new ProcessBuilder( command: _* ).redirectError( Redirect.INHERIT ).start()
      val in = new PrintWriter( process.getOutputStream )
      val out = new BufferedReader( new InputStreamReader( process.getInputStream ) )

      override def tell( input: SExpression ) = {
        //if ( debug ) println( input )
        in println input
      }

      override def ask( input: SExpression ) = {
        //if ( debug ) println( input )
        in println input
        in.flush()
        val res = out.readLine()
        //if ( debug ) println( s"-> $res" )
        if ( res == null ) throw new ExternalSmtlibProgram.UnexpectedTerminationException( input )
        SExpressionParser( StringInputFile( res ) ).head
      }

      override def close() = process.destroy()
    }

    /**
     * An SMTLibSessionCompiler that writes to a string.
     *
     * Its `tell` simply writes to the string, while its `ask` writes
     * to the string and receives dummy replies.
     */
    class BenchmarkCompiler extends SMTLibSessionCompiler {
      private val nLine = sys.props( "line.separator" )

      private val benchmark = new StringBuilder
      def getBenchmark() = benchmark.result()

      override def tell( input: SExpression ) = benchmark append input append nLine
      override def ask( input: SExpression ) = {
        tell( input )
        input match {
          case LFun( "check-sat" ) => LAtom( "unsat" )
          case _                   => LList()
        }
      }

      override def close() = ()
    }

    /**
     * A compiler that interprets a session by literally manipulating a stack of sets of formulas.
     * @param checkValidity The function the compiler uses to test validity of sequents.
     */
    class StackSessionCompiler( checkValidity: HOLSequent => Boolean ) extends ( SessionCommand ~> Id ) {
      val formulaStack = mutable.Stack[Set[HOLFormula]]()
      var assertedFormulas = Set[HOLFormula]()

      override def apply[A]( command: SessionCommand[A] ): Id[A] = command match {
        case Push =>
          formulaStack push assertedFormulas; ()
        case Pop =>
          assertedFormulas = formulaStack.pop; ()
        case Assert( formula ) =>
          assertedFormulas += formula; ()
        case CheckSat                => !checkValidity( assertedFormulas ++: Sequent() )
        case Ask( input )            => input
        case _: SessionCommand[Unit] => ()
      }
    }
  }
}

