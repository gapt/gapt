package gapt.provers

import java.io.{ BufferedReader, InputStreamReader, PrintWriter }
import java.lang.ProcessBuilder.Redirect

import gapt.expr._
import gapt.formats.StringInputFile
import gapt.formats.lisp._
import gapt.proofs.{ HOLSequent, Sequent }
import gapt.provers.smtlib.ExternalSmtlibProgram
import gapt.utils.NameGenerator
import cats.free.Free.liftF
import cats.free._
import cats.implicits._
import cats.{ Id, ~> }

import scala.collection.mutable

/**
 * Implementation of proof sessions via the cats free monad. See [[http://typelevel.org/cats/datatypes/freemonad.html]].
 */
object Session {

  /**
   * Trait for individual session commands.
   * @tparam A The return type of the command.
   */
  sealed trait SessionCommand[A]

  object SessionCommand {

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
    case class Assert( formula: Formula ) extends SessionCommand[Unit]

    /**
     * Asserts a formula with a label.
     */
    case class AssertLabelled( formula: Formula, label: String ) extends SessionCommand[Unit]

    /**
     * Checks whether the current set of declarations and assertions is satisfiable.
     */
    case object CheckSat extends SessionCommand[Either[SExpression, Boolean]]

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
  def assert( f: Formula ) = liftF( Assert( f ) )

  /**
   * Asserts a formula with a label.
   */
  def assert( f: Formula, label: String ) = liftF( AssertLabelled( f, label ) )

  /**
   * Checks whether the current set of declarations and assertions is satisfiable.
   */
  def checkSat: Session[Either[SExpression, Boolean]] = liftF( CheckSat )

  /**
   * Checks whether the current set of declarations and assertions is not satisfiable.
   */
  def checkUnsat: Session[Either[SExpression, Boolean]] = checkSat.map( _.map( !_ ) )

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

  def pure[T]( t: T ): Session[T] = Free.pure[SessionCommand, T]( t )

  def skip: Session[Unit] = pure( () )

  /**
   * Asserts a list of formulas.
   */
  def assert( formulas: List[Formula] ): Session[Unit] = formulas.traverse_( assert )

  /**
   * Pushes the stack, then runs f, then pops the stack.
   */
  def withScope[A]( f: Session[A] ): Session[A] = wrap( push, f, pop )

  /**
   * Encloses the session `f` between `before` and `after`.
   */
  def wrap[A]( before: Session[Unit], f: Session[A], after: Session[Unit] ): Session[A] = for {
    _ <- before
    x <- f
    _ <- after
  } yield x

  /**
   * Declares all symbols (sorts and functions) in a list of Exprs.
   */
  def declareSymbolsIn( expressions: TraversableOnce[Expr] ): Session[Unit] = {
    val cs = expressions.toSet[Expr] flatMap { constants( _ ) } filter {
      case EqC( _ )           => false
      case _: LogicalConstant => false
      case _                  => true
    }
    val ts = cs flatMap { c => baseTypes( c.ty ) } filter {
      case To => false
      case _  => true
    }

    for {
      _ <- ts.toList.traverse_( declareSort )
      _ <- cs.toList.traverse_( declareFun )
    } yield ()
  }

  /**
   * Declares all symbols (sorts and functions) in a list of Exprs.
   */
  def declareSymbolsIn( expressions: Expr* )( implicit d: DummyImplicit ): Session[Unit] = declareSymbolsIn( expressions.toList )

  def when( p: Boolean )( s: Session[Unit] ) = if ( p ) s else skip

  /**
   * Contains various functions for interpreting a value of type Session.
   *
   * A "runner" contains a natural transformation from SessionCommand to Id; i.e. a function that can transform any
   * SessionCommand[A] to an Id[A] (= A).
   *
   * Given such a transformation comp: SessionCommand ~> Id, you can use it to interpret a session program p via
   * p.foldMap(comp).
   */
  object Runners {

    /**
     * Runs a session. What that means, exactly, is up to the concrete implementation.
     */
    abstract class SessionRunner {
      /**
       * Interprets a single session command.
       */
      protected def interpretCommand[A]( command: SessionCommand[A] ): A

      /**
       * Runs a session by wrapping the `interpretCommand` function into a natural transformation
       * trans: SessionCommand ~> Id and calling session.foldMap(trans).
       */
      def run[A]( session: Session[A] ): A = {
        val trans = new ( SessionCommand ~> Id ) {
          def apply[B]( command: SessionCommand[B] ): B = interpretCommand( command )
        }
        session.foldMap( trans )
      }
    }

    /**
     * A runner that interprets a Session by communicating with an SMTLib process. The process is left abstract --
     * it might not be an external program.
     *
     * Subclasses must implement the tell and ask functions.
     */
    abstract class SMTLibSessionRunner extends SessionRunner {
      protected def tell( input: SExpression ): Unit
      protected def ask( input: SExpression ): SExpression

      protected def interpretCommand[A]( command: SessionCommand[A] ): A = command match {
        case Push                => tell( LFun( "push", LSymbol( "1" ) ) )
        case Pop                 => tell( LFun( "pop", LSymbol( "1" ) ) )
        case DeclareSort( sort ) => tell( LFun( "declare-sort", LSymbol( typeRenaming( sort ).name ), LSymbol( 0.toString ) ) )
        case DeclareFun( fun ) => termRenaming( fun ) match {
          case Const( name, FunctionType( TBase( retType, Nil ), argTypes ), _ ) =>
            tell( LFun( "declare-fun", LSymbol( name ),
              LList( argTypes.map {
                case TBase( argType, Nil ) => LSymbol( argType )
                case ty                    => throw new IllegalArgumentException( s"unsupported type: $ty" )
              } ),
              LSymbol( retType ) ) )
        }
        case Assert( formula )                => tell( LFun( "assert", convert( formula ) ) )

        case AssertLabelled( formula, label ) => tell( LFun( "assert", LFun( "!", convert( formula ), LKeyword( "named" ), LSymbol( label ) ) ) )
        case CheckSat => ask( LFun( "check-sat" ) ) match {
          case LSymbol( "sat" )   => Right( true )
          case LSymbol( "unsat" ) => Right( false )
          case unknown            => Left( unknown )
        }
        case SetLogic( logic )         => tell( LFun( "set-logic", LSymbol( logic ) ) )
        case SetOption( option, args ) => tell( LFun( "set-option", LKeyword( option ) +: args.map( LSymbol ): _* ) )
        case Ask( input )              => ask( input )
        case Tell( input )             => tell( input )
      }

      protected val nameGen = new NameGenerator( Set() ) // TODO: add reserved keywords?

      object typeRenaming {
        val map = mutable.Map[TBase, TBase]()

        def apply( t: TBase ): TBase = map.getOrElseUpdate( t, t match {
          case To => TBase( "Bool", Nil )
          case TBase( n, _ ) => // TODO: polymorphic types
            TBase( nameGen.fresh( mangleName( n, "t_" ) ), Nil )
        } )

        def apply( t: Ty ): Ty = t match {
          case base: TBase => apply( base )
          case a ->: b     => apply( a ) ->: apply( b )
        }
      }

      object termRenaming {
        val map = mutable.Map[Const, Const]()
        def apply( c: Const ): Const = map.getOrElseUpdate(
          c,
          Const( nameGen.fresh( mangleName( c.name ) ), typeRenaming( c.ty ) ) )
      }

      def convert( expr: Expr, boundVars: Map[Var, String] = Map() ): SExpression = expr match {
        case Top()       => LSymbol( "true" )
        case Bottom()    => LSymbol( "false" )
        case Neg( a )    => LFun( "not", convert( a, boundVars ) )
        case And( a, b ) => LFun( "and", convert( a, boundVars ), convert( b, boundVars ) )
        case Or( a, b )  => LFun( "or", convert( a, boundVars ), convert( b, boundVars ) )
        case Imp( a, b ) => LFun( "=>", convert( a, boundVars ), convert( b, boundVars ) )
        case Eq( a, b )  => LFun( "=", convert( a, boundVars ), convert( b, boundVars ) )
        case c: Const    => LSymbol( termRenaming( c ).name )
        case All( x @ Var( _, ty: TBase ), a ) =>
          val smtVar = s"x${boundVars.size}"
          LFun( "forall", LList( LFun( smtVar, LSymbol( typeRenaming( ty ).name ) ) ), convert( a, boundVars + ( x -> smtVar ) ) )
        case Ex( x @ Var( _, ty: TBase ), a ) =>
          val smtVar = s"x${boundVars.size}"
          LFun( "exists", LList( LFun( smtVar, LSymbol( typeRenaming( ty ).name ) ) ), convert( a, boundVars + ( x -> smtVar ) ) )
        case v: Var => LSymbol( boundVars( v ) )
        case Apps( c: Const, args ) =>
          LFun( termRenaming( c ).name, args map { convert( _, boundVars ) }: _* )
      }

    }

    /**
     * An SMTLibSessionRunner that actually communicates with an external program.
     * @param command The command & list of options used to start the external program.
     */
    class ExternalSMTLibSessionRunner( command: String* ) extends SMTLibSessionRunner {
      val process = new ProcessBuilder( command: _* ).redirectError( Redirect.INHERIT ).start()
      val in = new PrintWriter( process.getOutputStream )
      val out = new BufferedReader( new InputStreamReader( process.getInputStream ) )
      var debug = false

      protected def tell( input: SExpression ) = {
        if ( debug ) println( input )
        in println input.toDoc.render( Int.MaxValue )
      }

      protected def ask( input: SExpression ) = {
        if ( debug ) println( input )
        in println input.toDoc.render( Int.MaxValue )
        in.flush()
        val res = out.readLine()
        if ( debug ) println( s"-> $res" )
        if ( res == null ) throw new ExternalSmtlibProgram.UnexpectedTerminationException( input )
        SExpressionParser( StringInputFile( res ) ).head
      }
    }

    /**
     * An SMTLibSessionRunner that writes all commands sequentially to a string.
     *
     * Its `tell` simply writes to the string, while its `ask` writes
     * to the string and receives dummy replies.
     */
    class BenchmarkRecorder( lineWidth: Int = 80 ) extends SMTLibSessionRunner {
      private val benchmark = new StringBuilder
      def getBenchmark() = benchmark.result()

      protected def tell( input: SExpression ) =
        benchmark append ( input.toDoc <> "\n" ).render( lineWidth )
      protected def ask( input: SExpression ) = {
        tell( input )
        input match {
          case LFun( "check-sat" ) => LSymbol( "unsat" )
          case _                   => LList()
        }
      }
    }

    /**
     * A runner that interprets a session by manipulating a stack of sets of formulas.
     * @param checkValidity The function the runner uses to test validity of sequents.
     */
    class StackSessionRunner( checkValidity: HOLSequent => Boolean ) extends SessionRunner {
      val formulaStack = mutable.Stack[Set[Formula]]()
      var assertedFormulas = Set[Formula]()

      protected def interpretCommand[A]( command: SessionCommand[A] ): Id[A] = command match {
        case Push =>
          formulaStack push assertedFormulas; ()
        case Pop =>
          assertedFormulas = formulaStack.pop; ()
        case Assert( formula ) =>
          assertedFormulas += formula; ()
        case AssertLabelled( formula, _ ) =>
          assertedFormulas += formula; ()
        case CheckSat => Right( !checkValidity( assertedFormulas ++: Sequent() ) )
        case Ask( input ) => input
        case DeclareFun( _ ) | DeclareSort( _ ) | SetLogic( _ ) | SetOption( _, _ ) | Tell( _ ) => ()
      }
    }
  }
}

