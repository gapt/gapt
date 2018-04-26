package gapt.formats.tip

import java.io.IOException

import gapt.expr._
import gapt.formats.lisp._
import gapt.formats.{ InputFile, StringInputFile }
import gapt.proofs.Context
import gapt.utils.{ ExternalProgram, NameGenerator, runProcess }

import scala.collection.mutable

class TipSmtParser {
  var ctx = Context()

  val typeDecls = mutable.Map[String, TBase]()
  val funDecls = mutable.Map[String, Const]()

  def declare( t: TBase ): Unit = typeDecls( t.name ) = t
  def declare( f: Const ): Unit = funDecls( f.name ) = f

  val datatypes = mutable.Buffer[TipDatatype]()
  val functions = mutable.Buffer[TipFun]()
  val assumptions = mutable.Buffer[Formula]()
  val goals = mutable.Buffer[Formula]()

  typeDecls( "Bool" ) = To
  datatypes += TipDatatype( To, Seq( TipConstructor( TopC(), Seq() ), TipConstructor( BottomC(), Seq() ) ) )

  case class TipSmtParserException( message: String ) extends Exception( message )

  private def checkKeywords( keywords: Seq[SExpression] ): Unit = keywords match {
    case Seq( LKeyword( _ ), LSymbol( _ ), rest @ _* ) => checkKeywords( rest )
    case Seq( LKeyword( _ ), rest @ _* ) => checkKeywords( rest )
    case Seq() =>
    case _ => throw TipSmtParserException( "invalid keyword sequence" )
  }

  private object SortDeclaration {
    def unapply( sexps: Seq[SExpression] ): Option[( SExpression, Seq[SExpression], SExpression )] = {
      if ( sexps.size < 2 )
        None
      else
        Some( sexps.head, sexps.tail.init, sexps.last )
    }
  }

  private def declareBaseType( sort: String ) = {
    val baseType = TBase( sort )
    declare( baseType )
    ctx += baseType
  }

  private def parseSortDeclaration( sexps: Seq[SExpression] ): Unit = {

    val SortDeclaration( LSymbol( sort ), keywords, LSymbol( "0" ) ) = sexps

    checkKeywords( keywords )

    declareBaseType( sort )
  }

  private object Datatype {
    def unapply( sexps: Seq[SExpression] ): Option[( SExpression, Seq[SExpression], Seq[SExpression] )] =
      if ( sexps.size < 2 )
        None
      else
        Some(
          sexps.head,
          sexps.tail.takeWhile( !_.isInstanceOf[LList] ),
          sexps.tail.dropWhile( !_.isInstanceOf[LList] ) )
  }

  private object DatatypeDeclaration {
    def unapply( sexps: Seq[SExpression] ): Option[( SExpression, Seq[SExpression], SExpression, Seq[SExpression] )] =
      if ( sexps.size < 2 )
        None
      else
        sexps.last match {
          case LList( LList( expressions @ _* ) ) =>
            val Datatype( typename, keywords, constructors ) = expressions
            Some( sexps.head, keywords, typename, constructors )
          case _ => None
        }
  }

  private def declareDatatype( typename: String, constructors: Seq[SExpression] ): Unit = {
    val t = TBase( typename )
    declare( t )
    val dt = TipDatatype( t, constructors map { parseConstructor( _, t ) } )
    ctx += Context.InductiveType( t, dt.constructors.map( _.constr ): _* )
    datatypes += dt
    dt.constructors foreach { ctr =>
      declare( ctr.constr )
      for ( proj <- ctr.projectors ) {
        declare( proj )
        ctx += proj
      }
    }
  }

  private def parseDatatypeDeclaration( sexps: Seq[SExpression] ): Unit = {

    val DatatypeDeclaration( LList(), keywords, LSymbol( typename ), constructors ) = sexps

    checkKeywords( keywords )

    declareDatatype( typename, constructors )
  }

  private object ConstantDeclaration {
    def unapply( sexps: Seq[SExpression] ): Option[( SExpression, Seq[SExpression], SExpression )] =
      if ( sexps.size < 2 )
        None
      else
        Some( ( sexps.head, sexps.tail.init, sexps.last ) )
  }

  private def declareConstant( constantName: String, typeName: String ): Unit = {
    val c = Const( constantName, typeDecls( typeName ) )
    declare( c )
    ctx += c
  }

  private def parseConstantDeclaration( sexps: Seq[SExpression] ): Unit = {

    val ConstantDeclaration( LSymbol( constantName ), keywords, LSymbol( typeName ) ) = sexps

    checkKeywords( keywords )

    declareConstant( constantName, typeName )
  }

  private object FunctionDeclaration {
    def unapply( sexps: Seq[SExpression] ): Option[( SExpression, Seq[SExpression], SExpression, SExpression )] =
      if ( sexps.size < 3 )
        None
      else
        Some( ( sexps.head, sexps.tail.init.init, sexps.reverse( 1 ), sexps.reverse( 0 ) ) )
  }

  private def declareFunction( functionName: String, argumentTypes: Seq[SExpression], returnType: String ): Unit = {
    val f = Const( functionName, FunctionType(
      typeDecls( returnType ),
      argumentTypes.asInstanceOf[Seq[LSymbol]].map { case LSymbol( argType ) => typeDecls( argType ) } ) )
    declare( f )
    ctx += f
  }

  private def parseFunctionDeclaration( sexps: Seq[SExpression] ): Unit = {

    val FunctionDeclaration( LSymbol( functionName ), keywords, LList( argTypes @ _* ), LSymbol( returnType ) ) = sexps

    checkKeywords( keywords )

    declareFunction( functionName, argTypes, returnType )
  }

  private object FunctionDefinition {
    def unapply( sexps: Seq[SExpression] ): Option[( SExpression, Seq[SExpression], SExpression, SExpression, SExpression )] =
      if ( sexps.size < 4 )
        None
      else
        Some( ( sexps.head, sexps.tail.init.init.init, sexps.reverse( 2 ), sexps.reverse( 1 ), sexps.reverse( 0 ) ) )
  }

  private def defineFunction(
    functionName: String,
    arguments:    Seq[SExpression],
    returnType:   String,
    body:         SExpression ): Unit = {
    val argVars = for (
      LFun( argName, LSymbol( argType ) ) <- arguments
    ) yield Var( argName, typeDecls( argType ) )
    val funConst = Const( functionName, FunctionType( typeDecls( returnType ), argVars.map( _.ty ) ) )
    declare( funConst )
    ctx += funConst
    functions += TipFun(
      funConst,
      parseFunctionBody( body, funConst( argVars: _* ), argVars.map { v => v.name -> v }.toMap ) )
  }

  private def parseFunctionDefinition( sexps: Seq[SExpression] ): Unit = {

    val FunctionDefinition( LSymbol( functionName ), keywords, LList( args @ _* ), LSymbol( retType ), body ) = sexps

    checkKeywords( keywords )

    defineFunction( functionName, args, retType, body )
  }

  private object Formula {
    def unapply( sexps: Seq[SExpression] ): Option[( Seq[SExpression], SExpression )] =
      if ( sexps.size < 1 )
        None
      else
        Some( ( sexps.init, sexps.last ) )
  }

  private def parseAssertion( sexps: Seq[SExpression] ): Unit = {

    val Formula( keywords, formula ) = sexps

    checkKeywords( keywords )

    assumptions += parseExpression( formula, Map() ).asInstanceOf[Formula]
  }

  private def parseGoal( sexps: Seq[SExpression] ): Unit = {

    val Formula( keywords, formula ) = sexps

    checkKeywords( keywords )

    goals += parseExpression( formula, Map() ).asInstanceOf[Formula]
  }

  private val tipExpressionParsers: Map[String, ( Seq[SExpression] ) => Unit] =
    Map(
      ( "declare-sort", parseSortDeclaration( _ ) ),
      ( "declare-datatypes", parseDatatypeDeclaration( _ ) ),
      ( "declare-const", parseConstantDeclaration( _ ) ),
      ( "declare-fun", parseFunctionDeclaration( _ ) ),
      ( "define-fun", parseFunctionDefinition( _ ) ),
      ( "define-fun-rec", parseFunctionDefinition( _ ) ),
      ( "assert", parseAssertion( _ ) ),
      ( "assert-not", parseGoal( _ ) ),
      ( "prove", parseGoal( _ ) ),
      ( "check-sat", ( sexps: Seq[SExpression] ) => () ) )

  def parse( sexp: SExpression ): Unit = sexp match {
    case LFun( head, declaration @ _* ) => tipExpressionParsers( head )( declaration )
  }

  def parseConstructor( sexp: SExpression, ofType: Ty ): TipConstructor = sexp match {
    case LFun( constructorName, LKeyword( _ ), LSymbol( _ ), rest @ _* ) =>
      parseConstructor( LFun( constructorName, rest: _* ), ofType )
    case LFun( constructorName, LKeyword( _ ), rest @ _* ) =>
      parseConstructor( LFun( constructorName, rest: _* ), ofType )

    case LFun( name, fields @ _* ) =>
      val projectors = fields map { parseField( _, ofType ) }
      val fieldTypes = projectors map { _.ty } map { case FunctionType( to, _ ) => to }
      TipConstructor( Const( name, FunctionType( ofType, fieldTypes ) ), projectors )
  }

  def parseField( sexp: SExpression, ofType: Ty ) = sexp match {
    case LFun( projector, LSymbol( typename ) ) =>
      Const( projector, ofType ->: typeDecls( typename ) )
  }

  def parseFunctionBody( sexp: SExpression, lhs: Expr, freeVars: Map[String, Expr] ): Seq[Formula] = sexp match {
    case LFun( "match", LSymbol( varName ), cases @ _* ) =>
      def handleCase( cas: SExpression ): Seq[Formula] = cas match {
        case LFun( "case", LSymbol( "default" ), body ) =>
          val coveredConstructors = cases collect {
            case LFun( "case", LFunOrAtom( constrName, _* ), _ ) if constrName != "default" =>
              funDecls( constrName )
          }
          val missingConstructors = datatypes.find( _.t == freeVars( varName ).ty ).get.constructors.map( _.constr ) diff coveredConstructors
          missingConstructors flatMap { ctr =>
            val FunctionType( _, ts ) = ctr.ty
            val nameGen = new NameGenerator( freeVars.keys )
            val vs = for ( t <- ts ) yield LSymbol( nameGen fresh "x" )
            handleCase( LFun( "case", LFun( ctr.name, vs: _* ), body ) )
          }
        case LFun( "case", LFunOrAtom( constrName, argNames @ _* ), body ) =>
          require(
            freeVars( varName ).isInstanceOf[Var],
            s"${freeVars( varName )} is not a variable" )
          val constr = funDecls( constrName )
          val FunctionType( _, constrArgTypes ) = constr.ty
          require( constrArgTypes.size == argNames.size )
          val args = for ( ( LSymbol( name ), ty ) <- argNames zip constrArgTypes ) yield Var( name, ty )
          val subst = Substitution( freeVars( varName ).asInstanceOf[Var] -> constr( args: _* ) )
          parseFunctionBody(
            body,
            subst( lhs ),
            freeVars.mapValues( subst( _ ) ) ++ args.map { v => v.name -> v } )
      }
      cases flatMap handleCase
    case LFun( "ite", cond, ifTrue, ifFalse ) =>
      parseFunctionBody( ifFalse, lhs, freeVars ).map( -parseExpression( cond, freeVars ) --> _ ) ++
        parseFunctionBody( ifTrue, lhs, freeVars ).map( parseExpression( cond, freeVars ) --> _ )
    case LSymbol( "true" )  => Seq( lhs.asInstanceOf[Formula] )
    case LSymbol( "false" ) => Seq( -lhs )
    case _ =>
      val expr = parseExpression( sexp, freeVars )
      Seq( if ( lhs.ty == To ) lhs <-> expr else lhs === expr )
  }

  def parseExpression( sexp: SExpression, freeVars: Map[String, Expr] ): Expr = sexp match {
    case LSymbol( name ) if freeVars contains name => freeVars( name )
    case LSymbol( "false" )                        => Bottom()
    case LSymbol( "true" )                         => Top()
    case LSymbol( name )                           => funDecls( name )
    case LFun( "forall", LList( varNames @ _* ), formula ) =>
      val vars = for ( LFun( name, LSymbol( typeName ) ) <- varNames ) yield Var( name, typeDecls( typeName ) )
      All.Block( vars, parseExpression( formula, freeVars ++ vars.map { v => v.name -> v } ) )
    case LFun( "exists", LList( varNames @ _* ), formula ) =>
      val vars = for ( LFun( name, LSymbol( typeName ) ) <- varNames ) yield Var( name, typeDecls( typeName ) )
      Ex.Block( vars, parseExpression( formula, freeVars ++ vars.map { v => v.name -> v } ) )
    case LFun( "=", sexps @ _* ) =>
      val exprs = sexps map { parseExpression( _, freeVars ) }
      And( for ( ( a, b ) <- exprs zip exprs.tail )
        yield if ( exprs.head.ty == To ) a <-> b else a === b )
    case LFun( "and", sexps @ _* ) => And( sexps map { parseExpression( _, freeVars ).asInstanceOf[Formula] } )
    case LFun( "or", sexps @ _* )  => Or( sexps map { parseExpression( _, freeVars ).asInstanceOf[Formula] } )
    case LFun( "not", sexp_ )      => Neg( parseExpression( sexp_, freeVars ) )
    case LFun( "=>", sexps @ _* )  => sexps map { parseExpression( _, freeVars ) } reduceRight { _ --> _ }
    case LFun( name, args @ _* ) =>
      funDecls( name )( args map { parseExpression( _, freeVars ) }: _* )
  }

  def toProblem: TipProblem =
    TipProblem(
      ctx,
      typeDecls.values.toSeq diff datatypes.map { _.t }, datatypes,
      funDecls.values.toSeq diff functions.map { _.fun },
      functions,
      assumptions, And( goals ) )
}

object TipSmtParser extends ExternalProgram {
  def parse( tipBench: InputFile ): TipProblem = {
    val tipSmtParser = new TipSmtParser
    SExpressionParser( tipBench ) foreach tipSmtParser.parse
    tipSmtParser.toProblem
  }

  def fixupAndParse( tipBench: InputFile ): TipProblem =
    parse( StringInputFile( runProcess(
      Seq(
        "tip",
        "--type-skolem-conjecture",
        "--commute-match",
        "--lambda-lift", "--axiomatize-lambdas",
        "--monomorphise",
        "--if-to-bool-op",
        "--int-to-nat",
        "--uncurry-theory",
        "--let-lift" ),
      tipBench.read,
      catchStderr = true ) ) )

  val isInstalled =
    try { runProcess( Seq( "tip", "--help" ), "" ); true }
    catch { case _: IOException => false }
}
