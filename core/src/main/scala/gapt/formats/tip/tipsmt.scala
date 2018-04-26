package gapt.formats.tip

import java.io.IOException

import gapt.expr._
import gapt.formats.lisp._
import gapt.formats.{ InputFile, StringInputFile }
import gapt.proofs.Context
import gapt.utils.{ ExternalProgram, NameGenerator, runProcess }

import scala.collection.mutable

sealed trait TipSmtAst

case class TipSmtKeyword(
    name:     String,
    argument: Option[String] ) extends TipSmtAst

case class TipSmtSortDeclaration(
    name:     String,
    keywords: Seq[TipSmtKeyword] ) extends TipSmtAst

case class TipSmtConstructor(
    name:     String,
    keywords: Seq[TipSmtKeyword],
    fields:   Seq[TipSmtConstructorField] )

case class TipSmtConstructorField(
    name: String,
    typ:  TipSmtType )

case class TipSmtType(
    typename: String ) extends TipSmtAst

case class TipSmtDatatype(
    name:         String,
    keywords:     Seq[TipSmtKeyword],
    constructors: Seq[TipSmtConstructor] ) extends TipSmtAst

case class TipSmtDatatypesDeclaration(
    datatypes: Seq[TipSmtDatatype] ) extends TipSmtAst

case class TipSmtConstantDeclaration(
    name:     String,
    keywords: Seq[TipSmtKeyword],
    typ:      TipSmtType ) extends TipSmtAst

case class TipSmtFunctionDeclaration(
    name:          String,
    keywords:      Seq[TipSmtKeyword],
    argumentTypes: Seq[TipSmtType],
    returnType:    TipSmtType ) extends TipSmtAst

case class TipSmtFunctionDefinition(
    name:       String,
    keywords:   Seq[TipSmtKeyword],
    parameters: Seq[TipSmtFormalParameter],
    returnType: TipSmtType,
    body:       SExpression ) extends TipSmtAst

case class TipSmtAssertion(
    expr: TipSmtExpression ) extends TipSmtAst

case class TipSmtGoal(
    expr: TipSmtExpression ) extends TipSmtAst

case class TipSmtFormalParameter(
    name: String, typ: TipSmtType )

case class TipSmtExpression(
    keywords: Seq[TipSmtKeyword], expr: SExpression ) extends TipSmtAst

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
  datatypes += TipDatatype(
    To,
    Seq( TipConstructor( TopC(), Seq() ), TipConstructor( BottomC(), Seq() ) ) )

  case class TipSmtParserException(
      message: String ) extends Exception( message )

  private def parseKeywords( sexps: Seq[SExpression] ): Seq[TipSmtKeyword] =
    sexps match {
      case Seq( LKeyword( keyword ), LSymbol( argument ), rest @ _* ) =>
        Seq( TipSmtKeyword( keyword, Some( argument ) ) ) ++
          parseKeywords( rest )
      case Seq( LKeyword( keyword ), kw @ LKeyword( _ ), rest @ _* ) =>
        Seq( TipSmtKeyword( keyword, None ) ) ++ parseKeywords( kw +: rest )
      case Seq( LKeyword( keyword ) ) =>
        Seq( TipSmtKeyword( keyword, None ) )
      case Seq() =>
        Seq()
      case _ => throw TipSmtParserException( "" )
    }

  private def parseSortDeclaration(
    sexps: Seq[SExpression] ): TipSmtSortDeclaration =
    sexps match {
      case Seq( LSymbol( sortName ), rest @ _* ) =>
        if ( rest.isEmpty )
          throw TipSmtParserException( "" )
        rest.last match {
          case LSymbol( "0" ) =>
            TipSmtSortDeclaration( sortName, parseKeywords( rest.init ) )
          case _ => throw new TipSmtParserException( "" )
        }
      case _ => throw new TipSmtParserException( "" )
    }

  private def parseDatatype( sexps: SExpression ): TipSmtDatatype =
    sexps match {
      case LList( LSymbol( datatypeName ), rest @ _* ) =>
        val ( keywords, constructors ) = rest.partition(
          !_.isInstanceOf[LList] )
        TipSmtDatatype(
          datatypeName,
          parseKeywords( keywords ),
          parseConstructors( constructors ) )
      case _ => throw TipSmtParserException( "" )
    }

  private def parseDatatypesDeclaration(
    sexps: Seq[SExpression] ): TipSmtDatatypesDeclaration = sexps match {
    case Seq( LList(), LList( datatypes @ _* ) ) =>
      TipSmtDatatypesDeclaration( datatypes.map { parseDatatype( _ ) } )
    case _ => throw TipSmtParserException( "" )
  }

  private def parseTypename( sexp: SExpression ): TipSmtType = sexp match {
    case LSymbol( typename ) =>
      TipSmtType( typename )
    case _ => throw TipSmtParserException( "" )
  }

  private def parseConstantDeclaration(
    sexps: Seq[SExpression] ): TipSmtConstantDeclaration = sexps match {
    case Seq( LSymbol( constantName ), rest @ _* ) =>
      if ( rest.isEmpty )
        throw TipSmtParserException( "" )
      TipSmtConstantDeclaration(
        constantName,
        parseKeywords( rest.init ),
        parseTypename( rest.last ) )
  }

  private def parseArgumentTypeList( sexp: SExpression ): Seq[TipSmtType] =
    sexp match {
      case LList( types @ _* ) => types map { parseTypename( _ ) }
      case _                   => throw TipSmtParserException( "" )
    }

  private def parseFunctionDeclaration(
    sexps: Seq[SExpression] ): TipSmtFunctionDeclaration = sexps match {
    case Seq( LSymbol( functionName ), rest @ _* ) =>
      if ( rest.size < 2 )
        throw new TipSmtParserException( "" )
      TipSmtFunctionDeclaration(
        functionName,
        parseKeywords( rest.init.init ),
        parseArgumentTypeList( rest.init.last ),
        parseTypename( rest.last ) )
  }

  private def parseFormalParameter(
    sexpr: SExpression ): TipSmtFormalParameter =
    sexpr match {
      case LList( LSymbol( parameter ), paraType ) =>
        TipSmtFormalParameter( parameter, parseTypename( paraType ) )
      case _ => throw TipSmtParserException( "" )
    }

  private def parseFormalParameterList(
    sexp: SExpression ): Seq[TipSmtFormalParameter] = sexp match {
    case LList( parameters @ _* ) =>
      parameters map { parseFormalParameter( _ ) }
    case _ =>
      throw TipSmtParserException( "" )
  }

  private def parseFunctionDefinition(
    sexps: Seq[SExpression] ): TipSmtFunctionDefinition = sexps match {
    case Seq( LSymbol( functionName ), rest @ _* ) =>
      if ( rest.size < 3 )
        throw new TipSmtParserException( "" )
      TipSmtFunctionDefinition(
        functionName,
        parseKeywords( rest.init.init.init ),
        parseFormalParameterList( rest.init.init.last ),
        parseTypename( rest.init.last ),
        rest.last )
  }

  private def parseConstructorFields(
    sexps: Seq[SExpression] ): Seq[TipSmtConstructorField] =
    sexps map { parseConstructorField( _ ) }

  private def parseConstructorField(
    sexps: SExpression ): TipSmtConstructorField = sexps match {
    case LList( LSymbol( fieldName ), fieldType ) =>
      TipSmtConstructorField( fieldName, parseTypename( fieldType ) )
    case _ => throw new TipSmtParserException( "" )
  }

  private def parseConstructors(
    sexps: Seq[SExpression] ): Seq[TipSmtConstructor] =
    sexps map { parseConstructor( _ ) }

  private def parseConstructor( sexp: SExpression ): TipSmtConstructor =
    sexp match {
      case LList( LSymbol( constructorName ), rest @ _* ) =>
        val ( keywords, fields ) = rest partition { !_.isInstanceOf[LList] }
        TipSmtConstructor(
          constructorName,
          parseKeywords( keywords ),
          parseConstructorFields( fields ) )
      case _ => throw TipSmtParserException( "" )
    }

  private def parseTipSmtExpression(
    sexps: Seq[SExpression] ): TipSmtExpression = {
    if ( sexps.isEmpty )
      throw TipSmtParserException( "" )
    TipSmtExpression( parseKeywords( sexps.init ), sexps.last )
  }

  private def parseAssertion( sexps: Seq[SExpression] ): TipSmtAssertion =
    TipSmtAssertion( parseTipSmtExpression( sexps ) )

  private def parseGoal( sexps: Seq[SExpression] ): TipSmtGoal =
    TipSmtGoal( parseTipSmtExpression( sexps ) )

  private def compileSortDeclaration(
    tipSmtSortDeclaration: TipSmtSortDeclaration ): Unit = {

    val TipSmtSortDeclaration( sort, keywords ) = tipSmtSortDeclaration

    declareBaseType( sort )
  }

  private def compileDatatypesDeclaration(
    tipSmtDatatypesDeclaration: TipSmtDatatypesDeclaration ): Unit = {

    val TipSmtDatatypesDeclaration( datatypes ) = tipSmtDatatypesDeclaration

    datatypes map { declareDatatype( _ ) }
  }

  private def compileConstantDeclaration(
    tipSmtConstantDeclaration: TipSmtConstantDeclaration ): Unit = {

    val TipSmtConstantDeclaration(
      constantName, keywords, typ ) = tipSmtConstantDeclaration

    declareConstant( constantName, typ.typename )
  }

  private def compileFunctionDeclaration(
    tipSmtFunctionDeclaration: TipSmtFunctionDeclaration ): Unit = {

    val TipSmtFunctionDeclaration(
      functionName,
      keywords,
      argTypes,
      returnType ) = tipSmtFunctionDeclaration

    declareFunction( functionName, argTypes, returnType )
  }

  private def compileFunctionDefinition(
    tipSmtFunctionDefinition: TipSmtFunctionDefinition ): Unit = {

    val TipSmtFunctionDefinition(
      functionName,
      _,
      formalParameters,
      returnType,
      body ) = tipSmtFunctionDefinition

    defineFunction( functionName, formalParameters, returnType, body )
  }

  private def compileAssertion( tipSmtAssertion: TipSmtAssertion ): Unit = {

    val TipSmtAssertion( TipSmtExpression( _, formula ) ) = tipSmtAssertion

    assumptions += compileExpression( formula, Map() ).asInstanceOf[Formula]
  }

  private def compileGoal( tipSmtGoal: TipSmtGoal ): Unit = {

    val TipSmtGoal( TipSmtExpression( _, formula ) ) = tipSmtGoal

    goals += compileExpression( formula, Map() ).asInstanceOf[Formula]
  }

  private def compileConstructorField(
    field: TipSmtConstructorField, ofType: Ty ): Const =
    Const( field.name, ofType ->: typeDecls( field.typ.typename ) )

  private def compileTipSmtConstructor(
    constructor: TipSmtConstructor, ofType: Ty ): TipConstructor = {
    val destructors = constructor.fields map {
      compileConstructorField( _, ofType )
    }
    val fieldTypes = constructor.fields map { field =>
      typeDecls( field.typ.typename )
    }
    TipConstructor(
      Const( constructor.name, FunctionType( ofType, fieldTypes ) ),
      destructors )
  }

  def compileFunctionBody( sexp: SExpression, lhs: Expr, freeVars: Map[String, Expr] ): Seq[Formula] = sexp match {
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
          compileFunctionBody(
            body,
            subst( lhs ),
            freeVars.mapValues( subst( _ ) ) ++ args.map { v => v.name -> v } )
      }
      cases flatMap handleCase
    case LFun( "ite", cond, ifTrue, ifFalse ) =>
      compileFunctionBody( ifFalse, lhs, freeVars ).map( -compileExpression( cond, freeVars ) --> _ ) ++
        compileFunctionBody( ifTrue, lhs, freeVars ).map( compileExpression( cond, freeVars ) --> _ )
    case LSymbol( "true" )  => Seq( lhs.asInstanceOf[Formula] )
    case LSymbol( "false" ) => Seq( -lhs )
    case _ =>
      val expr = compileExpression( sexp, freeVars )
      Seq( if ( lhs.ty == To ) lhs <-> expr else lhs === expr )
  }

  def compileExpression( sexp: SExpression, freeVars: Map[String, Expr] ): Expr = sexp match {
    case LSymbol( name ) if freeVars contains name => freeVars( name )
    case LSymbol( "false" )                        => Bottom()
    case LSymbol( "true" )                         => Top()
    case LSymbol( name )                           => funDecls( name )
    case LFun( "forall", LList( varNames @ _* ), formula ) =>
      val vars = for ( LFun( name, LSymbol( typeName ) ) <- varNames ) yield Var( name, typeDecls( typeName ) )
      All.Block( vars, compileExpression( formula, freeVars ++ vars.map { v => v.name -> v } ) )
    case LFun( "exists", LList( varNames @ _* ), formula ) =>
      val vars = for ( LFun( name, LSymbol( typeName ) ) <- varNames ) yield Var( name, typeDecls( typeName ) )
      Ex.Block( vars, compileExpression( formula, freeVars ++ vars.map { v => v.name -> v } ) )
    case LFun( "=", sexps @ _* ) =>
      val exprs = sexps map { compileExpression( _, freeVars ) }
      And( for ( ( a, b ) <- exprs zip exprs.tail )
        yield if ( exprs.head.ty == To ) a <-> b else a === b )
    case LFun( "and", sexps @ _* ) => And( sexps map { compileExpression( _, freeVars ).asInstanceOf[Formula] } )
    case LFun( "or", sexps @ _* )  => Or( sexps map { compileExpression( _, freeVars ).asInstanceOf[Formula] } )
    case LFun( "not", sexp_ )      => Neg( compileExpression( sexp_, freeVars ) )
    case LFun( "=>", sexps @ _* )  => sexps map { compileExpression( _, freeVars ) } reduceRight { _ --> _ }
    case LFun( name, args @ _* ) =>
      funDecls( name )( args map { compileExpression( _, freeVars ) }: _* )
  }

  private def declareBaseType( sort: String ) = {
    val baseType = TBase( sort )
    declare( baseType )
    ctx += baseType
  }

  private def declareDatatype( tipSmtDatatype: TipSmtDatatype ): Unit = {
    val t = TBase( tipSmtDatatype.name )
    declare( t )
    val dt = TipDatatype(
      t,
      tipSmtDatatype.constructors.map { compileTipSmtConstructor( _, t ) } )
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

  private def declareConstant(
    constantName: String, typeName: String ): Unit = {
    val c = Const( constantName, typeDecls( typeName ) )
    declare( c )
    ctx += c
  }

  private def declareFunction(
    functionName:  String,
    argumentTypes: Seq[TipSmtType],
    returnType:    TipSmtType ): Unit = {
    val f = Const(
      functionName,
      FunctionType(
        typeDecls( returnType.typename ),
        argumentTypes map { argType => typeDecls( argType.typename ) } ) )
    declare( f )
    ctx += f
  }

  private def defineFunction(
    functionName: String,
    arguments:    Seq[TipSmtFormalParameter],
    returnType:   TipSmtType,
    body:         SExpression ): Unit = {
    val argVars = for (
      TipSmtFormalParameter( argName, argType ) <- arguments
    ) yield Var( argName, typeDecls( argType.typename ) )
    val funConst = Const(
      functionName,
      FunctionType( typeDecls( returnType.typename ), argVars.map( _.ty ) ) )
    declare( funConst )
    ctx += funConst
    functions += TipFun(
      funConst,
      compileFunctionBody(
        body, funConst( argVars: _* ), argVars.map { v => v.name -> v }.toMap ) )
  }

  private val tipExpressionCompilers: Map[String, ( Seq[SExpression] ) => Unit] = Map(
    ( "declare-sort", { sexps =>
      compileSortDeclaration( parseSortDeclaration( sexps ) )
    } ),
    ( "declare-datatypes", { sexps =>
      compileDatatypesDeclaration( parseDatatypesDeclaration( sexps ) )
    } ),
    ( "declare-const", { sexps =>
      compileConstantDeclaration( parseConstantDeclaration( sexps ) )
    } ),
    ( "declare-fun", { sexps =>
      compileFunctionDeclaration( parseFunctionDeclaration( sexps ) )
    } ),
    ( "define-fun", { sexps =>
      compileFunctionDefinition( parseFunctionDefinition( sexps ) )
    } ),
    ( "define-fun-rec", { sexps =>
      compileFunctionDefinition( parseFunctionDefinition( sexps ) )
    } ),
    ( "assert", { sexps =>
      compileAssertion( parseAssertion( sexps ) )
    } ),
    ( "assert-not", { sexps =>
      compileGoal( parseGoal( sexps ) )
    } ),
    ( "prove", { sexps =>
      compileGoal( parseGoal( sexps ) )
    } ),
    ( "check-sat", ( sexps: Seq[SExpression] ) => () ) )

  def parse( sexp: SExpression ): Unit = sexp match {
    case LFun( head, declaration @ _* ) => tipExpressionCompilers( head )( declaration )
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
