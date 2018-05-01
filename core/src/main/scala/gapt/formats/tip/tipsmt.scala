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
    fields:   Seq[TipSmtConstructorField] ) extends TipSmtAst

case class TipSmtConstructorField(
    name: String,
    typ:  TipSmtType ) extends TipSmtAst

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
    body:       TipSmtExpr ) extends TipSmtAst

case class TipSmtAssertion(
    expr: TipSmtExpression ) extends TipSmtAst

case class TipSmtGoal(
    expr: TipSmtExpression ) extends TipSmtAst

case class TipSmtFormalParameter(
    name: String, typ: TipSmtType ) extends TipSmtAst

case class TipSmtExpression(
    keywords: Seq[TipSmtKeyword], expr: TipSmtExpr ) extends TipSmtAst

case object TipSmtCheckSat extends TipSmtAst

sealed trait TipSmtExpr extends TipSmtAst

case class TipSmtMatch(
    expr:  TipSmtExpr,
    cases: Seq[TipSmtCase] ) extends TipSmtExpr

case class TipSmtCase(
    pattern: TipSmtPattern,
    expr:    TipSmtExpr )

case class TipSmtIte(
    cond: TipSmtExpr,
    the:  TipSmtExpr,
    els:  TipSmtExpr ) extends TipSmtExpr

sealed trait TipSmtPattern

case object TipSmtDefault extends TipSmtPattern

case class TipSmtConstructorPattern(
    constructor: TipSmtIdentifier,
    identifiers: Seq[TipSmtIdentifier] ) extends TipSmtPattern

case object TipSmtTrue extends TipSmtExpr

case object TipSmtFalse extends TipSmtExpr

case class TipSmtIdentifier(
    name: String ) extends TipSmtExpr

case class TipSmtForall(
    variables: Seq[TipSmtVariableDecl],
    formula:   TipSmtExpr ) extends TipSmtExpr

case class TipSmtExists(
    variables: Seq[TipSmtVariableDecl],
    formula:   TipSmtExpr ) extends TipSmtExpr

case class TipSmtEq(
    exprs: Seq[TipSmtExpr] ) extends TipSmtExpr

case class TipSmtAnd(
    exprs: Seq[TipSmtExpr] ) extends TipSmtExpr

case class TipSmtOr(
    exprs: Seq[TipSmtExpr] ) extends TipSmtExpr

case class TipSmtNot(
    expr: TipSmtExpr ) extends TipSmtExpr

case class TipSmtImp(
    exprs: Seq[TipSmtExpr] ) extends TipSmtExpr

case class TipSmtFun(
    name:      String,
    arguments: Seq[TipSmtExpr] ) extends TipSmtExpr

case class TipSmtVariableDecl(
    name: String,
    typ:  TipSmtType ) extends TipSmtExpr

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

  /**
   * Parses a sequence of keywords.
   *
   * A keyword sequence is a list of s-expressions of the form:
   * keyword_sequence ::= { keyword [ symbol ] }.
   *
   * @param sexps The keyword sequence.
   * @return A list of parsed keywords.
   */
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
      case _ => throw TipSmtParserException(
        "malformed sequence of keywords: " + sexps )
    }

  /**
   * Parses an smt2 sort declaration.
   *
   * The accepted sort declarations are of the form:
   * sort_declaration ::= sort keyword_sequence num
   * where sort is a symbol, keywords a keyword sequence and num a symbol
   * representing an integer value.
   *
   * @param sexps The elements of the sort declaration.
   * @return A parsed sort declaration.
   */
  private def parseSortDeclaration(
    sexps: Seq[SExpression] ): TipSmtSortDeclaration =
    sexps match {
      case Seq( LSymbol( sortName ), rest @ _* ) =>
        if ( rest.isEmpty )
          throw TipSmtParserException( "" )
        rest.last match {
          case LSymbol( s ) if s forall { _.isDigit } =>
            TipSmtSortDeclaration( sortName, parseKeywords( rest.init ) )
          case _ => throw new TipSmtParserException(
            "malformed sort declaration" )
        }
      case _ => throw new TipSmtParserException( "malformed sort declaration" )
    }

  /**
   * Parses an SMT2 datatype declaration.
   *
   * Accepted datatype declarations are s-expressions of the form:
   * datatype_declaration
   *     ::= type_name keyword_sequence { constructor_declaration }
   * where type_name is a symbol.
   * @param sexps The elements of the datatype declaration.
   * @return A parsed datatype declaration.
   */
  private def parseDatatype( sexps: SExpression ): TipSmtDatatype =
    sexps match {
      case LList( LSymbol( datatypeName ), rest @ _* ) =>
        val ( keywords, constructors ) = rest.partition(
          !_.isInstanceOf[LList] )
        TipSmtDatatype(
          datatypeName,
          parseKeywords( keywords ),
          parseConstructors( constructors ) )
      case _ => throw TipSmtParserException( "malformed datatype expression" )
    }

  /**
   * Parses a sequence of datatype declaration.
   *
   * @param sexps The datatype declarations to be parsed.
   * @return The parsed datatype declarations.
   */
  private def parseDatatypesDeclaration(
    sexps: Seq[SExpression] ): TipSmtDatatypesDeclaration = sexps match {
    case Seq( LList(), LList( datatypes @ _* ) ) =>
      TipSmtDatatypesDeclaration( datatypes.map { parseDatatype( _ ) } )
    case _ => throw TipSmtParserException( "malformed datatype declaration" )
  }

  /**
   * Parses an SMT2 type expression.
   *
   * Accepted type expressions are of the form:
   * type ::= type_name,
   * where type_name is a symbol.
   *
   * @param sexp The type expression to be parsed.
   * @return The parsed type expression.
   */
  private def parseType( sexp: SExpression ): TipSmtType = sexp match {
    case LSymbol( typename ) =>
      TipSmtType( typename )
    case _ => throw TipSmtParserException(
      "malformed type expression: " + sexp )
  }

  /**
   * Parses an SMT2 constant declaration.
   *
   * Accepted constant declarations are of the form:
   * constant_declaration ::= constant_name keyword_sequence type,
   * where constant_name is a symbol.
   *
   * @param sexps The elements of the constant declaration.
   * @return The parsed constant expression.
   */
  private def parseConstantDeclaration(
    sexps: Seq[SExpression] ): TipSmtConstantDeclaration = sexps match {
    case Seq( LSymbol( constantName ), rest @ _* ) =>
      if ( rest.isEmpty )
        throw TipSmtParserException( "malformed constant declaration" )
      TipSmtConstantDeclaration(
        constantName,
        parseKeywords( rest.init ),
        parseType( rest.last ) )
    case _ => throw TipSmtParserException( "malformed constant declaration" )
  }

  /**
   * Parses a parameter type list.
   *
   * Accepted parameter type lists are s-expressions of the form:
   * param_types ::= '(' { type } ')'.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed parameter types.
   */
  private def parseArgumentTypeList( sexp: SExpression ): Seq[TipSmtType] =
    sexp match {
      case LList( types @ _* ) =>
        types map { parseType( _ ) }
      case _ =>
        throw TipSmtParserException( "malformed argument types: " + sexp )
    }

  /**
   * Parses a function declaration.
   *
   * Accepted function declarations are s-expressions of the form:
   * function_declaration ::=
   *   function_name keywords parameter_types ret_type,
   *   ret_type :: = type,
   * where function_name is a symbol.
   *
   * @param sexps The elements of the expression to be parsed.
   * @return The parsed function declaration.
   */
  private def parseFunctionDeclaration(
    sexps: Seq[SExpression] ): TipSmtFunctionDeclaration = sexps match {
    case Seq( LSymbol( functionName ), rest @ _* ) =>
      if ( rest.size < 2 )
        throw new TipSmtParserException( "malformed function declaration" )
      TipSmtFunctionDeclaration(
        functionName,
        parseKeywords( rest.init.init ),
        parseArgumentTypeList( rest.init.last ),
        parseType( rest.last ) )
    case _ => throw TipSmtParserException( "malformed function declaration" )
  }

  /**
   * Parses a formal parameter.
   *
   * Formal parameters are s-expressions of the form:
   * formal_param ::= '(' param_name type ')',
   * param_name   ::= symbol.
   *
   * @param sexpr The expression to be parsed.
   * @return The parsed formal parameter.
   */
  private def parseFormalParameter(
    sexpr: SExpression ): TipSmtFormalParameter =
    sexpr match {
      case LList( LSymbol( parameter ), paraType ) =>
        TipSmtFormalParameter( parameter, parseType( paraType ) )
      case _ => throw TipSmtParserException(
        "malformed formal parameter: " + sexpr )
    }

  /**
   * Parses a formal parameter list.
   *
   * A formal parameter list is an s-expression of the form:
   * formal_param_list ::= '(' formal_param ')'.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed formal parameter list.
   */
  private def parseFormalParameterList(
    sexp: SExpression ): Seq[TipSmtFormalParameter] = sexp match {
    case LList( parameters @ _* ) =>
      parameters map { parseFormalParameter( _ ) }
    case _ =>
      throw TipSmtParserException( "malformed formal parameter list: " + sexp )
  }

  /**
   * Parses a function definition.
   *
   * A function definition is an s-expression of the form:
   * function_definition
   *     ::= function_name keywords formal_param_list ret_type expression,
   * function_name ::= symbol.
   *
   * @param sexps The elements of the expression to be parsed
   * @return The parsed function definition.
   */
  private def parseFunctionDefinition(
    sexps: Seq[SExpression] ): TipSmtFunctionDefinition = sexps match {
    case Seq( LSymbol( functionName ), rest @ _* ) =>
      if ( rest.size < 3 )
        throw new TipSmtParserException( "" )
      TipSmtFunctionDefinition(
        functionName,
        parseKeywords( rest.init.init.init ),
        parseFormalParameterList( rest.init.init.last ),
        parseType( rest.init.last ),
        parseExpr( rest.last ) )
    case _ => throw TipSmtParserException( "malformed function definition" )
  }

  /**
   * Parses a sequence of constructor fields.
   *
   * @param sexps The expressions to be parsed
   * @return The parsed constructor fields
   */
  private def parseConstructorFields(
    sexps: Seq[SExpression] ): Seq[TipSmtConstructorField] =
    sexps map { parseConstructorField( _ ) }

  /**
   * Parses a constructor field.
   *
   * A constructor field is an s-expression of the form:
   * field ::= '(' field_name field_type ')',
   * field_name ::= symbol,
   * field_type ::= type.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed constructor field. Throws an exception if sexp is
   *         not an expression of the form described above.
   */
  private def parseConstructorField(
    sexp: SExpression ): TipSmtConstructorField = sexp match {
    case LList( LSymbol( fieldName ), fieldType ) =>
      TipSmtConstructorField( fieldName, parseType( fieldType ) )
    case _ => throw new TipSmtParserException(
      "malformed constructor field: " + sexp )
  }

  /**
   * Parses a sequence of constructor.
   *
   * @param sexps The expressions to be parsed.
   * @return The parsed constructors. Throws an expression if one of the
   *         expressions is not a constructor.
   */
  private def parseConstructors(
    sexps: Seq[SExpression] ): Seq[TipSmtConstructor] =
    sexps map { parseConstructor( _ ) }

  /**
   * Parses a constructor.
   *
   * A constructor is an expression of the form:
   * constructor ::= constructor_name keyword_sequence { field },
   * constructor_name ::= symbol.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed constructor.
   */
  private def parseConstructor( sexp: SExpression ): TipSmtConstructor =
    sexp match {
      case LList( LSymbol( constructorName ), rest @ _* ) =>
        val ( keywords, fields ) = rest partition { !_.isInstanceOf[LList] }
        TipSmtConstructor(
          constructorName,
          parseKeywords( keywords ),
          parseConstructorFields( fields ) )
      case _ => throw TipSmtParserException( "malformed constructor: " + sexp )
    }

  /**
   * Parses an expression.
   *
   * @param sexps The elements of the expression.
   * @return The parsed expression.
   */
  private def parseTipSmtExpression(
    sexps: Seq[SExpression] ): TipSmtExpression = {
    if ( sexps.isEmpty )
      throw TipSmtParserException( "malformed expression" )
    TipSmtExpression( parseKeywords( sexps.init ), parseExpr( sexps.last ) )
  }

  /**
   * Parses an assertion.
   *
   * @param sexps The elements of the assertion.
   * @return The parsed assertion.
   */
  private def parseAssertion( sexps: Seq[SExpression] ): TipSmtAssertion =
    TipSmtAssertion( parseTipSmtExpression( sexps ) )

  private def parseGoal( sexps: Seq[SExpression] ): TipSmtGoal =
    TipSmtGoal( parseTipSmtExpression( sexps ) )

  def parseIte( sexp: SExpression ): TipSmtIte = sexp match {
    case LFun( "ite", cond, the, els ) =>
      TipSmtIte( parseExpr( cond ), parseExpr( the ), parseExpr( els ) )
    case _ => throw TipSmtParserException( "malformed ite-expression: " + sexp )
  }

  def parseMatch( sexp: SExpression ): TipSmtMatch = sexp match {
    case LFun( "match", expr, cases @ _* ) =>
      TipSmtMatch( parseExpr( expr ), cases map { parseCase( _ ) } )
    case _ => throw TipSmtParserException(
      "malformed match-expression: " + sexp )
  }

  def parseCase( sexp: SExpression ): TipSmtCase = sexp match {
    case LFun( "case", pattern, expr ) =>
      TipSmtCase( parsePattern( pattern ), parseExpr( expr ) )
    case _ => throw TipSmtParserException(
      "malformed case-expression: " + sexp )
  }

  def parsePattern( sexp: SExpression ): TipSmtPattern = sexp match {
    case LSymbol( "default" ) =>
      TipSmtDefault
    case p @ LSymbol( _ ) =>
      TipSmtConstructorPattern( parseTipSmtIdentifier( p ), Seq() )
    case LFun( constructor, identifiers @ _* ) =>
      TipSmtConstructorPattern(
        TipSmtIdentifier( constructor ),
        identifiers map { parseTipSmtIdentifier( _ ) } )
    case _ => throw TipSmtParserException( "malformed pattern: " + sexp )
  }

  def parseTipSmtIdentifier(
    sexp: SExpression ): TipSmtIdentifier = sexp match {
    case LSymbol( identifier ) =>
      TipSmtIdentifier( identifier )
    case _ =>
      throw TipSmtParserException( "malformed identifier: " + sexp )
  }

  def parseExpr( sexp: SExpression ): TipSmtExpr = sexp match {
    case LFun( "match", _* ) =>
      parseMatch( sexp )
    case LFun( "ite", _* ) =>
      parseIte( sexp )
    case LSymbol( "false" ) =>
      TipSmtFalse
    case LSymbol( "true" ) =>
      TipSmtTrue
    case LFun( "forall", LList( variables @ _* ), formula ) =>
      TipSmtForall(
        variables map { parseTipSmtVarDecl( _ ) },
        parseExpr( formula ) )
    case LFun( "exists", LList( variables @ _* ), formula ) =>
      TipSmtExists(
        variables map { parseTipSmtVarDecl( _ ) },
        parseExpr( formula ) )
    case LFun( "and", exprs @ _* ) =>
      TipSmtAnd( exprs map { parseExpr( _ ) } )
    case LFun( "or", exprs @ _* ) =>
      TipSmtOr( exprs map { parseExpr( _ ) } )
    case LFun( "=", exprs @ _* ) =>
      TipSmtEq( exprs map { parseExpr( _ ) } )
    case LFun( "=>", exprs @ _* ) =>
      TipSmtImp( exprs map { parseExpr( _ ) } )
    case LSymbol( name ) =>
      TipSmtIdentifier( name )
    case LFun( name, args @ _* ) =>
      TipSmtFun( name, args map { parseExpr( _ ) } )
    case _ => throw TipSmtParserException( "malformed expression: " + sexp )
  }

  def parseTipSmtVarDecl( sexp: SExpression ): TipSmtVariableDecl = sexp match {
    case LList( LSymbol( variableName ), variableType ) =>
      TipSmtVariableDecl( variableName, parseType( variableType ) )
    case _ =>
      throw TipSmtParserException( "malformed variable declaration: " + sexp )
  }

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
      constantName, _, typ ) = tipSmtConstantDeclaration

    val c = Const( constantName, typeDecls( typ.typename ) )
    declare( c )
    ctx += c
  }

  private def compileFunctionDeclaration(
    tipSmtFunctionDeclaration: TipSmtFunctionDeclaration ): Unit = {

    val TipSmtFunctionDeclaration(
      functionName,
      _,
      argumentTypes,
      returnType ) = tipSmtFunctionDeclaration

    val f = Const(
      functionName,
      FunctionType(
        typeDecls( returnType.typename ),
        argumentTypes map { argType => typeDecls( argType.typename ) } ) )
    declare( f )
    ctx += f
  }

  private def compileFunctionDefinition(
    tipSmtFunctionDefinition: TipSmtFunctionDefinition ): Unit = {

    val TipSmtFunctionDefinition(
      functionName,
      _,
      formalParameters,
      returnType,
      body ) = tipSmtFunctionDefinition

    val argVars = for (
      TipSmtFormalParameter( argName, argType ) <- formalParameters
    ) yield Var( argName, typeDecls( argType.typename ) )

    val funConst = Const(
      functionName,
      FunctionType( typeDecls( returnType.typename ), argVars.map( _.ty ) ) )

    declare( funConst )
    ctx += funConst
    functions += TipFun(
      funConst,
      compileFunctionBody(
        body,
        funConst( argVars: _* ),
        argVars.map { v => v.name -> v }.toMap ) )
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

  def compileFunctionBody(
    sexp:     TipSmtExpr,
    lhs:      Expr,
    freeVars: Map[String, Expr] ): Seq[Formula] = sexp match {
    case TipSmtMatch( TipSmtIdentifier( varName ), cases ) =>

      def handleCase( cas: TipSmtCase ): Seq[Formula] = cas match {
        case TipSmtCase( TipSmtDefault, body ) =>
          val coveredConstructors = cases collect {
            case TipSmtCase( TipSmtConstructorPattern( constr, Seq() ), _ ) =>
              funDecls( constr.name )
          }
          val missingConstructors = datatypes.find(
            _.t == freeVars( varName ).ty ).
            get.
            constructors.
            map( _.constr ) diff coveredConstructors

          missingConstructors flatMap { ctr =>
            val FunctionType( _, ts ) = ctr.ty
            val nameGen = new NameGenerator( freeVars.keys )
            val newVariables = for ( t <- ts ) yield nameGen fresh "x"
            handleCase(
              TipSmtCase(
                TipSmtConstructorPattern(
                  TipSmtIdentifier( ctr.name ),
                  newVariables map { TipSmtIdentifier( _ ) } ), body ) )
          }

        case TipSmtCase( TipSmtConstructorPattern( constructor, arguments ), body ) =>

          require(
            freeVars( varName ).isInstanceOf[Var],
            s"${freeVars( varName )} is not a variable" )

          val constr = funDecls( constructor.name )
          val FunctionType( _, constrArgTypes ) = constr.ty

          require( constrArgTypes.size == arguments.size )

          val args = for {
            ( name, ty ) <- arguments.map( _.name ) zip constrArgTypes
          } yield Var( name, ty )

          val subst = Substitution(
            freeVars( varName ).asInstanceOf[Var] -> constr( args: _* ) )

          compileFunctionBody(
            body,
            subst( lhs ),
            freeVars.mapValues( subst( _ ) ) ++ args.map { v => v.name -> v } )
      }
      cases flatMap handleCase

    case TipSmtIte( cond, ifTrue, ifFalse ) =>
      compileFunctionBody( ifFalse, lhs, freeVars ).map( -compileExpression( cond, freeVars ) --> _ ) ++
        compileFunctionBody( ifTrue, lhs, freeVars ).map( compileExpression( cond, freeVars ) --> _ )

    case TipSmtTrue  => Seq( lhs.asInstanceOf[Formula] )
    case TipSmtFalse => Seq( -lhs )
    case _ =>
      val expr = compileExpression( sexp, freeVars )
      Seq( if ( lhs.ty == To ) lhs <-> expr else lhs === expr )
  }

  def compileExpression(
    expr: TipSmtExpr, freeVars: Map[String, Expr] ): Expr = expr match {
    case TipSmtIdentifier( name ) if freeVars contains name => freeVars( name )
    case TipSmtFalse                                        => Bottom()
    case TipSmtTrue                                         => Top()
    case TipSmtIdentifier( name )                           => funDecls( name )

    case TipSmtForall( variables, formula ) =>
      val vars = variables map {
        case TipSmtVariableDecl( name, typ ) =>
          Var( name, typeDecls( typ.typename ) )
      }
      All.Block(
        vars,
        compileExpression(
          formula,
          freeVars ++ vars.map { v => v.name -> v } ) )

    case TipSmtExists( variables, formula ) =>
      val vars = variables map {
        case TipSmtVariableDecl( name, typ ) =>
          Var( name, typeDecls( typ.typename ) )
      }
      Ex.Block(
        vars,
        compileExpression(
          formula,
          freeVars ++ vars.map { v => v.name -> v } ) )

    case TipSmtEq( eqs ) =>
      val exprs = eqs map { compileExpression( _, freeVars ) }
      And( for ( ( a, b ) <- exprs zip exprs.tail )
        yield if ( exprs.head.ty == To ) a <-> b else a === b )

    case TipSmtAnd( exprs ) =>
      And(
        exprs map { compileExpression( _, freeVars ).asInstanceOf[Formula] } )

    case TipSmtOr( exprs ) =>
      Or(
        exprs map { compileExpression( _, freeVars ).asInstanceOf[Formula] } )

    case TipSmtNot( expr ) =>
      Neg( compileExpression( expr, freeVars ) )

    case TipSmtImp( exprs ) =>
      exprs map { compileExpression( _, freeVars ) } reduceRight { _ --> _ }

    case TipSmtFun( name, args ) =>
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
    case LFun( head, declaration @ _* ) =>
      tipExpressionCompilers( head )( declaration )
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

  def parse( input: String ): TipProblem = {
    parse( StringInputFile( input ) )
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
