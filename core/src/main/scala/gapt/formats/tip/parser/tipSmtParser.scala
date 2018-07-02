package gapt.formats.tip.parser

import gapt.formats.InputFile
import gapt.formats.StringInputFile
import gapt.formats.lisp.LFun
import gapt.formats.lisp.LKeyword
import gapt.formats.lisp.LList
import gapt.formats.lisp.LSymbol
import gapt.formats.lisp.SExpression
import gapt.formats.lisp.SExpressionParser

case class TipSmtParserException(
    message: String ) extends Exception( message )

object TipSmtParser {

  /**
   * Parses a TIP problem.
   *
   * @param input The input to be parsed.
   * @return The parsed TIP problem.
   */
  def parse( input: InputFile ): TipSmtProblem = {
    parse( SExpressionParser( input ) )
  }

  /**
   * Parses a TIP problem.
   *
   * @param input The input to be parsed.
   * @return The parsed TIP problem.
   */
  def parse( input: String ): TipSmtProblem = {
    parse( StringInputFile( input ) )
  }

  /**
   * Parses a TIP problem.
   *
   * A tip problem consists of a sequence of s-expressions. Each of these
   * s-expressions represents a command.
   *
   * @param sexps The expressions to be parsed.
   * @return The parsed TIP problem.
   */
  def parse( sexps: Seq[SExpression] ): TipSmtProblem = {
    TipSmtProblem( sexps map { parseCommand } )
  }

  /**
   * Parses a command expression.
   *
   * A command expression is either a sort declaration, a datatypes
   * declaration, a constant declaration, a function declaration, a function
   * definition, an assertion, a goal, or a check sat expression.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed command.
   */
  def parseCommand( sexp: SExpression ): TipSmtCommand = {
    sexp match {
      case LFun( head, _* ) =>
        head match {
          case "declare-sort" =>
            parseSortDeclaration( sexp )
          case "declare-datatypes" =>
            parseDatatypesDeclaration( sexp )
          case "declare-const" =>
            parseConstantDeclaration( sexp )
          case "declare-fun" =>
            parseFunctionDeclaration( sexp )
          case "define-fun" | "define-fun-rec" =>
            parseFunctionDefinition( sexp )
          case "define-funs-rec" =>
            parseMutuallyRecursiveFunctionDefinition( sexp )
          case "assert" =>
            parseAssertion( sexp )
          case "prove" | "assert-not" =>
            parseGoal( sexp )
          case "check-sat" =>
            parseCheckSat( sexp )
          case _ => throw TipSmtParserException(
            "unknown head symbol: " + head )
        }
    }
  }

  /**
   * Parses a check-sat expression.
   *
   * A check-sat expression is an s-expression of the form:
   * check_sat_expr ::= '(' "check-sat" ')'.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed check-sat expression.
   */
  private def parseCheckSat( sexp: SExpression ): TipSmtCheckSat = {
    sexp match {
      case LFun( "check-sat" ) =>
        TipSmtCheckSat()
      case _ => throw TipSmtParserException( "malformed check-sat expression" )
    }
  }

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
   * sort_declaration ::= '(' "declare-sort" sort_name keyword_sequence num ')',
   * sort_name ::= symbol,
   * where num is a symbol representing an integer value.
   *
   * @param sexp The expression to be parsed.
   * @return A parsed sort declaration.
   */
  private def parseSortDeclaration(
    sexp: SExpression ): TipSmtSortDeclaration =
    sexp match {
      case LFun( "declare-sort", LSymbol( sortName ), rest @ _* ) =>
        if ( rest.isEmpty )
          throw TipSmtParserException( "" )
        rest.last match {
          case LSymbol( s ) if s forall { _.isDigit } =>
            TipSmtSortDeclaration( sortName, parseKeywords( rest.init ) )
          case _ => throw TipSmtParserException(
            "malformed sort declaration" )
        }
      case _ => throw TipSmtParserException( "malformed sort declaration" )
    }

  /**
   * Parses an SMT2 datatype declaration.
   *
   * Accepted datatype declarations are s-expressions of the form:
   * datatype_declaration
   *     ::= type_name keyword_sequence { constructor_declaration }
   * where type_name is a symbol.
   * @param sexp The expression to be parsed.
   * @return A parsed datatype declaration.
   */
  private def parseDatatype( sexp: SExpression ): TipSmtDatatype =
    sexp match {
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
   * Parses a datatypes declaration.
   *
   * A datatypes declaration is of the form:
   * datatypes_declaration ::= '(' "declare-datatypes" '(' ')' { datatype } ')'.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed datatype declarations.
   */
  private def parseDatatypesDeclaration(
    sexp: SExpression ): TipSmtDatatypesDeclaration = sexp match {
    case LFun( "declare-datatypes", LList(), LList( datatypes @ _* ) ) =>
      TipSmtDatatypesDeclaration( datatypes.map { parseDatatype } )
    case _ => throw TipSmtParserException( "malformed datatypes declaration" )
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
   * constant_declaration
   *     ::= '(' "declare-const" constant_name keyword_sequence type ')',
   * where constant_name is a symbol.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed constant expression.
   */
  private def parseConstantDeclaration(
    sexp: SExpression ): TipSmtConstantDeclaration = sexp match {
    case LFun( "declare-const", LSymbol( constantName ), rest @ _* ) =>
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
        types map { parseType }
      case _ =>
        throw TipSmtParserException( "malformed argument types: " + sexp )
    }

  /**
   * Parses a function declaration.
   *
   * Accepted function declarations are s-expressions of the form:
   * function_declaration ::=
   *   '(' "declare-fun" function_name keywords parameter_types ret_type ')',
   *   ret_type :: = type,
   * where function_name is a symbol.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed function declaration.
   */
  private def parseFunctionDeclaration(
    sexp: SExpression ): TipSmtFunctionDeclaration = sexp match {
    case LFun( "declare-fun", LSymbol( functionName ), rest @ _* ) =>
      if ( rest.size < 2 )
        throw TipSmtParserException( "malformed function declaration" )
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
      parameters map { parseFormalParameter }
    case _ =>
      throw TipSmtParserException( "malformed formal parameter list: " + sexp )
  }

  /**
   * Parses a function definition.
   *
   * A function definition is an s-expression of the form:
   * function_definition ::= '(' "define-fun" function_name keywords
   * formal_param_list ret_type expression ')',
   * function_name ::= symbol.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed function definition.
   */
  private def parseFunctionDefinition(
    sexp: SExpression ): TipSmtFunctionDefinition = sexp match {
    case LFun(
      "define-fun" | "define-fun-rec", LSymbol( functionName ), rest @ _*
      ) if rest.size >= 3 =>
      TipSmtFunctionDefinition(
        functionName,
        parseKeywords( rest.init.init.init ),
        parseFormalParameterList( rest.init.init.last ),
        parseType( rest.init.last ),
        parseExpression( rest.last ) )
    case _ => throw TipSmtParserException( "malformed function definition" )
  }

  /**
   * Parses a function definition of mutually recursive functions.
   *
   * A mutually recursive functions definition is an expression of the form:
   * mutuall_recursive_functions_definition ::=
   *  '(' "define-funs-rec" '(' { signature } ')' '(' { definition } ')' ')',
   *  where
   *  signature  ::= '(' function_name keywords formal_param_list ret_type ')',
   *  definition ::= expression,
   *
   * @param expression The expression to be parsed.
   * @return The parsed mutually recursive functions definition.
   */
  private def parseMutuallyRecursiveFunctionDefinition(
    expression: SExpression ): TipSmtMutualRecursiveFunctionDefinition = {
    def parseFunctionSignature( sexp: SExpression ): ( //
    String, Seq[TipSmtKeyword], Seq[TipSmtFormalParameter], TipSmtType ) = {
      sexp match {
        case LFun( functionName, rest @ _* ) if rest.size >= 2 =>
          (
            functionName,
            parseKeywords( rest.init.init ),
            parseFormalParameterList( rest.init.last ),
            parseType( rest.last ) )
        case _ => throw TipSmtParserException(
          "malformed function signature: " + sexp )
      }
    }
    expression match {
      case LFun(
        "define-funs-rec", LList( signatures @ _* ), LList( definitions @ _* )
        ) if ( signatures.size == definitions.size ) =>
        val functions =
          signatures
            .map { parseFunctionSignature }
            .zip( definitions.map { parseExpression } )
            .map {
              case ( //
                ( functionName, keywords, formalParameters, returnType ),
                body ) =>
                TipSmtFunctionDefinition(
                  functionName, keywords, formalParameters, returnType, body )
            }
        TipSmtMutualRecursiveFunctionDefinition( functions )
      case _ => throw TipSmtParserException(
        "malformed mutual recursive functions definition" )
    }
  }

  /**
   * Parses a sequence of constructor fields.
   *
   * @param sexps The expressions to be parsed
   * @return The parsed constructor fields
   */
  private def parseConstructorFields(
    sexps: Seq[SExpression] ): Seq[TipSmtConstructorField] =
    sexps map { parseConstructorField }

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
    case _ => throw TipSmtParserException(
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
    sexps map { parseConstructor }

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
   * Parses an assertion.
   *
   * An assertion is an s-expression of the form:
   * assertion ::= '(' "assert" keyword_sequence expression ')'.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed assertion.
   */
  private def parseAssertion(
    sexp: SExpression ): TipSmtAssertion = sexp match {
    case LFun( "assert", rest @ _* ) if rest.nonEmpty =>
      TipSmtAssertion(
        parseKeywords( rest.init ),
        parseExpression( rest.last ) )
    case _ => throw TipSmtParserException( "malformed assertion" )
  }

  /**
   * Parses a goal.
   *
   * A goal is an s-expression of the form:
   * goal ::= '(' ("prove | "assert-not") keyword_sequence expression ')'.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed goal.
   */
  private def parseGoal(
    sexp: SExpression ): TipSmtGoal = sexp match {
    case LFun( "prove" | "assert-not", rest @ _* ) if rest.nonEmpty =>
      TipSmtGoal(
        parseKeywords( rest.init ),
        parseExpression( rest.last ) )
    case _ => throw TipSmtParserException( "malformed assertion" )
  }

  /**
   * Parses an if-then-else expression.
   *
   * An if-then-else expression is an s-expression of the form:
   * ite_expr ::= '(' "ite" expr expr expr ')'.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed if-then-else expression.
   */
  def parseIte( sexp: SExpression ): TipSmtIte = sexp match {
    case LFun( "ite", cond, the, els ) =>
      TipSmtIte(
        parseExpression( cond ),
        parseExpression( the ),
        parseExpression( els ) )
    case _ => throw TipSmtParserException( "malformed ite-expression: " + sexp )
  }

  /**
   * Parses a match expression.
   *
   * A match expression is an s-expression of the form:
   * match_expr ::= '(' "match" symbol { case_expr } ')'.
   *
   * @param sexp The expression to be parsed
   * @return The parsed match expression.
   */
  def parseMatch( sexp: SExpression ): TipSmtMatch = sexp match {
    case LFun( "match", expr, cases @ _* ) =>
      TipSmtMatch( parseExpression( expr ), cases map { parseCase } )
    case _ => throw TipSmtParserException(
      "malformed match-expression: " + sexp )
  }

  /**
   * Parses a case expression.
   *
   * A case expression is an s-expression of the form:
   * case_expr ::= '(' "case" pattern expression ')'.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed case expression.
   */
  def parseCase( sexp: SExpression ): TipSmtCase = sexp match {
    case LFun( "case", pattern, expr ) =>
      TipSmtCase( parsePattern( pattern ), parseExpression( expr ) )
    case _ => throw TipSmtParserException(
      "malformed case-expression: " + sexp )
  }

  /**
   * Parses a pattern.
   *
   * A pattern is an s-expression of the form:
   * pattern ::= "default" | symbol | '(' symbol { symbol } ')'.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed pattern.
   */
  def parsePattern( sexp: SExpression ): TipSmtPattern = sexp match {
    case LSymbol( "default" ) =>
      TipSmtDefault
    case p @ LSymbol( _ ) =>
      TipSmtConstructorPattern( parseTipSmtIdentifier( p ), Seq() )
    case LFun( constructor, identifiers @ _* ) =>
      TipSmtConstructorPattern(
        TipSmtIdentifier( constructor ),
        identifiers map { parseTipSmtIdentifier } )
    case _ => throw TipSmtParserException( "malformed pattern: " + sexp )
  }

  /**
   * Parses an identifier.
   *
   * An identifier is a symbol.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed identifier.
   */
  def parseTipSmtIdentifier(
    sexp: SExpression ): TipSmtIdentifier = sexp match {
    case LSymbol( identifier ) =>
      TipSmtIdentifier( identifier )
    case _ =>
      throw TipSmtParserException( "malformed identifier: " + sexp )
  }

  /**
   * Parses an expression.
   *
   * An expression is an s-expression of the form:
   * expression ::= true
   * | false
   * | ite_expr
   * | match_expr
   * | forall_expr
   * | exists_expr
   * | '(' "or" expression expression ')'
   * | '(' "and" expression expression ')'
   * | '(' "=>" expression expression ')'
   * | '(' "=" expression expression ')'
   * | identifier
   * | function_call,
   * function_call ::= '(' function_name { expression } ')',
   * function_name ::= symbol.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed expression.
   */
  def parseExpression( sexp: SExpression ): TipSmtExpression = sexp match {
    case LFun( "match", _* ) =>
      parseMatch( sexp )
    case LFun( "ite", _* ) =>
      parseIte( sexp )
    case LSymbol( "false" ) =>
      TipSmtFalse
    case LSymbol( "true" ) =>
      TipSmtTrue
    case expr @ LFun( "forall", _* ) =>
      parseForallExpression( expr )
    case expr @ LFun( "exists", _* ) =>
      parseExistsExpression( expr )
    case LFun( "and", exprs @ _* ) =>
      TipSmtAnd( exprs map { parseExpression } )
    case LFun( "or", exprs @ _* ) =>
      TipSmtOr( exprs map { parseExpression } )
    case LFun( "=", exprs @ _* ) =>
      TipSmtEq( exprs map { parseExpression } )
    case LFun( "=>", exprs @ _* ) =>
      TipSmtImp( exprs map { parseExpression } )
    case expr @ LFun( "not", _* ) =>
      parseNotExpression( expr )
    case LFun( "distinct", exprs @ _* ) =>
      TipSmtDistinct( exprs.map { parseExpression } )
    case LSymbol( name ) =>
      TipSmtIdentifier( name )
    case LFun( name, args @ _* ) =>
      TipSmtFun( name, args map { parseExpression } )
    case _ => throw TipSmtParserException( "malformed expression: " + sexp )
  }

  private def parseNotExpression( sexp: SExpression ): TipSmtNot =
    sexp match {
      case LFun( "not", expr ) =>
        TipSmtNot( parseExpression( expr ) )
      case _ => throw TipSmtParserException(
        "malformed not-expression: " + sexp )
    }

  private def parseExistsExpression( sexp: SExpression ): TipSmtExists =
    sexp match {
      case LFun( "exists", LList( variables @ _* ), formula ) =>
        TipSmtExists(
          variables map { parseTipSmtVarDecl },
          parseExpression( formula ) )
      case _ => throw TipSmtParserException(
        "malformed exists-expression: " + sexp )
    }

  private def parseForallExpression( sexp: SExpression ): TipSmtForall =
    sexp match {
      case LFun( "forall", LList( variables @ _* ), formula ) =>
        TipSmtForall(
          variables map { parseTipSmtVarDecl },
          parseExpression( formula ) )
      case _ => throw TipSmtParserException(
        "malformed forall expression: " + sexp )
    }

  /**
   * Parses a variable declaration.
   *
   * A variable declaration is an s-expression of the form:
   * variable_declaration ::= '(' symbol type ')'.
   *
   * @param sexp The expression to be parsed.
   * @return The parsed variable declaration.
   */
  def parseTipSmtVarDecl( sexp: SExpression ): TipSmtVariableDecl = sexp match {
    case LList( LSymbol( variableName ), variableType ) =>
      TipSmtVariableDecl( variableName, parseType( variableType ) )
    case _ =>
      throw TipSmtParserException( "malformed variable declaration: " + sexp )
  }
}

