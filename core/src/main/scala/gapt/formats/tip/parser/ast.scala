package gapt.formats.tip.parser

import gapt.formats.tip.analysis.SymbolTable

sealed trait TipSmtAst

sealed trait TipSmtCommand

case class TipSmtDatatypesDeclaration(
    datatypes: Seq[TipSmtDatatype] ) extends TipSmtCommand

case class TipSmtAssertion(
    keywords: Seq[TipSmtKeyword],
    expr:     TipSmtExpression ) extends TipSmtCommand

case class TipSmtGoal(
    keywords: Seq[TipSmtKeyword],
    expr:     TipSmtExpression ) extends TipSmtCommand

case class TipSmtConstantDeclaration(
    name:     String,
    keywords: Seq[TipSmtKeyword],
    typ:      TipSmtType ) extends TipSmtCommand

case class TipSmtFunctionDeclaration(
    name:          String,
    keywords:      Seq[TipSmtKeyword],
    argumentTypes: Seq[TipSmtType],
    returnType:    TipSmtType ) extends TipSmtCommand

case class TipSmtMutualRecursiveFunctionDefinition(
    functions: Seq[TipSmtFunctionDefinition] ) extends TipSmtCommand

case class TipSmtSortDeclaration(
    name:     String,
    keywords: Seq[TipSmtKeyword] ) extends TipSmtCommand

case class TipSmtFunctionDefinition(
    name:       String,
    keywords:   Seq[TipSmtKeyword],
    parameters: Seq[TipSmtFormalParameter],
    returnType: TipSmtType,
    body:       TipSmtExpression ) extends TipSmtCommand

case class TipSmtProblem(
    definitions: Seq[TipSmtCommand] ) {
  var symbolTable: Option[SymbolTable] = None
}

case class TipSmtKeyword(
    name:     String,
    argument: Option[String] ) extends TipSmtAst

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

case class TipSmtFormalParameter(
    name: String, typ: TipSmtType ) extends TipSmtAst

case class TipSmtCheckSat() extends TipSmtCommand

case class Datatype( name: String )

sealed trait TipSmtExpression extends TipSmtAst {
  var datatype: Option[Datatype] = None
}

case class TipSmtMatch(
    expr:  TipSmtExpression,
    cases: Seq[TipSmtCase] ) extends TipSmtExpression

case class TipSmtCase(
    pattern: TipSmtPattern,
    expr:    TipSmtExpression )

case class TipSmtIte(
    cond:    TipSmtExpression,
    ifTrue:  TipSmtExpression,
    ifFalse: TipSmtExpression ) extends TipSmtExpression

case class TipSmtDistinct(
    expressions: Seq[TipSmtExpression] ) extends TipSmtExpression

sealed trait TipSmtPattern

case object TipSmtDefault extends TipSmtPattern

case class TipSmtConstructorPattern(
    constructor: TipSmtIdentifier,
    identifiers: Seq[TipSmtIdentifier] ) extends TipSmtPattern

case object TipSmtTrue extends TipSmtExpression

case object TipSmtFalse extends TipSmtExpression

case class TipSmtIdentifier(
    name: String ) extends TipSmtExpression

case class TipSmtForall(
    variables: Seq[TipSmtVariableDecl],
    formula:   TipSmtExpression ) extends TipSmtExpression

case class TipSmtExists(
    variables: Seq[TipSmtVariableDecl],
    formula:   TipSmtExpression ) extends TipSmtExpression

case class TipSmtEq(
    exprs: Seq[TipSmtExpression] ) extends TipSmtExpression

case class TipSmtAnd(
    exprs: Seq[TipSmtExpression] ) extends TipSmtExpression

case class TipSmtOr(
    exprs: Seq[TipSmtExpression] ) extends TipSmtExpression

case class TipSmtNot(
    expr: TipSmtExpression ) extends TipSmtExpression

case class TipSmtImp(
    exprs: Seq[TipSmtExpression] ) extends TipSmtExpression

case class TipSmtFun(
    name:      String,
    arguments: Seq[TipSmtExpression] ) extends TipSmtExpression

case class TipSmtVariableDecl(
    name: String,
    typ:  TipSmtType )

