package gapt.formats.tip.compiler

import gapt.expr.Abs
import gapt.expr.App
import gapt.expr.Apps
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.ReductionRule
import gapt.expr.Var
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Bottom
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.expr.formula.constants.BottomC
import gapt.expr.formula.constants.TopC
import gapt.expr.ty.FunctionType
import gapt.expr.ty.TBase
import gapt.expr.ty.TVar
import gapt.expr.ty.To
import gapt.expr.ty.Ty
import gapt.expr.util.syntacticMatching
import gapt.formats.tip.TipConstructor
import gapt.formats.tip.TipDatatype
import gapt.formats.tip.TipFun
import gapt.formats.tip.TipProblem
import gapt.formats.tip.analysis.SymbolTable
import gapt.formats.tip.decoration.ReconstructDatatypes
import gapt.formats.tip.parser.Datatype
import gapt.formats.tip.parser.TipSmtAnd
import gapt.formats.tip.parser.TipSmtAssertion
import gapt.formats.tip.parser.TipSmtCase
import gapt.formats.tip.parser.TipSmtCheckSat
import gapt.formats.tip.parser.TipSmtConstantDeclaration
import gapt.formats.tip.parser.TipSmtConstructor
import gapt.formats.tip.parser.TipSmtConstructorField
import gapt.formats.tip.parser.TipSmtConstructorPattern
import gapt.formats.tip.parser.TipSmtDatatype
import gapt.formats.tip.parser.TipSmtDatatypesDeclaration
import gapt.formats.tip.parser.TipSmtDistinct
import gapt.formats.tip.parser.TipSmtEq
import gapt.formats.tip.parser.TipSmtExists
import gapt.formats.tip.parser.TipSmtExpression
import gapt.formats.tip.parser.TipSmtFalse
import gapt.formats.tip.parser.TipSmtForall
import gapt.formats.tip.parser.TipSmtFormalParameter
import gapt.formats.tip.parser.TipSmtFun
import gapt.formats.tip.parser.TipSmtFunctionDeclaration
import gapt.formats.tip.parser.TipSmtFunctionDefinition
import gapt.formats.tip.parser.TipSmtGoal
import gapt.formats.tip.parser.TipSmtIdentifier
import gapt.formats.tip.parser.TipSmtImp
import gapt.formats.tip.parser.TipSmtIte
import gapt.formats.tip.parser.TipSmtMatch
import gapt.formats.tip.parser.TipSmtMutualRecursiveFunctionDefinition
import gapt.formats.tip.parser.TipSmtNot
import gapt.formats.tip.parser.TipSmtOr
import gapt.formats.tip.parser.TipSmtParserException
import gapt.formats.tip.parser.TipSmtProblem
import gapt.formats.tip.parser.TipSmtSortDeclaration
import gapt.formats.tip.parser.TipSmtTrue
import gapt.formats.tip.parser.TipSmtType
import gapt.formats.tip.parser.TipSmtVariableDecl
import gapt.formats.tip.transformation.desugarDistinctExpressions
import gapt.formats.tip.transformation.eliminateBooleanConstants
import gapt.formats.tip.transformation.eliminateRedundantQuantifiers
import gapt.formats.tip.transformation.expandConstructorMatchExpressions
import gapt.formats.tip.transformation.expandDefaultPatterns
import gapt.formats.tip.transformation.expandVariableMatchExpressions
import gapt.formats.tip.transformation.moveUniversalQuantifiersInwards
import gapt.formats.tip.transformation.toOuterConditionalNormalForm
import gapt.formats.tip.transformation.useDefiningFormulas
import gapt.proofs.context.Context
import gapt.proofs.context.facet.StructurallyInductiveTypes
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.PrimitiveRecursiveFunction
import gapt.utils.NameGenerator
import gapt.proofs.context.update.ReductionRuleUpdate.reductionRuleAsReductionRuleUpdate

import scala.collection.mutable

class TipSmtToTipProblemCompiler( var problem: TipSmtProblem ) {

  problem = problem >>: ( desugarDistinctExpressions ->>: expandDefaultPatterns )

  ( new ReconstructDatatypes( problem ) )()
  problem.symbolTable = Some( SymbolTable( problem ) )

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

  private def compileSortDeclaration(
    tipSmtSortDeclaration: TipSmtSortDeclaration ): Unit = {

    val TipSmtSortDeclaration( sort, keywords ) = tipSmtSortDeclaration

    declareBaseType( sort )
  }

  private def compileDatatypesDeclaration(
    tipSmtDatatypesDeclaration: TipSmtDatatypesDeclaration ): Unit = {

    val TipSmtDatatypesDeclaration( datatypes ) = tipSmtDatatypesDeclaration

    datatypes foreach { declareDatatype }
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
    val functionConstant = toFunctionConstant( tipSmtFunctionDeclaration )
    declare( functionConstant )
    ctx += functionConstant
  }

  private def toFunctionConstant(
    functionDeclaration: TipSmtFunctionDeclaration ): Const =
    toFunctionConstant(
      functionDeclaration.name,
      functionDeclaration.argumentTypes,
      functionDeclaration.returnType )

  private def toFunctionConstant(
    functionDefinition: TipSmtFunctionDefinition ): Const =
    toFunctionConstant(
      functionDefinition.name,
      functionDefinition.parameters map { _.typ },
      functionDefinition.returnType )

  private def toFunctionConstant(
    functionName:  String,
    argumentTypes: Seq[TipSmtType],
    returnType:    TipSmtType ): Const =
    Const(
      functionName,
      FunctionType(
        typeDecls( returnType.typename ),
        argumentTypes map { argType => typeDecls( argType.typename ) } ) )

  private def declareFunction(
    tipSmtFunctionDefinition: TipSmtFunctionDefinition ): Unit = {
    val functionConstant = toFunctionConstant( tipSmtFunctionDefinition )
    declare( functionConstant )
    ctx += functionConstant
  }

  private def compileFunctionDefinition(
    functionDefinition: TipSmtFunctionDefinition ): Unit = {

    val formalParameters: Seq[Var] = for (
      TipSmtFormalParameter( argName, argType ) <- functionDefinition.parameters
    ) yield Var( argName, typeDecls( argType.typename ) )

    val functionConstant = toFunctionConstant( functionDefinition )

    val typeParameters = functionDefinition.parameters.map { p => TVar( p.name ) }
    val returnType = compileTipType( functionDefinition.returnType, typeParameters )
    val compiledFunctionBody = compileExpression( functionDefinition.body, formalParameters, Some( returnType ) )

    ctx += ReductionRule( functionConstant( formalParameters ), compiledFunctionBody )
  }

  private def compileAssertion( tipSmtAssertion: TipSmtAssertion ): Unit = {

    val TipSmtAssertion( _, formula ) = tipSmtAssertion

    assumptions += compileExpression( formula, Nil, Some( To ) )
      .asInstanceOf[Formula]
  }

  private def compileGoal( tipSmtGoal: TipSmtGoal ): Unit = {

    val TipSmtGoal( _, formula ) = tipSmtGoal

    goals += compileExpression( formula, Nil, Some( To ) )
      .asInstanceOf[Formula]
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

  def compileExpression(
    expression: TipSmtExpression, freeVars: Seq[Var], resultType: Option[Ty] ): Expr =
    expression match {
      case expr @ TipSmtForall( _, _ ) =>
        compileExpression( expr, freeVars, resultType )
      case expr @ TipSmtExists( _, _ ) =>
        compileExpression( expr, freeVars, resultType )
      case expr @ TipSmtEq( _ ) =>
        compileExpression( expr, freeVars, resultType )
      case expr @ TipSmtIte( _, _, _ ) =>
        compileExpression( expr, freeVars, resultType )
      case expr @ TipSmtMatch( _, _ ) =>
        compileExpression( expr, freeVars, resultType )
      case expr @ TipSmtAnd( _ ) =>
        compileExpression( expr, freeVars, resultType )
      case expr @ TipSmtOr( _ ) =>
        compileExpression( expr, freeVars, resultType )
      case expr @ TipSmtNot( _ ) =>
        compileExpression( expr, freeVars, resultType )
      case expr @ TipSmtImp( _ ) =>
        compileExpression( expr, freeVars, resultType )
      case expr @ TipSmtIdentifier( _ ) =>
        compileExpression( expr, freeVars, resultType )
      case expr @ TipSmtFun( _, _ ) =>
        compileExpression( expr, freeVars, resultType )
      case TipSmtFalse =>
        Bottom()
      case TipSmtTrue =>
        Top()
      case TipSmtDistinct( _ ) => throw new IllegalArgumentException
    }

  private def compileExpression(
    tipSmtAnd: TipSmtAnd, freeVars: Seq[Var], expectedType: Ty ): Expr = {
    if ( expectedType != To ) {
      throw TipSmtParserException( "type mismatch" )
    }
    And(
      tipSmtAnd.exprs
        .map { compileExpression( _, freeVars, Some( To ) ).asInstanceOf[Formula] } )
  }

  private def compileExpression(
    tipSmtOr: TipSmtOr, freeVars: Seq[Var], expectedType: Ty ): Expr = {
    if ( expectedType != To ) {
      throw TipSmtParserException( "type mismatch" )
    }
    Or(
      tipSmtOr.exprs
        .map { compileExpression( _, freeVars, Some( To ) ).asInstanceOf[Formula] } )
  }

  private def compileExpression(
    tipSmtNot: TipSmtNot, freeVars: Seq[Var], expectedType: Ty ): Expr = {
    if ( expectedType != To ) {
      throw TipSmtParserException( "type mismatch" )
    }
    Neg( compileExpression( tipSmtNot.expr, freeVars, Some( To ) ) )
  }

  private def compileExpression(
    tipSmtImp: TipSmtImp, freeVars: Seq[Var], expectedType: Ty ): Expr = {
    if ( expectedType != To ) {
      throw TipSmtParserException( "type mismatch" )
    }
    tipSmtImp.exprs
      .map { compileExpression( _, freeVars, Some( To ) ) } reduceRight { _ --> _ }
  }

  private def compileExpression(
    identifier: TipSmtIdentifier, ctxVars: Seq[Var], expectedType: Option[Ty] ): Expr = {
    if ( ctxVars.exists( _.name == identifier.name ) ) {
      lookupVariable( identifier, ctxVars, expectedType )
    } else {
      lookupConstant( identifier, ctxVars, expectedType )
    }
  }

  // lookup and check a variable that exists in the context variables
  private def lookupVariable( identifier: TipSmtIdentifier, ctxVars: Seq[Var], expectedType: Option[Ty] ): Expr = {
    val v = ctxVars.find( _.name == identifier.name ).get
    expectedType match {
      case Some( ty ) =>
        if ( v.ty != ty ) {
          throw TipSmtParserException( s"expected type $ty but got ${v.ty}" )
        }
        v
      case _ => v
    }
  }

  // try to lookup and check a constant from the context
  private def lookupConstant( identifier: TipSmtIdentifier, ctxVars: Seq[Var], expectedType: Option[Ty] ): Expr = {
    ctx.constant( identifier.name ) match {
      case Some( c ) =>
        expectedType match {
          case Some( eTy ) =>
            syntacticMatching( c.ty, eTy ) match {
              case Some( matching ) => matching( c )
              case _ => throw TipSmtParserException(
                s"unable to instantiate constant ${c} to expected type ${eTy}" )
            }
          case _ => c
        }
      case _ => throw TipSmtParserException( s"undefined constant ${identifier.name}" )
    }
  }

  private def compileExpression(
    tipSmtFun: TipSmtFun, ctxVars: Seq[Var], expectedType: Option[Ty] ): Expr = {
    // todo: fix this, the expected type fixes some but not all type variables
    val functionConstant = ctx.constant( tipSmtFun.name ) match {
      case Some( fc ) =>
        expectedType match {
          case Some( ety ) =>
            val FunctionType( returnType, argumentTypes ) = fc.ty
            syntacticMatching( returnType, ety ) match {
              case Some( matching ) => matching( fc )
              case _ =>
                throw TipSmtParserException(
                  s"return type ${returnType} does not match expected " +
                    s"type ${ety}." )
            }
          case _ => fc
        }
      case _ =>
        throw TipSmtParserException( s"unknown constant ${tipSmtFun.name}" )
    }
    val FunctionType( returnType, argumentTypes ) = functionConstant.ty
    if ( tipSmtFun.arguments.size != argumentTypes.size ) {
      throw TipSmtParserException(
        s"illegal number of arguments: function ${functionConstant} expects " +
          s"${argumentTypes.size} argument(s) but got " +
          s"${tipSmtFun.arguments.size} arguments." )
    }
    functionConstant(
      tipSmtFun.arguments.zip( argumentTypes ) map { case ( arg, ty ) => compileExpression( arg, ctxVars, Some( ty ) ) }: _* )
  }

  private def compileExpression(
    tipSmtMatch: TipSmtMatch, freeVars: Seq[Var], expectedType: Option[Ty] ): Expr = {
    val TipSmtMatch( matchedExpression, cases ) = tipSmtMatch

    val compiledMatchedExpression =
      compileExpression( matchedExpression, freeVars, None )

    if ( !compiledMatchedExpression.ty.isInstanceOf[TBase] ) {
      throw TipSmtParserException( "matching expression having complex type" )
    }

    if ( ctx.getConstructors( compiledMatchedExpression.ty ).isEmpty ) {
      throw TipSmtParserException( "matching expression with non-inductive base type" )
    }

    val matchedType: TBase = compiledMatchedExpression.ty.asInstanceOf[TBase]

    // todo: check that the number of cases and the names are valid.

    val compiledCases =
      reorderCases( matchedType, cases ) map { compileCase( _, freeVars, matchedType, expectedType ) }

    val compiledCasesTypes = compiledCases.map { _._2 }.toSet
    if ( compiledCasesTypes.size > 1 ) {
      throw TipSmtParserException( s"match cases have differing types ${compiledCasesTypes}" )
    }
    val resultType = compiledCases.head._2
    expectedType match {
      case Some( ety ) =>
        if ( resultType != ety ) {
          throw TipSmtParserException( s"match cases have unexpected type: expected ${ety} but got ${resultType}." )
        }
      case _ =>
    }
    val Some( matchConstant ) = ctx.constant( matchConstantName( matchedType ), List( resultType ) )
    Apps( matchConstant, compiledMatchedExpression +: compiledCases.map { _._1 } )

  }

  private def reorderCases( inductiveType: TBase, cases: Seq[TipSmtCase] ): Seq[TipSmtCase] = {
    val constructors = ctx.getConstructors( inductiveType ).get.map { _.name }
    cases.sortWith( {
      case ( TipSmtCase( TipSmtConstructorPattern( n1, _ ), _ ), TipSmtCase( TipSmtConstructorPattern( n2, _ ), _ ) ) =>
        val constructorsWithIndex = constructors.zipWithIndex
        constructorsWithIndex.find( { _._1 == n1.name } ).get._2 < constructorsWithIndex.find( { _._1 == n2.name } ).get._2
    } )
  }

  private def compileCase(
    tipSmtCase:  TipSmtCase,
    freeVars:    Seq[Var],
    matchedType: TBase,
    resultType:  Option[Ty] ): ( Expr, Ty ) = {

    val Some( constructors ) = ctx.getConstructors( matchedType )
    val TipSmtCase(
      TipSmtConstructorPattern( constructorName, identifiers ),
      expr ) = tipSmtCase

    constructors.find { _.name == constructorName.name } match {
      case Some( const ) => const
      case None          => throw TipSmtParserException( "invalid constructor in case" )
    }
    val constructorConstant = ctx.constant( constructorName.name, matchedType.params ).get
    val FunctionType( _, constructorArgumentTypes ) = constructorConstant.ty
    if ( identifiers.size != constructorArgumentTypes.size ) {
      throw TipSmtParserException( "invalid number of variables in constructor pattern" )
    }

    val abstractionVariables: Seq[Var] =
      identifiers
        .map { _.name }
        .zip( constructorArgumentTypes )
        .map {
          case ( name, ty ) => Var( name, ty )
        }

    val compiledExpr = compileExpression( expr, abstractionVariables ++ freeVars, resultType )

    ( Abs( abstractionVariables, compiledExpr ), compiledExpr.ty )
  }

  private def compileExpression(
    iteExpression: TipSmtIte, ctxVars: Seq[Var], expectedType: Option[Ty] ): Expr = {
    val condition = compileExpression( iteExpression.cond, ctxVars, Some( To ) )
    val ifTrue = compileExpression( iteExpression.ifTrue, ctxVars, expectedType )
    val ifFalse = compileExpression( iteExpression.ifFalse, ctxVars, expectedType )
    if ( ifTrue.ty != ifFalse.ty ) {
      throw TipSmtParserException( s"type mismatch: ${ifTrue.ty} is not equal to ${ifFalse.ty}" )
    }
    ctx.constant( iteConstantName, List( ifTrue.ty ) ).get.apply( condition, ifTrue, ifFalse )
  }

  private def compileExpression(
    tipSmtEq: TipSmtEq, freeVars: Seq[Var], expectedType: Option[Ty] ): Expr = {
    expectedType match {
      case Some( ety ) =>
        if ( ety != To ) {
          throw TipSmtParserException( s"expected type ${ety} but got ${To}." )
        }
      case _ =>
    }
    val exprs = tipSmtEq.exprs map { compileExpression( _, freeVars, None ) }
    And( for ( ( a, b ) <- exprs zip exprs.tail )
      yield if ( exprs.head.ty == To ) a <-> b else a === b )
  }

  private def compileExpression(
    tipSmtForall: TipSmtForall, freeVars: Seq[Var], expectedType: Option[Ty] ): Expr = {
    expectedType match {
      case Some( ety ) =>
        if ( ety != To ) {
          throw TipSmtParserException( s"expected type ${ety} but got ${To}." )
        }
      case _ =>
    }
    val variables =
      tipSmtForall.variables.map { case TipSmtVariableDecl( name, ty ) => Var( name, compileTipType( ty, Seq() ) ) }

    All.Block(
      variables,
      compileExpression( tipSmtForall.formula, variables ++ freeVars, Some( To ) ) )
  }

  private def compileTipType( ty: TipSmtType, typeVariables: Seq[TVar] ): Ty = {
    ty match {
      case TipSmtType( name ) =>
        // check that the base type exists
        if ( ctx.isType( TBase( name ) ) ) {
          TBase( name )
        } else {
          throw TipSmtParserException( "unknown base type" )
        }
      case _ => ???
    }
  }

  private def compileExpression(
    tipSmtExists: TipSmtExists, freeVars: Seq[Var], expectedType: Option[Ty] ): Expr = {
    expectedType match {
      case Some( ety ) =>
        if ( expectedType != To ) {
          throw TipSmtParserException( s"expected type ${ety} but got ${To}." )
        }
      case _ =>
    }
    val variables = tipSmtExists.variables.map {
      case TipSmtVariableDecl( name, ty ) =>
        Var( name, compileTipType( ty, Seq() ) )
    }
    Ex.Block(
      variables,
      compileExpression( tipSmtExists.formula, variables ++ freeVars, Some( To ) ) )
  }

  private def compileFields(
    fields: Seq[( TipSmtIdentifier, Datatype )] ): Seq[Expr] = {
    fields map {
      case ( f, ty ) =>
        if ( isVariable( f ) ) {
          Var( f.name, typeDecls( ty.name ) )
        } else {
          Const( f.name, typeDecls( ty.name ) )
        }
    }
  }

  private def compileConstructorSymbol( id: TipSmtIdentifier ): Expr = {
    val constructorType = problem.symbolTable.get.typeOf( id.name )
    Const(
      id.name,
      FunctionType(
        typeDecls( constructorType.returnType.name ),
        constructorType.argumentTypes
          .map { dt => typeDecls( dt.name ) }.toList ) )
  }

  private def isVariable( id: TipSmtIdentifier ): Boolean = {
    !problem.symbolTable.get.contains( id.name )
  }

  private def declareBaseType( sort: String ): Unit = {
    val baseType = TBase( sort )
    declare( baseType )
    ctx += baseType
  }

  private val iteConstantName: String = "ite"

  private def declareIteConstant(): Unit = {
    val iteType = To ->: TVar( "a" ) ->: TVar( "a" ) ->: TVar( "a" )
    val iteConstant = Const( "ite", iteType, List( TVar( "a" ) ) )
    val itePrfDefinition =
      PrimitiveRecursiveFunction(
        iteConstant,
        3,
        0,
        {
          val x = Var( "x", TVar( "a" ) )
          val y = Var( "y", TVar( "a" ) )
          Vector(
            Apps( iteConstant, Seq( TopC(), x, y ) ) -> x,
            Apps( iteConstant, Seq( BottomC(), x, y ) ) -> y )
        } )
    ctx += itePrfDefinition
  }

  // name of the constant of a match on a specific inductive type
  private def matchConstantName( inductiveType: InductiveType ): String = {
    matchConstantName( inductiveType.ty )
  }

  private def matchConstantName( inductiveType: TBase ): String = {
    "match" + "_" + inductiveType.name
  }

  // declares the constant symbol corresponding to a match statement
  // the match constant for an inductive type T with constructors c_1, ..., c_m
  // is of the form matchT : T -> f_1 -> ... -> f_m
  // where f_i is the i-th case in the match expression
  private def declareMatchConstant( inductiveType: InductiveType ): Unit = {
    val resultType = TVar( "a" )
    val argumentTypes =
      inductiveType
        .constructors
        .map { _.ty }
        .map { case FunctionType( _, from ) => FunctionType( resultType, from ) }
    val matchType: Ty = FunctionType( resultType, inductiveType.ty +: argumentTypes )
    val matchConstant = Const( matchConstantName( inductiveType ), matchType, List( resultType ) )
    // add this constant as a primitive recursively defined function
    // functions f_1, ..., f_m corresponding to the cases.
    val caseArguments: Map[Const, Var] = inductiveType.constructors.map {
      constructor =>
        val names = new NameGenerator( Seq() )
        val FunctionType( _, argumentTypes ) = constructor.ty
        val caseVariable = Var( names.fresh( "f" ), FunctionType( resultType, argumentTypes ) )
        ( constructor, caseVariable )
    }.toMap
    // equations of the form `match (c_i x_1 ... x_n) f_1 ... f_{i-1} f_i f_{i+1} ... f_m = f_i x_1 ... x_n`
    val equations: Vector[( Expr, Expr )] =
      inductiveType.constructors.map {
        constructor =>
          val names = new NameGenerator( Seq() )
          val FunctionType( _, argumentTypes ) = constructor.ty
          val constructorArguments = argumentTypes.map { Var( names.fresh( "x" ), _ ) }
          val leftHandSide =
            Apps(
              matchConstant,
              Apps( constructor, constructorArguments ) +: inductiveType.constructors.map { caseArguments( _ ) } )
          val rightHandSide = Apps( caseArguments( constructor ), constructorArguments )
          leftHandSide -> rightHandSide
      }
    val matchPrfDefinition =
      PrimitiveRecursiveFunction( matchConstant, inductiveType.constructors.size + 1, 0, equations )
    ctx += matchPrfDefinition
  }

  private def declareDatatype( tipSmtDatatype: TipSmtDatatype ): Unit = {
    val t = TBase( tipSmtDatatype.name )
    declare( t )
    // add the inductive datatype
    val dt = TipDatatype(
      t,
      tipSmtDatatype.constructors.map { compileTipSmtConstructor( _, t ) } )
    val inductiveType = InductiveType( t, dt.constructors.map( _.constr ): _* )
    ctx += inductiveType
    // declare the corresponding match constant
    declareMatchConstant( inductiveType )
    datatypes += dt
    dt.constructors foreach { ctr =>
      declare( ctr.constr )
      for ( proj <- ctr.projectors ) {
        declare( proj )
        ctx += proj
      }
    }
  }

  def toProblem: TipProblem =
    TipProblem(
      ctx,
      typeDecls.values.toSeq diff datatypes.map { _.t }, datatypes,
      funDecls.values.toSeq diff functions.map { _.fun },
      functions,
      assumptions, And( goals ) )

  def compileTipProblem(): TipSmtToTipProblemCompiler = {
    declareIteConstant()
    problem.definitions.foreach {
      case c @ TipSmtConstantDeclaration( _, _, _ ) =>
        compileConstantDeclaration( c )
      case c @ TipSmtSortDeclaration( _, _ ) =>
        compileSortDeclaration( c )
      case c @ TipSmtFunctionDeclaration( _, _, _, _ ) =>
        compileFunctionDeclaration( c )
      case c @ TipSmtGoal( _, _ ) =>
        compileGoal( c )
      case c @ TipSmtAssertion( _, _ ) =>
        compileAssertion( c )
      case c @ TipSmtFunctionDefinition( _, _, _, _, _ ) =>
        declareFunction( c )
        compileFunctionDefinition( c )
      case c @ TipSmtCheckSat() =>
      case c @ TipSmtDatatypesDeclaration( _ ) =>
        compileDatatypesDeclaration( c )
      case c @ TipSmtMutualRecursiveFunctionDefinition( functions ) =>
        functions foreach { declareFunction }
        functions foreach { compileFunctionDefinition }
    }
    this
  }
}