package gapt.formats.tip.compiler

import gapt.expr.All
import gapt.expr.And
import gapt.expr.Apps
import gapt.expr.Bottom
import gapt.expr.BottomC
import gapt.expr.Const
import gapt.expr.Ex
import gapt.expr.Expr
import gapt.expr.Formula
import gapt.expr.FunctionType
import gapt.expr.Neg
import gapt.expr.Or
import gapt.expr.TBase
import gapt.expr.To
import gapt.expr.Top
import gapt.expr.TopC
import gapt.expr.Ty
import gapt.expr.Var
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
import gapt.formats.tip.parser.TipSmtNot
import gapt.formats.tip.parser.TipSmtOr
import gapt.formats.tip.parser.TipSmtProblem
import gapt.formats.tip.parser.TipSmtSortDeclaration
import gapt.formats.tip.parser.TipSmtTrue
import gapt.formats.tip.parser.TipSmtVariableDecl
import gapt.formats.tip.transformation.BooleanConstantElimination
import gapt.formats.tip.transformation.EliminateUselessQuantifiers
import gapt.formats.tip.transformation.MoveUniversalQuantifiersInwards
import gapt.formats.tip.transformation.TipSmtDefaultPatternExpansion
import gapt.formats.tip.transformation.UseDefinitionEquations
import gapt.formats.tip.transformation.VariableMatchExpansion
import gapt.formats.tip.transformation.tipOcnf
import gapt.proofs.Context

import scala.collection.mutable

class TipSmtToTipProblemCompiler( var problem: TipSmtProblem ) {

  ( new ReconstructDatatypes( problem ) )()
  ( new TipSmtDefaultPatternExpansion( problem ) )()

  problem = new UseDefinitionEquations( problem )()

  problem = tipOcnf( problem )

  problem = new VariableMatchExpansion( problem )()
  problem = new BooleanConstantElimination( problem )()
  problem = new MoveUniversalQuantifiersInwards( problem )()
  problem = new EliminateUselessQuantifiers( problem )()

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
      compileFunctionBody( body, argVars.map { v => v.name -> v }.toMap ) )
  }

  private def compileAssertion( tipSmtAssertion: TipSmtAssertion ): Unit = {

    val TipSmtAssertion( _, formula ) = tipSmtAssertion

    assumptions += compileExpression( formula, Map[String, Expr]() )
      .asInstanceOf[Formula]
  }

  private def compileGoal( tipSmtGoal: TipSmtGoal ): Unit = {

    val TipSmtGoal( _, formula ) = tipSmtGoal

    goals += compileExpression( formula, Map[String, Expr]() )
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

  def compileFunctionBody(
    body: TipSmtExpression, freeVars: Map[String, Expr] ): Seq[Formula] = {
    body match {
      case TipSmtAnd( conjuncts ) =>
        conjuncts
          .flatMap { compileFunctionBody( _, freeVars ) }
      case TipSmtIte( condition, ifTrue, ifFalse ) =>
        val compiledCondition = compileExpression( condition, freeVars )
        compileFunctionBody( ifTrue, freeVars )
          .map { compiledCondition --> _ } ++
          compileFunctionBody( ifFalse, freeVars )
          .map { -compiledCondition --> _ }
      case TipSmtForall( boundVars, formula ) =>
        val bound = boundVars map { v =>
          Var( v.name, typeDecls( v.typ.typename ) )
        }
        val result = compileFunctionBody(
          formula, freeVars ++ ( bound map { v => v.name -> v } ) )
          .map { All.Block( bound, _ ) }
        result
      case _ => Seq( compileExpression( body, freeVars ).asInstanceOf[Formula] )
    }
  }

  def compileExpression(
    expression: TipSmtExpression, freeVars: Map[String, Expr] ): Expr =
    expression match {
      case expr @ TipSmtForall( _, _ ) =>
        compileExpression( expr, freeVars )
      case expr @ TipSmtExists( _, _ ) =>
        compileExpression( expr, freeVars )
      case expr @ TipSmtEq( _ ) =>
        compileExpression( expr, freeVars )
      case expr @ TipSmtIte( _, _, _ ) =>
        compileExpression( expr, freeVars )
      case expr @ TipSmtMatch( _, _ ) =>
        compileExpression( expr, freeVars )
      case expr @ TipSmtAnd( _ ) =>
        compileExpression( expr, freeVars )
      case expr @ TipSmtOr( _ ) =>
        compileExpression( expr, freeVars )
      case expr @ TipSmtNot( _ ) =>
        compileExpression( expr, freeVars )
      case expr @ TipSmtImp( _ ) =>
        compileExpression( expr, freeVars )
      case expr @ TipSmtIdentifier( _ ) =>
        compileExpression( expr, freeVars )
      case expr @ TipSmtFun( _, _ ) =>
        compileExpression( expr, freeVars )
      case TipSmtFalse =>
        Bottom()
      case TipSmtTrue =>
        Top()
    }

  private def compileExpression(
    tipSmtAnd: TipSmtAnd, freeVars: Map[String, Expr] ): Expr = {
    And(
      tipSmtAnd.exprs
        .map { compileExpression( _, freeVars ).asInstanceOf[Formula] } )
  }

  private def compileExpression(
    tipSmtOr: TipSmtOr, freeVars: Map[String, Expr] ): Expr = {
    Or(
      tipSmtOr.exprs
        .map { compileExpression( _, freeVars ).asInstanceOf[Formula] } )
  }

  private def compileExpression(
    tipSmtNot: TipSmtNot, freeVars: Map[String, Expr] ): Expr = {
    Neg( compileExpression( tipSmtNot.expr, freeVars ) )
  }

  private def compileExpression(
    tipSmtImp: TipSmtImp, freeVars: Map[String, Expr] ): Expr = {
    tipSmtImp.exprs
      .map { compileExpression( _, freeVars ) } reduceRight { _ --> _ }
  }

  private def compileExpression(
    tipSmtIdentifier: TipSmtIdentifier, freeVars: Map[String, Expr] ): Expr = {
    if ( freeVars contains tipSmtIdentifier.name ) {
      freeVars( tipSmtIdentifier.name )
    } else {
      funDecls( tipSmtIdentifier.name )
    }
  }

  private def compileExpression(
    tipSmtFun: TipSmtFun, freeVars: Map[String, Expr] ): Expr = {
    funDecls( tipSmtFun.name )(
      tipSmtFun.arguments map { compileExpression( _, freeVars ) }: _* )
  }

  private def compileExpression(
    tipSmtMatch: TipSmtMatch, freeVars: Map[String, Expr] ): Expr = {
    val TipSmtMatch( matchedExpression, cases ) = tipSmtMatch
    val compiledMatchedExpression =
      compileExpression( matchedExpression, freeVars )
    And( cases map {
      compileCase( _, compiledMatchedExpression, freeVars )
    } )
  }

  private def compileExpression(
    tipSmtIte: TipSmtIte, freeVars: Map[String, Expr] ): Expr = {
    val TipSmtIte( cond, ifTrue, ifFalse ) = tipSmtIte
    val compiledCondition = compileExpression( cond, freeVars )
    And(
      compiledCondition --> compileExpression( ifTrue, freeVars ),
      -compiledCondition --> compileExpression( ifFalse, freeVars ) )
  }

  private def compileExpression(
    tipSmtEq: TipSmtEq, freeVars: Map[String, Expr] ): Expr = {
    val exprs = tipSmtEq.exprs map { compileExpression( _, freeVars ) }
    And( for ( ( a, b ) <- exprs zip exprs.tail )
      yield if ( exprs.head.ty == To ) a <-> b else a === b )
  }

  private def compileExpression(
    tipSmtForall: TipSmtForall, freeVars: Map[String, Expr] ): Expr = {
    val TipSmtForall( variables, formula ) = tipSmtForall
    val vars = variables map {
      case TipSmtVariableDecl( name, typ ) =>
        Var( name, typeDecls( typ.typename ) )
    }
    All.Block(
      vars,
      compileExpression(
        formula,
        freeVars ++ vars.map { v => v.name -> v } ) )
  }

  private def compileExpression(
    tipSmtExists: TipSmtExists, freeVars: Map[String, Expr] ): Expr = {
    val TipSmtExists( variables, formula ) = tipSmtExists
    val vars = variables map {
      case TipSmtVariableDecl( name, typ ) =>
        Var( name, typeDecls( typ.typename ) )
    }
    Ex.Block(
      vars,
      compileExpression(
        formula,
        freeVars ++ vars.map { v => v.name -> v } ) )
  }

  private def compileCase(
    tipSmtCase:        TipSmtCase,
    matchedExpression: Expr,
    freeVars:          Map[String, Expr] ): Expr = {
    val TipSmtConstructorPattern( constructor, fields ) = tipSmtCase.pattern
    val constructorType = problem.symbolTable.get.typeOf( constructor.name )
    val boundVariables =
      fields
        .zip( constructorType.argumentTypes )
        .filter { case ( field, _ ) => isVariable( field ) }
        .map { case ( field, ty ) => Var( field.name, typeDecls( ty.name ) ) }

    val newFreeVars = freeVars ++ boundVariables.map { v => v.name -> v }

    val compiledPattern =
      Apps(
        compileConstructorSymbol( constructor ),
        compileFields( fields.zip( constructorType.argumentTypes ) ) )

    All.Block(
      boundVariables,
      ( matchedExpression === compiledPattern ) -->
        compileExpression( tipSmtCase.expr, newFreeVars ) )
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

  def toProblem: TipProblem =
    TipProblem(
      ctx,
      typeDecls.values.toSeq diff datatypes.map { _.t }, datatypes,
      funDecls.values.toSeq diff functions.map { _.fun },
      functions,
      assumptions, And( goals ) )

  def compileTipProblem(): TipSmtToTipProblemCompiler = {
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
        compileFunctionDefinition( c )
      case c @ TipSmtCheckSat() =>
      case c @ TipSmtDatatypesDeclaration( _ ) =>
        compileDatatypesDeclaration( c )
    }
    this
  }
}