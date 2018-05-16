package gapt.formats.tip

import java.io.IOException

import gapt.expr._
import gapt.formats.tip.parser._
import gapt.formats.{ InputFile, StringInputFile }
import gapt.proofs.Context
import gapt.utils.{ ExternalProgram, NameGenerator, runProcess }

import scala.collection.mutable

object retrieveDatatypes {
  def apply( problemAst: TipSmtProblem ): Seq[TipSmtDatatype] = {
    problemAst.definitions flatMap {
      _ match {
        case TipSmtDatatypesDeclaration( datatypes ) => datatypes
        case _                                       => Seq()
      }
    }
  }
  def apply( problemAst: TipSmtProblem, datatype: String ): TipSmtDatatype = {
    println( datatype )
    apply( problemAst ).find( _.name == datatype ).get
  }
}

case class Type(
    argumentTypes: Seq[Datatype],
    returnType:    Datatype )

case class SymbolTable(
    symbols: Map[String, Type] )

object computeSymbolTable {
  def apply( tipSmtProblem: TipSmtProblem ): SymbolTable = {
    var symbols: Map[String, Type] = Map()
    tipSmtProblem.definitions foreach {
      _ match {
        case TipSmtFunctionDeclaration(
          functionName, _, argumentTypes, returnType
          ) =>
          val argTypes = argumentTypes.map {
            argType => Datatype( argType.typename )
          }
          symbols +=
            ( functionName -> Type( argTypes, Datatype( returnType.typename ) ) )

        case TipSmtFunctionDefinition(
          functionName, _, formalParameters, returnType, _
          ) =>
          val argTypes = formalParameters map { param =>
            Datatype( param.typ.typename )
          }
          symbols +=
            ( functionName -> Type( argTypes, Datatype( returnType.typename ) ) )

        case TipSmtConstantDeclaration( constantName, _, typ ) =>
          symbols += ( constantName -> Type( Seq(), Datatype( typ.typename ) ) )

        case TipSmtDatatypesDeclaration( datatypes ) =>
          datatypes.foreach { symbols ++= datatypeSymbols( _ ) }

        case _ =>
      }
    }
    SymbolTable( symbols )
  }

  private def datatypeSymbols(
    tipSmtDatatype: TipSmtDatatype ): Map[String, Type] = {
    val symbols: Seq[( String, Type )] =
      tipSmtDatatype.constructors map {
        case TipSmtConstructor( constructorName, _, fields ) =>
          val fieldTypes: Seq[Datatype] = fields map {
            field => Datatype( field.typ.typename )
          }
          constructorName -> Type(
            fieldTypes, Datatype( tipSmtDatatype.name ) )
      }
    Map( symbols: _* )
  }
}

class ReconstructDatatypes( problem: TipSmtProblem ) {

  val symbolTable = computeSymbolTable( problem )

  def apply(): TipSmtProblem = {

    problem.definitions foreach {
      case TipSmtFunctionDefinition( _, _, parameters, _, body ) =>
        val context = parameters map {
          case TipSmtFormalParameter( name, typ ) =>
            name -> Datatype( typ.typename )
        }
        reconstructTypes( body, Map( context: _* ) )
      case TipSmtAssertion( _, expression ) =>
        reconstructTypes( expression, Map() )
      case TipSmtGoal( _, expression ) =>
        reconstructTypes( expression, Map() )
      case _ =>
    }
    problem
  }

  private def reconstructTypes(
    expression: TipSmtExpression,
    variables:  Map[String, Datatype] ): Unit = expression match {
    case TipSmtAnd( subexpressions ) =>
      subexpressions foreach { reconstructTypes( _, variables ) }
      expression.datatype = Some( Datatype( "bool" ) )
    case TipSmtOr( subexpressions ) =>
      subexpressions foreach { reconstructTypes( _, variables ) }
      expression.datatype = Some( Datatype( "bool" ) )
    case TipSmtImp( subexpressions ) =>
      subexpressions foreach { reconstructTypes( _, variables ) }
      expression.datatype = Some( Datatype( "bool" ) )
    case TipSmtNot( subexpression ) =>
      reconstructTypes( subexpression, variables )
      expression.datatype = Some( Datatype( "bool" ) )
    case TipSmtForall( vars, subexpression ) =>
      val context: Seq[( String, Datatype )] = vars map {
        v =>
          v.name -> Datatype( v.typ.typename )
      }
      reconstructTypes(
        subexpression, Map( context: _* ) ++ variables )
      expression.datatype = Some( Datatype( "bool" ) )

    case TipSmtExists( vars, subexpression ) =>
      val context: Seq[( String, Datatype )] = vars map {
        v =>
          v.name -> Datatype( v.typ.typename )
      }
      reconstructTypes(
        subexpression, Map( context: _* ) ++ variables )
      expression.datatype = Some( Datatype( "bool" ) )

    case TipSmtIdentifier( identifier ) =>
      expression.datatype = Some( variables
        .getOrElse( identifier, symbolTable.symbols( identifier ).returnType ) )

    case TipSmtFun( functionName, arguments ) =>
      arguments foreach { arg => reconstructTypes( arg, variables ) }
      expression.datatype = Some( symbolTable.symbols( functionName ).returnType )

    case TipSmtTrue =>
      expression.datatype = Some( Datatype( "bool" ) )

    case TipSmtFalse =>
      expression.datatype = Some( Datatype( "bool" ) )

    case TipSmtIte( expr1, expr2, expr3 ) =>
      reconstructTypes( expr1, variables )
      reconstructTypes( expr3, variables )
      reconstructTypes( expr3, variables )
      expression.datatype = expr2.datatype

    case TipSmtEq( subexpressions ) =>
      subexpressions foreach { reconstructTypes( _, variables ) }
      expression.datatype = Some( Datatype( "bool" ) )

    case TipSmtMatch( expr, cases ) =>
      reconstructTypes( expr, variables )
      cases foreach {
        reconstructTypesCase( expr.datatype.get, _, variables )
      }
      expression.datatype = cases.head.expr.datatype
  }

  private def reconstructTypesCase(
    matchedType: Datatype,
    tipSmtCase:  TipSmtCase,
    variables:   Map[String, Datatype] ): Unit = {
    tipSmtCase.pattern match {
      case TipSmtDefault =>
        reconstructTypes( tipSmtCase.expr, variables )
      case TipSmtConstructorPattern( constructor, identifiers ) =>
        val constructorType = symbolTable.symbols( constructor.name )
        val matchVariables = identifiers.zipWithIndex.filter {
          case ( identifier, _ ) =>
            !symbolTable.symbols.contains( identifier.name )
        }
        val context = matchVariables map {
          case ( identifier, index ) =>
            ( identifier.name, constructorType.argumentTypes( index ) )
        }
        reconstructTypes(
          tipSmtCase.expr, Map( context: _* ) ++ variables )
    }
  }
}

class TipSmtDesugar( problem: TipSmtProblem ) {

  val symbolTable = computeSymbolTable( problem )

  def apply(): Unit = {

    problem.definitions foreach {
      case TipSmtFunctionDefinition( _, _, parameters, _, body ) =>
        val context = parameters map {
          _.name
        }
        desugarExpression( body, context )
      case TipSmtGoal( _, expression ) =>
        desugarExpression( expression, Seq() )
      case TipSmtAssertion( _, expression ) =>
        desugarExpression( expression, Seq() )
      case _ =>
    }
  }

  private def desugarExpression(
    expr:             TipSmtExpression,
    visibleVariables: Seq[String] ): Unit = expr match {
    case TipSmtAnd( subexpressions ) =>
      subexpressions foreach {
        desugarExpression( _, visibleVariables )
      }
    case TipSmtOr( subexpressions ) =>
      subexpressions foreach {
        desugarExpression( _, visibleVariables )
      }
    case TipSmtImp( subexpressions ) =>
      subexpressions foreach {
        desugarExpression( _, visibleVariables )
      }
    case TipSmtFun( _, arguments ) =>
      arguments foreach {
        desugarExpression( _, visibleVariables )
      }
    case TipSmtForall( vars, subexpression ) =>
      desugarExpression(
        subexpression,
        visibleVariables ++ vars.map( _.name ) )
    case TipSmtExists( vars, subexpression ) =>
      desugarExpression(
        subexpression,
        visibleVariables ++ vars.map( _.name ) )
    case matchExpr @ TipSmtMatch( _, _ ) =>
      if ( containsDefaultPattern( matchExpr ) ) {
        expandDefaultPattern( matchExpr, visibleVariables )
      }
      matchExpr.cases foreach {
        desugarCaseStatement( _, symbolTable, visibleVariables )
      }
    case TipSmtIte( expr1, expr2, expr3 ) =>
      desugarExpression( expr1, visibleVariables )
      desugarExpression( expr2, visibleVariables )
      desugarExpression( expr3, visibleVariables )
    case _ =>
  }

  private def desugarCaseStatement(
    cas:              TipSmtCase,
    symbolTable:      SymbolTable,
    visibleVariables: Seq[String] ): Unit = {
    cas.pattern match {
      case TipSmtConstructorPattern( _, fields ) =>
        val variableFields =
          fields map { _.name } filter { !symbolTable.symbols.contains( _ ) }
        desugarExpression(
          cas.expr, visibleVariables ++ variableFields )
      case _ => throw new IllegalStateException()
    }
  }

  private def containsDefaultPattern( tipSmtMatch: TipSmtMatch ): Boolean = {
    tipSmtMatch.cases.exists { _.pattern == TipSmtDefault }
  }

  private def expandDefaultPattern(
    tipSmtMatch:      TipSmtMatch,
    visibleVariables: Seq[String] ): Unit = {
    val TipSmtMatch( matchedExpression, cases ) = tipSmtMatch
    val Some( matchedType ) = tipSmtMatch.expr.datatype
    val coveredConstructors: Seq[String] =
      coveredConstrs( cases, symbolTable )
    val missingConstructors =
      retrieveDatatypes( problem, matchedType.name )
        .constructors
        .filter {
          constructor => !coveredConstructors.contains( constructor.name )
        }
    val defaultExpr = cases.filter {
      case TipSmtCase( TipSmtDefault, _ ) => true
      case _                              => false
    }.head.expr
    val generatedCases = missingConstructors map {
      generateCase( _, visibleVariables, defaultExpr )
    }
    tipSmtMatch.cases = tipSmtMatch.cases filter { _.pattern != TipSmtDefault }
    tipSmtMatch.cases ++= generatedCases
  }

  private def generateCase(
    tipSmtConstructor: TipSmtConstructor,
    visibleVariables:  Seq[String],
    defaultExpression: TipSmtExpression ): TipSmtCase = {
    val nameGenerator = new NameGenerator( visibleVariables )
    TipSmtCase(
      TipSmtConstructorPattern(
        TipSmtIdentifier( tipSmtConstructor.name ),
        tipSmtConstructor.fields.map {
          _ => TipSmtIdentifier( nameGenerator.fresh( "x" ) )
        } ),
      defaultExpression )
  }

  private def coveredConstrs(
    cases: Seq[TipSmtCase], symbolTable: SymbolTable ): Seq[String] = {
    cases map { _.pattern } filter {
      case TipSmtDefault => false
      case TipSmtConstructorPattern( constructor, _ ) =>
        symbolTable.symbols.contains( constructor.name )
    } map {
      case TipSmtConstructorPattern( constructor, _ ) =>
        constructor.name
      case _ => throw new IllegalStateException()
    }
  }
}

object tipOcnf {
  def apply( expression: TipSmtExpression ): TipSmtExpression = {
    expression match {
      case expr @ TipSmtAnd( _ ) => ocnfAnd(expr)
      case expr @ TipSmtOr(_) => ocnfOr(expr)
      case expr @ TipSmtImp(_) => ocnfImp(expr)
      case expr @ TipSmtEq(_) => ocnfEq(expr)
      case expr @ TipSmtForall(_,_) => ocnfForall(expr)
      case expr @ TipSmtExists(_,_) => ocnfExists(expr)
      case expr @ TipSmtIte(_,_,_) => ocnfIte(expr)
      case expr @ TipSmtMatch(_,_) => ocnfMatch(expr)
      case expr @ TipSmtFun(_,_) => ocnfFun(expr)
      case expr @ TipSmtNot(_) => ocnfNot(expr)
      case TipSmtIdentifier(_) => expression
      case TipSmtTrue => TipSmtTrue
      case TipSmtFalse => TipSmtFalse
    }
  }

  private def ocnfNot(expression: TipSmtNot): TipSmtExpression = {
    val newSubExpression = tipOcnf(expression.expr)
    newSubExpression match {
      case c @ TipSmtIte(_,_,_) =>
        val newIfTrue = tipOcnf(TipSmtNot(c.the))
        val newIfFalse = tipOcnf(TipSmtNot(c.els))
        TipSmtIte(c.cond, newIfTrue, newIfFalse)
      case m @ TipSmtMatch(_,_) =>
        val newCases = m.cases map { c =>
          TipSmtCase(c.pattern, tipOcnf(TipSmtNot(c.expr)))
        }
        TipSmtMatch(m.expr, newCases)
      case _ =>
        TipSmtNot(newSubExpression)
    }
  }

  private def ocnfMatch(expression: TipSmtMatch): TipSmtExpression = {
    val newMatchedExpr = tipOcnf(expression.expr)
    newMatchedExpr match {
      case c @ TipSmtIte(_,_,_) =>
        val newIfTrue = tipOcnf(TipSmtMatch(c.the, expression.cases))
        val newIfFalse = tipOcnf(TipSmtMatch(c.els, expression.cases))
        TipSmtIte(c.cond, newIfTrue, newIfFalse)
      case m @ TipSmtMatch(_,_) =>
        val newCases = m.cases map { c =>
          TipSmtCase(
            c.pattern,
            tipOcnf( TipSmtMatch(c.expr, expression.cases)))
        }
        TipSmtMatch(m.expr, newCases)
      case _ =>
        TipSmtMatch(
          newMatchedExpr,
          expression.cases.map{ c =>
            TipSmtCase(c.pattern, tipOcnf(c.expr))
          })
    }
  }

  private def ocnfIte(expression: TipSmtIte): TipSmtExpression = {
    val newCond = tipOcnf(expression.cond)
    newCond match {
      case c @ TipSmtIte(_,_,_) =>
        val newIfTrue  = tipOcnf(
          TipSmtIte(c.the, expression.the, expression.els))
        val newIfFalse = tipOcnf(
          TipSmtIte(c.els, expression.the, expression.els))
        TipSmtIte(c.cond, newIfTrue, newIfFalse)
      case m @ TipSmtMatch(_,_) =>
        val newCases = m.cases map { c =>
          TipSmtCase(
            c.pattern,
            tipOcnf(TipSmtIte(c.expr, expression.the, expression.els)))
        }
        TipSmtMatch(m.expr, newCases)
      case _ =>
        TipSmtIte(newCond, tipOcnf(expression.the), tipOcnf(expression.els))
    }
  }

  private def ocnfExists(expression: TipSmtExists): TipSmtExpression = {
    TipSmtExists( expression.variables, tipOcnf(expression.formula))
  }

  private def ocnfForall(expression: TipSmtForall): TipSmtExpression = {
    TipSmtForall( expression.variables, tipOcnf(expression.formula))
  }

  private def ocnfAnd( expression: TipSmtAnd): TipSmtExpression = {
    val newSubexpressions = expression.exprs map { tipOcnf(_) }
    if (newSubexpressions.exists(_.isInstanceOf[TipSmtIte])) {
      val Some((left, ite, right)) =
        find(
          newSubexpressions,
          { (expr:TipSmtExpression) => expr.isInstanceOf[TipSmtIte] })

      val TipSmtIte(cond, iftrue, iffalse) = ite
      val newIfTrue = TipSmtAnd(left ++ (Seq(iftrue)) ++ right)
      val newIfFalse = TipSmtAnd(left ++ (Seq(iffalse)) ++ right)
      TipSmtIte(cond, tipOcnf(newIfTrue), tipOcnf(newIfFalse))

    } else if (newSubexpressions.exists(_.isInstanceOf[TipSmtMatch])) {
      val Some( (left, matchExpr, right)) =
        find(
          newSubexpressions,
          { expr: TipSmtExpression => expr.isInstanceOf[TipSmtMatch] } )
      val TipSmtMatch( matchedTerm , cases ) = matchExpr
      val newCases = cases map {
        cas =>
          TipSmtCase(
            cas.pattern,
            tipOcnf(TipSmtAnd(left ++ Seq(cas.expr) ++ right)))
      }
      TipSmtMatch( matchedTerm, newCases )
    } else {
      TipSmtAnd( expression.exprs.map{ tipOcnf(_) })
    }
  }

  private def ocnfOr( expression: TipSmtOr): TipSmtExpression = {
    val newSubexpressions = expression.exprs map { tipOcnf(_) }
    if (newSubexpressions.exists(_.isInstanceOf[TipSmtIte])) {
      val Some((left, ite, right)) =
        find(
          newSubexpressions,
          { (expr:TipSmtExpression) => expr.isInstanceOf[TipSmtIte] })

      val TipSmtIte(cond, iftrue, iffalse) = ite
      val newIfTrue = TipSmtOr(left ++ (Seq(iftrue)) ++ right)
      val newIfFalse = TipSmtOr(left ++ (Seq(iffalse)) ++ right)
      TipSmtIte(cond, tipOcnf(newIfTrue), tipOcnf(newIfFalse))

    } else if (newSubexpressions.exists(_.isInstanceOf[TipSmtMatch])) {
      val Some( (left, matchExpr, right)) =
        find(
          newSubexpressions,
          { expr: TipSmtExpression => expr.isInstanceOf[TipSmtMatch] } )
      val TipSmtMatch( matchedTerm , cases ) = matchExpr
      val newCases = cases map {
        cas =>
          TipSmtCase(
            cas.pattern,
            tipOcnf(TipSmtOr(left ++ Seq(cas.expr) ++ right)))
      }
      TipSmtMatch( matchedTerm, newCases )
    } else {
      TipSmtOr( expression.exprs.map{ tipOcnf(_) })
    }
  }
  private def ocnfImp( expression: TipSmtImp): TipSmtExpression = {
    val newSubexpressions = expression.exprs map { tipOcnf(_) }
    if (newSubexpressions.exists(_.isInstanceOf[TipSmtIte])) {
      val Some((left, ite, right)) =
        find(
          newSubexpressions,
          { (expr:TipSmtExpression) => expr.isInstanceOf[TipSmtIte] })

      val TipSmtIte(cond, iftrue, iffalse) = ite
      val newIfTrue = TipSmtImp(left ++ (Seq(iftrue)) ++ right)
      val newIfFalse = TipSmtImp(left ++ (Seq(iffalse)) ++ right)
      TipSmtIte(cond, tipOcnf(newIfTrue), tipOcnf(newIfFalse))

    } else if (newSubexpressions.exists(_.isInstanceOf[TipSmtMatch])) {
      val Some( (left, matchExpr, right)) =
        find(
          newSubexpressions,
          { expr: TipSmtExpression => expr.isInstanceOf[TipSmtMatch] } )
      val TipSmtMatch( matchedTerm , cases ) = matchExpr
      val newCases = cases map {
        cas =>
          TipSmtCase(
            cas.pattern,
            tipOcnf(TipSmtImp(left ++ Seq(cas.expr) ++ right)))
      }
      TipSmtMatch( matchedTerm, newCases )
    } else {
      TipSmtImp( expression.exprs.map{ tipOcnf(_) })
    }
  }

  private def ocnfEq( expression: TipSmtEq): TipSmtExpression = {
    val newSubexpressions = expression.exprs map { tipOcnf(_) }
    if (newSubexpressions.exists(_.isInstanceOf[TipSmtIte])) {
      val Some((left, ite, right)) =
        find(
          newSubexpressions,
          { (expr:TipSmtExpression) => expr.isInstanceOf[TipSmtIte] })

      val TipSmtIte(cond, iftrue, iffalse) = ite
      val newIfTrue = TipSmtEq(left ++ (Seq(iftrue)) ++ right)
      val newIfFalse = TipSmtEq(left ++ (Seq(iffalse)) ++ right)
      TipSmtIte(cond, tipOcnf(newIfTrue), tipOcnf(newIfFalse))

    } else if (newSubexpressions.exists(_.isInstanceOf[TipSmtMatch])) {
      val Some( (left, matchExpr, right)) =
        find(
          newSubexpressions,
          { expr: TipSmtExpression => expr.isInstanceOf[TipSmtMatch] } )
      val TipSmtMatch( matchedTerm , cases ) = matchExpr
      val newCases = cases map {
        cas =>
          TipSmtCase(
            cas.pattern,
            tipOcnf(TipSmtEq(left ++ Seq(cas.expr) ++ right)))
      }
      TipSmtMatch( matchedTerm, newCases )
    } else {
      TipSmtEq( expression.exprs.map{ tipOcnf(_) })
    }
  }

  private def ocnfFun( expression: TipSmtFun): TipSmtExpression = {
    val TipSmtFun(funName, arguments) = expression
    val newSubexpressions = arguments map { tipOcnf(_) }
    if (newSubexpressions.exists(_.isInstanceOf[TipSmtIte])) {
      val Some((left, ite, right)) =
        find(
          newSubexpressions,
          { (expr:TipSmtExpression) => expr.isInstanceOf[TipSmtIte] })

      val TipSmtIte(cond, iftrue, iffalse) = ite
      val newIfTrue = TipSmtFun(funName, left ++ (Seq(iftrue)) ++ right)
      val newIfFalse = TipSmtFun(funName, left ++ (Seq(iffalse)) ++ right)
      TipSmtIte(cond, tipOcnf(newIfTrue), tipOcnf(newIfFalse))

    } else if (newSubexpressions.exists(_.isInstanceOf[TipSmtMatch])) {
      val Some( (left, matchExpr, right)) =
        find(
          newSubexpressions,
          { expr: TipSmtExpression => expr.isInstanceOf[TipSmtMatch] } )
      val TipSmtMatch( matchedTerm , cases ) = matchExpr
      val newCases = cases map {
        cas =>
          TipSmtCase(
            cas.pattern,
            tipOcnf(TipSmtFun(funName, left ++ Seq(cas.expr) ++ right)))
      }
      TipSmtMatch( matchedTerm, newCases )
    } else {
      TipSmtFun( funName, arguments.map{ tipOcnf(_) })
    }
  }
}

object find {
  def apply[T](
    elements: Seq[T], p: ( T ) => Boolean ): Option[( Seq[T], T, Seq[T] )] = {
    val index = elements.indexWhere( p )
    if ( index == -1 ) {
      None
    } else {
      Some( (
        elements.take( index ),
        elements( index ),
        elements.drop( index + 1 ) ) )
    }
  }
}

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

    val TipSmtAssertion( _, formula ) = tipSmtAssertion

    assumptions += compileExpression( formula, Map() ).asInstanceOf[Formula]
  }

  private def compileGoal( tipSmtGoal: TipSmtGoal ): Unit = {

    val TipSmtGoal( _, formula ) = tipSmtGoal

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
    sexp:     TipSmtExpression,
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
    expr: TipSmtExpression, freeVars: Map[String, Expr] ): Expr = expr match {
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

  def toProblem: TipProblem =
    TipProblem(
      ctx,
      typeDecls.values.toSeq diff datatypes.map { _.t }, datatypes,
      funDecls.values.toSeq diff functions.map { _.fun },
      functions,
      assumptions, And( goals ) )

  def compileTipProblem( tipProblem: TipSmtProblem ): TipSmtParser = {
    tipProblem.definitions.map { command =>
      command match {
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
    }
    this
  }
}

object TipSmtParser extends ExternalProgram {

  def parse( tipBench: InputFile ): TipProblem = {
    ( new TipSmtParser )
      .compileTipProblem( parser.TipSmtParser.parse( tipBench ) )
      .toProblem
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
