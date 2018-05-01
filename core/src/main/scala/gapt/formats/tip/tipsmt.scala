package gapt.formats.tip

import java.io.IOException

import gapt.expr._
import gapt.formats.tip.parser._
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
