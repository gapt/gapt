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

  def parse( sexp: SExpression ): Unit = sexp match {

    case LFun( "declare-sort", sort @ LSymbol( _ ), LKeyword( _ ), key @ LKeyword( _ ), rest @ _* ) =>
      parse( LFun( "declare-sort", sort +: key +: rest: _* ) )
    case LFun( "declare-sort", sort @ LSymbol( _ ), LKeyword( _ ), symbol @ LSymbol( _ ) ) =>
      parse( LFun( "declare-sort", sort, symbol ) )
    case LFun( "declare-sort", sort @ LSymbol( _ ), LKeyword( _ ), LSymbol( _ ), rest @ _* ) =>
      parse( LFun( "declare-sort", sort +: rest: _* ) )
    case LFun( "declare-sort", LSymbol( name ), LSymbol( "0" ) ) =>
      val t = TBase( name )
      declare( t )
      ctx += t

    case LFun( "declare-datatypes", LList(), LList( LFun( typename, LKeyword( _ ), LSymbol( _ ), rest @ _* ) ) ) =>
      parse( LFun( "declare-datatypes", LList(), LList( LFun( typename, rest: _* ) ) ) )
    case LFun( "declare-datatypes", LList(), LList( LFun( typename, LKeyword( _ ), rest @ _* ) ) ) =>
      parse( LFun( "declare-datatypes", LList(), LList( LFun( typename, rest: _* ) ) ) )
    case LFun( "declare-datatypes", LList(), LList( LFun( typename, constructors @ _* ) ) ) =>
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

    case LFun( "declare-const", LSymbol( constantName ), LKeyword( _ ), keyword @ LKeyword( _ ), rest @ _* ) =>
      parse( LFun( "declare-const", LSymbol( constantName ) +: keyword +: rest: _* ) )
    case LFun( "declare-const", LSymbol( constantName ), LKeyword( _ ), symbol @ LSymbol( _ ) ) =>
      parse( LFun( "declare-const", LSymbol( constantName ), symbol ) )
    case LFun( "declare-const", LSymbol( constantName ), LKeyword( _ ), LSymbol( _ ), rest @ _* ) =>
      parse( LFun( "declare-const", LSymbol( constantName ) +: rest: _* ) )
    case LFun( "declare-const", LSymbol( name ), LSymbol( typeName ) ) =>
      val c = Const( name, typeDecls( typeName ) )
      declare( c )
      ctx += c

    case LFun( "declare-fun", name @ LSymbol( _ ), LKeyword( _ ), LSymbol( _ ), rest @ _* ) =>
      parse( LFun( "declare-fun", name +: rest: _* ) )
    case LFun( "declare-fun", name @ LSymbol( _ ), LKeyword( _ ), rest @ _* ) =>
      parse( LFun( "declare-fun", name +: rest: _* ) )
    case LFun( "declare-fun", LSymbol( name ), LList( argTypes @ _* ), LSymbol( retType ) ) =>
      val f = Const( name, FunctionType(
        typeDecls( retType ),
        argTypes.asInstanceOf[Seq[LSymbol]].map { case LSymbol( argType ) => typeDecls( argType ) } ) )
      declare( f )
      ctx += f

    case LFun( cmd @ ( "define-fun" | "define-fun-rec" ), name @ LSymbol( _ ), LKeyword( _ ), LSymbol( _ ), rest @ _* ) =>
      parse( LFun( cmd, name +: rest: _* ) )
    case LFun( cmd @ ( "define-fun" | "define-fun-rec" ), name @ LSymbol( _ ), LKeyword( _ ), rest @ _* ) =>
      parse( LFun( cmd, name +: rest: _* ) )
    case LFun( "define-fun" | "define-fun-rec", LSymbol( name ), LList( args @ _* ), LSymbol( retType ), body ) =>
      val argVars = for ( LFun( argName, LSymbol( argType ) ) <- args ) yield Var( argName, typeDecls( argType ) )
      val funConst = Const( name, FunctionType( typeDecls( retType ), argVars.map( _.ty ) ) )
      declare( funConst )
      ctx += funConst
      functions += TipFun( funConst, parseFunctionBody( body, funConst( argVars: _* ), argVars.map { v => v.name -> v }.toMap ) )

    case LFun( assertion @ ( "assert" | "prove" | "assert-not" ), LKeyword( _ ), keyword @ LKeyword( _ ), rest @ _* ) =>
      parse( LFun( assertion, keyword +: rest: _* ) )

    case LFun( assertion @ ( "assert" | "prove" | "assert-not" ), LKeyword( _ ), formula ) =>
      parse( LFun( assertion, formula ) )

    case LFun( assertion @ ( "assert" | "prove" | "assert-not" ), LKeyword( _ ), LSymbol( _ ), rest @ _* ) =>
      parse( LFun( assertion, rest: _* ) )

    case LFun( "assert", formula ) =>
      assumptions += parseExpression( formula, Map() ).asInstanceOf[Formula]
    case LFun( "assert-not", formula ) =>
      goals += parseExpression( formula, Map() ).asInstanceOf[Formula]
    case LFun( "prove", formula ) =>
      goals += parseExpression( formula, Map() ).asInstanceOf[Formula]
    case LFun( "check-sat" ) => ()
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
