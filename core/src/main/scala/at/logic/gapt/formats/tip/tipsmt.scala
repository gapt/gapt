package at.logic.gapt.formats.tip

import java.io.IOException

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.formats.{ InputFile, StringInputFile }
import at.logic.gapt.formats.lisp._
import at.logic.gapt.utils.{ ExternalProgram, NameGenerator, runProcess }

import scala.collection.mutable

class TipSmtParser {
  val typeDecls = mutable.Map[String, TBase]()
  val funDecls = mutable.Map[String, Const]()

  def declare( t: TBase ): Unit = typeDecls( t.name ) = t
  def declare( f: Const ): Unit = funDecls( f.name ) = f

  val datatypes = mutable.Buffer[TipDatatype]()
  val functions = mutable.Buffer[TipFun]()
  val assumptions = mutable.Buffer[HOLFormula]()
  val goals = mutable.Buffer[HOLFormula]()

  typeDecls( "Bool" ) = To
  datatypes += TipDatatype( To, Seq( TipConstructor( TopC(), Seq() ), TipConstructor( BottomC(), Seq() ) ) )

  def parse( sexp: SExpression ) = sexp match {
    case LFun( "declare-sort", LAtom( name ), LAtom( "0" ) ) =>
      declare( TBase( name ) )
    case LFun( "declare-datatypes", LList(), LList( LFun( name, constructors @ _* ) ) ) =>
      val t = TBase( name )
      declare( t )
      val dt = TipDatatype( t, constructors map { parseConstructor( _, t ) } )
      datatypes += dt
      dt.constructors foreach { ctr =>
        declare( ctr.constr )
        ctr.projectors foreach declare
      }
    case LFun( "declare-const", LAtom( name ), LAtom( typeName ) ) =>
      declare( Const( name, typeDecls( typeName ) ) )
    case LFun( "declare-fun", LAtom( name ), LList( argTypes @ _* ), LAtom( retType ) ) =>
      declare( Const( name, FunctionType( typeDecls( retType ), argTypes map { case LAtom( argType ) => typeDecls( argType ) } ) ) )
    case LFun( "define-fun" | "define-fun-rec", LAtom( name ), LList( args @ _* ), LAtom( retType ), body ) =>
      val argVars = for ( LFun( argName, LAtom( argType ) ) <- args ) yield Var( argName, typeDecls( argType ) )
      val funConst = Const( name, FunctionType( typeDecls( retType ), argVars.map( _.exptype ) ) )
      declare( funConst )
      functions += TipFun( funConst, parseFunctionBody( body, funConst( argVars: _* ), argVars.map { v => v.name -> v }.toMap ) )
    case LFun( "assert", formula ) =>
      assumptions += parseExpression( formula, Map() ).asInstanceOf[HOLFormula]
    case LFun( "assert-not", formula ) =>
      goals += parseExpression( formula, Map() ).asInstanceOf[HOLFormula]
    case LFun( "check-sat" ) => ()
  }

  def parseConstructor( sexp: SExpression, ofType: Ty ) = sexp match {
    case LFun( name, fields @ _* ) =>
      val projectors = fields map { parseField( _, ofType ) }
      val fieldTypes = projectors map { _.exptype } map { case FunctionType( to, _ ) => to }
      TipConstructor( Const( name, FunctionType( ofType, fieldTypes ) ), projectors )
  }

  def parseField( sexp: SExpression, ofType: Ty ) = sexp match {
    case LFun( projector, LAtom( typename ) ) =>
      Const( projector, ofType -> typeDecls( typename ) )
  }

  def parseFunctionBody( sexp: SExpression, lhs: LambdaExpression, freeVars: Map[String, LambdaExpression] ): Seq[HOLFormula] = sexp match {
    case LFun( "match", LAtom( varName ), cases @ _* ) =>
      def handleCase( cas: SExpression ): Seq[HOLFormula] = cas match {
        case LFun( "case", LAtom( "default" ), body ) =>
          val coveredConstructors = cases collect {
            case LFun( "case", LFunOrAtom( constrName, _* ), _ ) if constrName != "default" =>
              funDecls( constrName )
          }
          val missingConstructors = datatypes.find( _.t == freeVars( varName ).exptype ).get.constructors.map( _.constr ) diff coveredConstructors
          missingConstructors flatMap { ctr =>
            val FunctionType( _, ts ) = ctr.exptype
            val nameGen = new NameGenerator( freeVars.keys )
            val vs = for ( t <- ts ) yield LAtom( nameGen fresh "x" )
            handleCase( LFun( "case", LFun( ctr.name, vs: _* ), body ) )
          }
        case LFun( "case", LFunOrAtom( constrName, argNames @ _* ), body ) =>
          require( freeVars( varName ).isInstanceOf[Var] )
          val constr = funDecls( constrName )
          val FunctionType( _, constrArgTypes ) = constr.exptype
          require( constrArgTypes.size == argNames.size )
          val args = for ( ( LAtom( name ), ty ) <- argNames zip constrArgTypes ) yield Var( name, ty )
          val subst = Substitution( freeVars( varName ).asInstanceOf[Var] -> constr( args: _* ) )
          parseFunctionBody(
            body,
            subst( lhs ),
            freeVars.mapValues( subst( _ ) ) ++ args.map { v => v.name -> v }
          )
      }
      cases flatMap handleCase
    case LFun( "ite", cond, ifTrue, ifFalse ) =>
      parseFunctionBody( ifFalse, lhs, freeVars ).map( -parseExpression( cond, freeVars ) --> _ ) ++
        parseFunctionBody( ifTrue, lhs, freeVars ).map( parseExpression( cond, freeVars ) --> _ )
    case LAtom( "true" )  => Seq( lhs.asInstanceOf[HOLFormula] )
    case LAtom( "false" ) => Seq( -lhs )
    case _ =>
      val expr = parseExpression( sexp, freeVars )
      Seq( if ( lhs.exptype == To ) lhs <-> expr else lhs === expr )
  }

  def parseExpression( sexp: SExpression, freeVars: Map[String, LambdaExpression] ): LambdaExpression = sexp match {
    case LAtom( name ) if freeVars contains name => freeVars( name )
    case LAtom( "false" )                        => Bottom()
    case LAtom( "true" )                         => Top()
    case LAtom( name )                           => funDecls( name )
    case LFun( "forall", LList( varNames @ _* ), formula ) =>
      val vars = for ( LFun( name, LAtom( typeName ) ) <- varNames ) yield Var( name, typeDecls( typeName ) )
      All.Block( vars, parseExpression( formula, freeVars ++ vars.map { v => v.name -> v } ) )
    case LFun( "exists", LList( varNames @ _* ), formula ) =>
      val vars = for ( LFun( name, LAtom( typeName ) ) <- varNames ) yield Var( name, typeDecls( typeName ) )
      Ex.Block( vars, parseExpression( formula, freeVars ++ vars.map { v => v.name -> v } ) )
    case LFun( "=", sexps @ _* ) =>
      val exprs = sexps map { parseExpression( _, freeVars ) }
      And( for ( ( a, b ) <- exprs zip exprs.tail )
        yield if ( exprs.head.exptype == To ) a <-> b else a === b )
    case LFun( "and", sexps @ _* ) => And( sexps map { parseExpression( _, freeVars ).asInstanceOf[HOLFormula] } )
    case LFun( "or", sexps @ _* )  => Or( sexps map { parseExpression( _, freeVars ).asInstanceOf[HOLFormula] } )
    case LFun( "not", sexp_ )      => Neg( parseExpression( sexp_, freeVars ) )
    case LFun( "=>", sexps @ _* )  => sexps map { parseExpression( _, freeVars ) } reduceRight { _ --> _ }
    case LFun( name, args @ _* ) =>
      funDecls( name )( args map { parseExpression( _, freeVars ) }: _* )
  }

  def toProblem: TipProblem =
    TipProblem(
      typeDecls.values.toSeq diff datatypes.map { _.t }, datatypes,
      funDecls.values.toSeq diff functions.map { _.fun },
      functions,
      assumptions, And( goals )
    )
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
        "--let-lift"
      ),
      tipBench.read,
      catchStderr = true
    ) ) )

  val isInstalled =
    try { runProcess( Seq( "tip", "--help" ), "" ); true }
    catch { case _: IOException => false }
}