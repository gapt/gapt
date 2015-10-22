package at.logic.gapt.formats.tip

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.formats.lisp._
import at.logic.gapt.utils.runProcess

import scala.collection.mutable
import scala.io.Source

class TipSmtParser {
  val typeDecls = mutable.Map[String, Ty]()
  val funDecls = mutable.Map[String, Const]()

  def declare( t: TBase ): Unit = typeDecls( t.name ) = t
  def declare( f: Const ): Unit = funDecls( f.name ) = f

  val datatypes = mutable.Buffer[TipDatatype]()
  val functions = mutable.Buffer[TipFun]()
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
      val argVars = args.map { case LFun( argName, LAtom( argType ) ) => Var( argName, typeDecls( argType ) ) }
      val funConst = Const( name, FunctionType( typeDecls( retType ), argVars.map( _.exptype ) ) )
      declare( funConst )
      functions += TipFun( funConst, parseFunctionBody( body, funConst( argVars: _* ), argVars.toSet ) )
    case LFun( "assert", formula ) =>
      goals += -parseExpression( formula, Set() )
    case LFun( "assert-not", formula ) =>
      goals += parseExpression( formula, Set() ).asInstanceOf[HOLFormula]
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

  def parseFunctionBody( sexp: SExpression, lhs: LambdaExpression, freeVars: Set[Var] ): Seq[HOLFormula] = sexp match {
    case LFun( "match", LAtom( varName ), cases @ _* ) =>
      cases flatMap {
        case LFun( "case", LFunOrAtom( constrName, argNames @ _* ), body ) =>
          val constr = funDecls( constrName )
          val FunctionType( _, constrArgTypes ) = constr.exptype
          require( constrArgTypes.size == argNames.size )
          val args = ( argNames.map { case LAtom( name ) => name }, constrArgTypes ).zipped map { Var( _, _ ) }
          val subst = Substitution( freeVars.find( _.name == varName ).get -> constr( args: _* ) )
          parseFunctionBody( body, lhs, freeVars ++ args ) map { subst( _ ) }
      }
    case LFun( "ite", cond, ifTrue, ifFalse ) =>
      parseFunctionBody( ifFalse, lhs, freeVars ).map( -parseExpression( cond, freeVars ) --> _ ) ++
        parseFunctionBody( ifTrue, lhs, freeVars ).map( parseExpression( cond, freeVars ) --> _ )
    case LAtom( "true" )  => Seq( lhs.asInstanceOf[HOLFormula] )
    case LAtom( "false" ) => Seq( -lhs )
    case _                => Seq( Eq( lhs, parseExpression( sexp, freeVars ) ) )
  }

  def parseExpression( sexp: SExpression, freeVars: Set[Var] ): LambdaExpression = sexp match {
    case LAtom( name ) if freeVars exists { _.name == name } => freeVars find { _.name == name } get
    case LAtom( name )                                       => funDecls( name )
    case LFun( "forall", LList( varNames @ _* ), formula ) =>
      val vars = varNames map { case LFun( name, LAtom( typeName ) ) => Var( name, typeDecls( typeName ) ) }
      All.Block( vars, parseExpression( formula, freeVars ++ vars ) )
    case LFun( "=", sexps @ _* ) =>
      sexps map { parseExpression( _, freeVars ) } reduce { Eq( _, _ ) }
    case LFun( "and", sexps @ _* ) => And( sexps map { parseExpression( _, freeVars ).asInstanceOf[HOLFormula] } )
    case LFun( "or", sexps @ _* )  => Or( sexps map { parseExpression( _, freeVars ).asInstanceOf[HOLFormula] } )
    case LFun( "=>", sexps @ _* )  => sexps map { parseExpression( _, freeVars ) } reduceRight { _ --> _ }
    case LFun( name, args @ _* ) =>
      funDecls( name )( args map { parseExpression( _, freeVars ) }: _* )
  }

  def toProblem: TipProblem =
    TipProblem( datatypes.toSeq, functions.toSeq, And( goals ) )
}

object TipSmtParser {
  def parse( tipBench: String ): TipProblem = {
    val tipSmtParser = new TipSmtParser
    SExpressionParser.parseString( tipBench ) foreach tipSmtParser.parse
    tipSmtParser.toProblem
  }

  def parseFile( filename: String ): TipProblem =
    parse( Source fromFile filename mkString )

  def fixupAndParse( contents: String ): TipProblem =
    parse( runProcess(
      Seq(
        "tip",
        "--type-skolem-conjecture",
        "--add-match", "--commute-match",
        "--lambda-lift", "--axiomatize-lambdas",
        "--monomorphise",
        "--if-to-bool-op",
        "--uncurry-theory",
        "--let-lift"
      ),
      contents
    ) )

  def fixupAndParseFile( filename: String ): TipProblem =
    fixupAndParse( Source fromFile filename mkString )
}