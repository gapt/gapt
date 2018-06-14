package gapt.formats.tip.parser

import gapt.expr.All
import gapt.expr.And
import gapt.expr.Apps
import gapt.expr.Bottom
import gapt.expr.Const
import gapt.expr.Eq
import gapt.expr.Ex
import gapt.expr.Expr
import gapt.expr.Formula
import gapt.expr.FunctionType
import gapt.expr.Imp
import gapt.expr.Neg
import gapt.expr.Or
import gapt.expr.TBase
import gapt.expr.To
import gapt.expr.Top
import gapt.expr.Ty
import gapt.expr.Var
import gapt.formats.lisp.LFun
import gapt.formats.lisp.LKeyword
import gapt.formats.lisp.LList
import gapt.formats.lisp.LSymbol
import gapt.formats.lisp.SExpression
import gapt.formats.tip.TipConstructor
import gapt.formats.tip.TipProblem

object toTipAst {

  def apply( expression: Expr ): TipSmtExpression = {
    expression match {
      case And( f1, f2 ) =>
        TipSmtAnd( Seq( toTipAst( f1 ), toTipAst( f2 ) ) )
      case Or( f1, f2 ) =>
        TipSmtOr( Seq( toTipAst( f1 ), toTipAst( f2 ) ) )
      case Imp( f1, f2 ) =>
        TipSmtImp( Seq( toTipAst( f1 ), toTipAst( f2 ) ) )
      case Eq( f1, f2 ) =>
        TipSmtEq( Seq( toTipAst( f1 ), toTipAst( f2 ) ) )
      case Neg( f ) =>
        TipSmtNot( toTipAst( f ) )
      case All( v, f ) =>
        TipSmtForall(
          Seq( TipSmtVariableDecl(
            v.name,
            TipSmtType( v.ty.asInstanceOf[TBase].name ) ) ), toTipAst( f ) )
      case Ex( v, f ) =>
        TipSmtExists(
          Seq( TipSmtVariableDecl(
            v.name,
            TipSmtType( v.ty.asInstanceOf[TBase].name ) ) ), toTipAst( f ) )
      case Bottom() =>
        TipSmtFalse
      case Top() =>
        TipSmtTrue
      case Var( name, _ ) =>
        TipSmtIdentifier( name )
      case Const( name, _, _ ) =>
        TipSmtIdentifier( name )
      case Apps( Const( name, _, _ ), exprs ) =>
        TipSmtFun( name, exprs.map { toTipAst( _ ) } )
    }
  }
}

object toSExpression {

  def apply( problem: TipProblem ): Seq[SExpression] = {

    def constructorToTipAst( constructor: TipConstructor ): TipSmtConstructor = {
      TipSmtConstructor(
        constructor.constr.name,
        Seq(),
        constructor
          .projectors
          .zip( constructor.fieldTypes )
          .map { case ( p, f ) => projectorToTipAst( p, f ) } )
    }

    def projectorToTipAst(
      projector: Const, fieldType: Ty ): TipSmtConstructorField = {
      TipSmtConstructorField(
        projector.name,
        TipSmtType( fieldType.asInstanceOf[TBase].name ) )
    }

    val sortsDeclarations =
      problem.sorts.map { s =>
        TipSmtSortDeclaration( s.name, Seq() )
      }

    val constructors =
      problem.datatypes.flatMap { _.constructors.map { _.constr } }
    val destructors =
      problem.datatypes.flatMap { _.constructors.flatMap { _.projectors } }

    val constantDeclarations =
      problem.uninterpretedConsts
        .filter { !( constructors ++ destructors ).contains( _ ) }
        .filter {
          c =>
            c.ty.isInstanceOf[TBase]
        }.map {
          c =>
            TipSmtConstantDeclaration(
              c.name,
              Seq(),
              TipSmtType( c.ty.asInstanceOf[TBase].name ) )
        }

    val functionConstantDeclarations =
      problem.uninterpretedConsts
        .filter { !( constructors ++ destructors ).contains( _ ) }
        .filter {
          c =>
            !c.ty.isInstanceOf[TBase]
        }.map {
          f =>
            val FunctionType( returnType, parameterTypes ) = f.ty
            TipSmtFunctionDeclaration(
              f.name,
              Seq(),
              parameterTypes.map { ty => TipSmtType( ty.asInstanceOf[TBase].name ) },
              TipSmtType( returnType.asInstanceOf[TBase].name ) )
        }

    val datatypeDeclarations =
      problem.datatypes
        .filter { _.t != To }
        .map {
          dt =>
            TipSmtDatatype(
              dt.t.name, Seq(),
              dt.constructors.map { constructorToTipAst } )
        }

    val functionDeclarations =
      problem.functions
        .map {
          f =>
            val FunctionType( TBase( returnType, _ ), parameterTypes ) = f.fun.ty
            TipSmtFunctionDeclaration(
              f.fun.name,
              Seq(),
              parameterTypes
                .map { ty => TipSmtType( ty.asInstanceOf[TBase].name ) },
              TipSmtType( returnType ) )
        }

    val goal = TipSmtGoal( Seq(), toTipAst( problem.goal ) )

    val assumptions: Seq[TipSmtAssertion] = problem.assumptions.map {
      a =>
        TipSmtAssertion( Seq(), toTipAst( a ) )
    } ++ problem.functions.flatMap {
      f =>
        f.definitions.map { d => TipSmtAssertion( Seq(), toTipAst( d ) ) }
    }

    sortsDeclarations.map { toSExpression( _ ) }
      .:+( toSExpression( TipSmtDatatypesDeclaration( datatypeDeclarations ) ) )
      .++( constantDeclarations.map { toSExpression( _ ) } )
      .++( functionConstantDeclarations.map { toSExpression( _ ) } )
      .++( functionDeclarations.map { toSExpression( _ ) } )
      .:+( toSExpression( goal ) )
      .++( assumptions.map { toSExpression( _ ) } )
  }

  def apply( problem: TipSmtProblem ): Seq[SExpression] = {
    problem.definitions.map { toSExpression( _ ) }
  }

  def apply( definition: TipSmtCommand ): SExpression = {
    definition match {
      case d @ TipSmtFunctionDefinition( _, _, _, _, _ ) =>
        toSExpression( d )
      case d @ TipSmtFunctionDeclaration( _, _, _, _ ) =>
        toSExpression( d )
      case d @ TipSmtMutualRecursiveFunctionDefinition( _ ) =>
        toSExpression( d )
      case d @ TipSmtDatatypesDeclaration( _ ) =>
        toSExpression( d )
      case d @ TipSmtConstantDeclaration( _, _, _ ) =>
        toSExpression( d )
      case d @ TipSmtGoal( _, _ ) =>
        toSExpression( d )
      case d @ TipSmtAssertion( _, _ ) =>
        toSExpression( d )
      case d @ TipSmtCheckSat() =>
        toSExpression( d )
      case d @ TipSmtSortDeclaration( _, _ ) =>
        toSExpression( d )
    }
  }

  def apply( definition: TipSmtSortDeclaration ): SExpression = {
    LFun(
      "declare-sort",
      LSymbol( definition.name ) +:
        keywordsToSExpression( definition.keywords ) :+
        LSymbol( "0" ): _* )
  }

  def apply( definition: TipSmtCheckSat ): SExpression = {
    LFun( "check-sat" )
  }

  def keywordsToSExpression( keywords: Seq[TipSmtKeyword] ): Seq[SExpression] = {
    keywords flatMap { toSExpression( _ ) }
  }

  def apply( keyword: TipSmtKeyword ): Seq[SExpression] = {
    keyword.argument match {
      case Some( argument ) =>
        Seq( LKeyword( keyword.name ), LSymbol( argument ) )
      case _ =>
        Seq( LKeyword( keyword.name ) )
    }
  }

  private def formalParameterListToSExpression(
    formalParameterList: Seq[TipSmtFormalParameter] ): SExpression = {
    LList( formalParameterList.map { toSExpression( _ ) } )
  }

  private def apply(
    formalParameter: TipSmtFormalParameter ): SExpression = {
    LList( LSymbol( formalParameter.name ), toSExpression( formalParameter.typ ) )
  }

  def apply( typ: TipSmtType ): SExpression = {
    LSymbol( typ.typename )
  }

  def apply( definition: TipSmtFunctionDefinition ): SExpression = {
    LFun(
      "define-fun-rec",
      LSymbol( definition.name ) +:
        keywordsToSExpression( definition.keywords ) :+
        formalParameterListToSExpression( definition.parameters ) :+
        toSExpression( definition.returnType ) :+
        toSExpression( definition.body ): _* )
  }

  def apply( definition: TipSmtFunctionDeclaration ): SExpression = {
    LFun(
      "declare-fun",
      LSymbol( definition.name ) +:
        keywordsToSExpression( definition.keywords ) :+
        LList( definition.argumentTypes map { toSExpression( _ ) } ) :+
        toSExpression( definition.returnType ): _* )
  }

  def apply( definition: TipSmtDatatypesDeclaration ): SExpression = {
    LFun(
      "declare-datatypes",
      LList(),
      LList( definition.datatypes.map { toSExpression( _ ) } ) )
  }

  def apply( datatype: TipSmtDatatype ): SExpression = {
    LFun(
      datatype.name,
      keywordsToSExpression( datatype.keywords ) ++:
        datatype.constructors.map { toSExpression( _ ) }: _* )
  }

  def apply( constructor: TipSmtConstructor ): SExpression = {
    LFun(
      constructor.name,
      keywordsToSExpression( constructor.keywords ) ++:
        constructor.fields.map { toSExpression( _ ) }: _* )
  }

  def apply( field: TipSmtConstructorField ): SExpression = {
    LFun( field.name, toSExpression( field.typ ) )
  }

  def apply( definition: TipSmtConstantDeclaration ): SExpression = {
    LFun(
      "declare-const",
      LSymbol( definition.name ) +:
        keywordsToSExpression( definition.keywords ) :+
        toSExpression( definition.typ ): _* )
  }

  def apply(
    definition: TipSmtMutualRecursiveFunctionDefinition ): SExpression = {
    LFun(
      "define-funs-rec",
      LList( definition.functions.map { sexprFunctionHeader } ),
      LList( definition.functions.map { f => toSExpression( f.body ) } ) )
  }

  def sexprFunctionHeader( function: TipSmtFunctionDefinition ): SExpression = {
    LFun(
      function.name,
      keywordsToSExpression( function.keywords ) :+
        formalParameterListToSExpression( function.parameters ) :+
        toSExpression( function.returnType ): _* )
  }

  def apply( definition: TipSmtGoal ): SExpression = {
    LFun(
      "prove",
      keywordsToSExpression( definition.keywords ) :+
        toSExpression( definition.expr ): _* )
  }

  def apply( definition: TipSmtAssertion ): SExpression = {
    LFun(
      "assert",
      keywordsToSExpression( definition.keywords ) :+
        toSExpression( definition.expr ): _* )
  }

  def apply( expression: TipSmtExpression ): SExpression = {
    expression match {
      case e @ TipSmtAnd( _ ) =>
        toSExpression( e )
      case e @ TipSmtOr( _ ) =>
        toSExpression( e )
      case e @ TipSmtImp( _ ) =>
        toSExpression( e )
      case e @ TipSmtEq( _ ) =>
        toSExpression( e )
      case e @ TipSmtIte( _, _, _ ) =>
        toSExpression( e )
      case e @ TipSmtMatch( _, _ ) =>
        toSExpression( e )
      case e @ TipSmtForall( _, _ ) =>
        toSExpression( e )
      case e @ TipSmtExists( _, _ ) =>
        toSExpression( e )
      case e @ TipSmtDistinct( _ ) =>
        toSExpression( e )
      case e @ TipSmtTrue =>
        LSymbol( "true" )
      case e @ TipSmtFalse =>
        LSymbol( "false" )
      case e @ TipSmtFun( _, _ ) =>
        toSExpression( e )
      case e @ TipSmtIdentifier( _ ) =>
        toSExpression( e )
      case e @ TipSmtNot( _ ) =>
        toSExpression( e )
    }
  }

  def apply( expression: TipSmtNot ): SExpression = {
    LFun( "not", toSExpression( expression.expr ) )
  }

  def apply( expression: TipSmtAnd ): SExpression = {
    LFun( "and", expression.exprs.map { toSExpression( _ ) }: _* )
  }

  def apply( expression: TipSmtOr ): SExpression = {
    LFun( "or", expression.exprs.map { toSExpression( _ ) }: _* )
  }

  def apply( expression: TipSmtEq ): SExpression = {
    LFun( "=", expression.exprs.map { toSExpression( _ ) }: _* )
  }

  def apply( expression: TipSmtImp ): SExpression = {
    LFun( "=>", expression.exprs.map { toSExpression( _ ) }: _* )
  }

  def apply( expression: TipSmtForall ): SExpression = {
    LFun(
      "forall",
      LList( expression.variables map { toSExpression( _ ) } ),
      toSExpression( expression.formula ) )
  }

  def apply( variableDecl: TipSmtVariableDecl ): SExpression = {
    LList( LSymbol( variableDecl.name ), toSExpression( variableDecl.typ ) )
  }

  def apply( expression: TipSmtExists ): SExpression = {
    LFun(
      "exists",
      LList( expression.variables map { toSExpression( _ ) } ),
      toSExpression( expression.formula ) )
  }

  def apply( expression: TipSmtMatch ): SExpression = {
    LFun(
      "match",
      toSExpression( expression.expr ) +:
        expression.cases.map { toSExpression( _ ) }: _* )
  }

  def apply( caseStatement: TipSmtCase ): SExpression = {
    LFun(
      "case",
      toSExpression( caseStatement.pattern ),
      toSExpression( caseStatement.expr ) )
  }

  def apply( pattern: TipSmtPattern ): SExpression = {
    pattern match {
      case TipSmtDefault =>
        LSymbol( "default" )
      case p @ TipSmtConstructorPattern( _, _ ) =>
        LFun( p.constructor.name, p.identifiers map { toSExpression( _ ) }: _* )
    }
  }

  def apply( identifier: TipSmtIdentifier ): SExpression = {
    LSymbol( identifier.name )
  }

  def apply( expression: TipSmtIte ): SExpression = {
    LFun(
      "ite",
      toSExpression( expression.cond ),
      toSExpression( expression.ifTrue ),
      toSExpression( expression.ifFalse ) )
  }

  def apply( expression: TipSmtFun ): SExpression = {
    LFun( expression.name, expression.arguments.map { toSExpression( _ ) }: _* )
  }

  def apply( expression: TipSmtDistinct ): SExpression = {
    LFun( "distinct", expression.expressions.map { toSExpression( _ ) }: _* )
  }
}
