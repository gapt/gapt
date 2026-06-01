package gapt.formats.tip.parser

import gapt.expr.Apps
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Bottom
import gapt.expr.formula.Eq
import gapt.expr.formula.Ex
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.expr.ty.FunctionType
import gapt.expr.ty.TBase
import gapt.expr.ty.To
import gapt.expr.ty.Ty
import gapt.formats.lisp.LFun
import gapt.formats.lisp.LKeyword
import gapt.formats.lisp.LList
import gapt.formats.lisp.LSymbol
import gapt.formats.lisp.SExpression
import gapt.formats.tip.TipProblem
import gapt.proofs.context.update.InductiveType

object toTipAst {

  def apply(expression: Expr): TipSmtExpression = {
    expression match {
      case And(f1, f2) =>
        TipSmtAnd(Seq(toTipAst(f1), toTipAst(f2)))
      case Or(f1, f2) =>
        TipSmtOr(Seq(toTipAst(f1), toTipAst(f2)))
      case Imp(f1, f2) =>
        TipSmtImp(Seq(toTipAst(f1), toTipAst(f2)))
      case Eq(f1, f2) =>
        TipSmtEq(Seq(toTipAst(f1), toTipAst(f2)))
      case Neg(f) =>
        TipSmtNot(toTipAst(f))
      case All(v, f) =>
        TipSmtForall(
          Seq(TipSmtVariableDecl(
            v.name,
            TipSmtType(v.ty.asInstanceOf[TBase].name)
          )),
          toTipAst(f)
        )
      case Ex(v, f) =>
        TipSmtExists(
          Seq(TipSmtVariableDecl(
            v.name,
            TipSmtType(v.ty.asInstanceOf[TBase].name)
          )),
          toTipAst(f)
        )
      case Bottom() =>
        TipSmtFalse
      case Top() =>
        TipSmtTrue
      case Var(name, _) =>
        TipSmtIdentifier(name)
      case Const(name, _, _) =>
        TipSmtIdentifier(name)
      case Apps(Const(name, _, _), exprs) =>
        TipSmtFun(name, exprs.map { toTipAst(_) })
    }
  }
}

object toSExpression {

  def apply(problem: TipProblem): Seq[SExpression] = {

    def baseTypeToTipType(baseType: TBase): TipSmtType = {
      TipSmtType(baseType.name match {
        case "o" => "Bool"
        case _   => baseType.name
      })
    }

    def constructorToTipAst(
        constructor: InductiveType.Constructor
    ): TipSmtConstructor =
      TipSmtConstructor(
        constructor.constant.name,
        Seq(),
        constructor.fields.map { f => projectorToTipAst(f.projector.get, f.ty) }
      )

    def projectorToTipAst(
        projector: Const,
        fieldType: Ty
    ): TipSmtConstructorField = {
      TipSmtConstructorField(
        projector.name,
        baseTypeToTipType(fieldType.asInstanceOf[TBase])
      )
    }

    val sortsDeclarations =
      problem.sorts.map { s =>
        TipSmtSortDeclaration(s.name, Seq())
      }

    val constructors =
      problem.datatypes.flatMap { _.constructorConstants }

    val destructors =
      problem.datatypes.flatMap { _.constructors.flatMap { _.fields.flatMap(_.projector) } }

    val constantDeclarations =
      problem.uninterpretedConsts
        .filter { !(constructors ++ destructors).contains(_) }
        .filter {
          c =>
            c.ty.isInstanceOf[TBase]
        }.map {
          c =>
            TipSmtConstantDeclaration(
              c.name,
              Seq(),
              baseTypeToTipType(c.ty.asInstanceOf[TBase])
            )
        }

    val functionConstantDeclarations =
      problem.uninterpretedConsts
        .filter { !(constructors ++ destructors).contains(_) }
        .filter {
          c =>
            !c.ty.isInstanceOf[TBase]
        }.map {
          f =>
            val FunctionType(returnType, parameterTypes) = f.ty: @unchecked
            TipSmtFunctionDeclaration(
              f.name,
              Seq(),
              parameterTypes.map {
                ty => baseTypeToTipType(ty.asInstanceOf[TBase])
              },
              baseTypeToTipType(returnType.asInstanceOf[TBase])
            )
        }

    val datatypeDeclarations =
      problem.datatypes
        .filter { _.baseType != To }
        .map {
          dt =>
            TipSmtDatatype(
              dt.baseType.name,
              Seq(),
              dt.constructors.map { constructorToTipAst }
            )
        }

    val functionDeclarations =
      problem.functions
        .map {
          f =>
            val FunctionType(returnType @ TBase(_, _), parameterTypes) =
              f.fun.ty: @unchecked

            TipSmtFunctionDeclaration(
              f.fun.name,
              Seq(),
              parameterTypes
                .map { ty => baseTypeToTipType(ty.asInstanceOf[TBase]) },
              baseTypeToTipType(returnType)
            )
        }

    val goal = TipSmtGoal(Seq(), toTipAst(problem.goal))

    val assumptions: Seq[TipSmtAssertion] = problem.assumptions.map {
      a =>
        TipSmtAssertion(Seq(), toTipAst(a))
    } ++ problem.functions.flatMap {
      f =>
        f.definitions.map { d => TipSmtAssertion(Seq(), toTipAst(d)) }
    }

    sortsDeclarations.map { sortDeclarationToSExpression(_) }
      .:+(datatypesDeclarationToSExpression(TipSmtDatatypesDeclaration(datatypeDeclarations)))
      .++(constantDeclarations.map { constantDeclarationToSExpression(_) })
      .++(functionConstantDeclarations.map { functionDeclarationToSExpression(_) })
      .++(functionDeclarations.map { functionDeclarationToSExpression(_) })
      .++(assumptions.map { assertionToSExpression(_) })
      .:+(goalToSExpression(goal))
  }

  def problemToSExpression(problem: TipSmtProblem): Seq[SExpression] = {
    problem.definitions.map { commandToSExpression(_) }
  }

  def commandToSExpression(definition: TipSmtCommand): SExpression = {
    definition match {
      case d @ TipSmtFunctionDefinition(_, _, _, _, _) =>
        functionDefinitionToSExpression(d)
      case d @ TipSmtFunctionDeclaration(_, _, _, _) =>
        functionDeclarationToSExpression(d)
      case d @ TipSmtMutualRecursiveFunctionDefinition(_) =>
        mutualRecursiveFunctionDefinitionToSExpression(d)
      case d @ TipSmtDatatypesDeclaration(_) =>
        datatypesDeclarationToSExpression(d)
      case d @ TipSmtConstantDeclaration(_, _, _) =>
        constantDeclarationToSExpression(d)
      case d @ TipSmtGoal(_, _) =>
        goalToSExpression(d)
      case d @ TipSmtAssertion(_, _) =>
        assertionToSExpression(d)
      case d @ TipSmtCheckSat() =>
        checkSatToSExpression()
      case d @ TipSmtSortDeclaration(_, _) =>
        sortDeclarationToSExpression(d)
    }
  }

  def sortDeclarationToSExpression(definition: TipSmtSortDeclaration): SExpression = {
    LFun(
      "declare-sort",
      LSymbol(definition.name) +:
        keywordsToSExpression(definition.keywords) :+
        LSymbol("0")*
    )
  }

  def checkSatToSExpression(): SExpression = {
    LFun("check-sat")
  }

  def keywordsToSExpression(keywords: Seq[TipSmtKeyword]): Seq[SExpression] = {
    keywords.flatMap { keywordToSExpression(_) }
  }

  def keywordToSExpression(keyword: TipSmtKeyword): Seq[SExpression] = {
    keyword.argument match {
      case Some(argument) =>
        Seq(LKeyword(keyword.name), LSymbol(argument))
      case _ =>
        Seq(LKeyword(keyword.name))
    }
  }

  private def formalParameterListToSExpression(
      formalParameterList: Seq[TipSmtFormalParameter]
  ): SExpression = {
    LList(formalParameterList.map { formalParameterToSExpression(_) })
  }

  private def formalParameterToSExpression(
      formalParameter: TipSmtFormalParameter
  ): SExpression = {
    LList(LSymbol(formalParameter.name), typeToSExpression(formalParameter.typ))
  }

  def typeToSExpression(typ: TipSmtType): SExpression = {
    LSymbol(typ.typename)
  }

  def functionDefinitionToSExpression(definition: TipSmtFunctionDefinition): SExpression = {
    LFun(
      "define-fun-rec",
      LSymbol(definition.name) +:
        keywordsToSExpression(definition.keywords) :+
        formalParameterListToSExpression(definition.parameters) :+
        typeToSExpression(definition.returnType) :+
        expressionToSExpression(definition.body)*
    )
  }

  def functionDeclarationToSExpression(definition: TipSmtFunctionDeclaration): SExpression = {
    LFun(
      "declare-fun",
      LSymbol(definition.name) +:
        keywordsToSExpression(definition.keywords) :+
        LList(definition.argumentTypes.map { typeToSExpression(_) }) :+
        typeToSExpression(definition.returnType)*
    )
  }

  def datatypesDeclarationToSExpression(definition: TipSmtDatatypesDeclaration): SExpression = {
    LFun(
      "declare-datatypes",
      LList(),
      LList(definition.datatypes.map { datatypeToSExpression(_) })
    )
  }

  def datatypeToSExpression(datatype: TipSmtDatatype): SExpression = {
    LFun(
      datatype.name,
      keywordsToSExpression(datatype.keywords) ++:
        datatype.constructors.map { constructorToSExpression(_) }*
    )
  }

  def constructorToSExpression(constructor: TipSmtConstructor): SExpression = {
    LFun(
      constructor.name,
      keywordsToSExpression(constructor.keywords) ++:
        constructor.fields.map { constructorFieldToSExpression(_) }*
    )
  }

  def constructorFieldToSExpression(field: TipSmtConstructorField): SExpression = {
    LFun(field.name, typeToSExpression(field.typ))
  }

  def constantDeclarationToSExpression(definition: TipSmtConstantDeclaration): SExpression = {
    LFun(
      "declare-const",
      LSymbol(definition.name) +:
        keywordsToSExpression(definition.keywords) :+
        typeToSExpression(definition.typ)*
    )
  }

  def mutualRecursiveFunctionDefinitionToSExpression(
      definition: TipSmtMutualRecursiveFunctionDefinition
  ): SExpression = {
    LFun(
      "define-funs-rec",
      LList(definition.functions.map { sexprFunctionHeader }),
      LList(definition.functions.map { f => expressionToSExpression(f.body) })
    )
  }

  def sexprFunctionHeader(function: TipSmtFunctionDefinition): SExpression = {
    LFun(
      function.name,
      keywordsToSExpression(function.keywords) :+
        formalParameterListToSExpression(function.parameters) :+
        typeToSExpression(function.returnType)*
    )
  }

  def goalToSExpression(definition: TipSmtGoal): SExpression = {
    LFun(
      "prove",
      keywordsToSExpression(definition.keywords) :+
        expressionToSExpression(definition.expr)*
    )
  }

  def assertionToSExpression(definition: TipSmtAssertion): SExpression = {
    LFun(
      "assert",
      keywordsToSExpression(definition.keywords) :+
        expressionToSExpression(definition.expr)*
    )
  }

  def expressionToSExpression(expression: TipSmtExpression): SExpression = {
    expression match {
      case e @ TipSmtAnd(_) =>
        andToSExpression(e)
      case e @ TipSmtOr(_) =>
        orToSExpression(e)
      case e @ TipSmtImp(_) =>
        impToSExpression(e)
      case e @ TipSmtEq(_) =>
        eqToSExpression(e)
      case e @ TipSmtIte(_, _, _) =>
        iteToSExpression(e)
      case e @ TipSmtMatch(_, _) =>
        matchToSExpression(e)
      case e @ TipSmtForall(_, _) =>
        forallToSExpression(e)
      case e @ TipSmtExists(_, _) =>
        existsToSExpression(e)
      case e @ TipSmtDistinct(_) =>
        distinctToSExpression(e)
      case TipSmtTrue =>
        LSymbol("true")
      case TipSmtFalse =>
        LSymbol("false")
      case e @ TipSmtFun(_, _) =>
        funToSExpression(e)
      case e @ TipSmtIdentifier(_) =>
        identifierToSExpression(e)
      case e @ TipSmtNot(_) =>
        notToSExpression(e)
    }
  }

  def notToSExpression(expression: TipSmtNot): SExpression = {
    LFun("not", expressionToSExpression(expression.expr))
  }

  def andToSExpression(expression: TipSmtAnd): SExpression = {
    LFun("and", expression.exprs.map { expressionToSExpression(_) }*)
  }

  def orToSExpression(expression: TipSmtOr): SExpression = {
    LFun("or", expression.exprs.map { expressionToSExpression(_) }*)
  }

  def eqToSExpression(expression: TipSmtEq): SExpression = {
    LFun("=", expression.exprs.map { expressionToSExpression(_) }*)
  }

  def impToSExpression(expression: TipSmtImp): SExpression = {
    LFun("=>", expression.exprs.map { expressionToSExpression(_) }*)
  }

  def forallToSExpression(expression: TipSmtForall): SExpression = {
    LFun(
      "forall",
      LList(expression.variables.map { variableDeclToSExpression(_) }),
      expressionToSExpression(expression.formula)
    )
  }

  def variableDeclToSExpression(variableDecl: TipSmtVariableDecl): SExpression = {
    LList(LSymbol(variableDecl.name), typeToSExpression(variableDecl.typ))
  }

  def existsToSExpression(expression: TipSmtExists): SExpression = {
    LFun(
      "exists",
      LList(expression.variables.map { variableDeclToSExpression(_) }),
      expressionToSExpression(expression.formula)
    )
  }

  def matchToSExpression(expression: TipSmtMatch): SExpression = {
    LFun(
      "match",
      expressionToSExpression(expression.expr) +:
        expression.cases.map { caseToSExpression(_) }*
    )
  }

  def caseToSExpression(caseStatement: TipSmtCase): SExpression = {
    LFun(
      "case",
      patternToSExpression(caseStatement.pattern),
      expressionToSExpression(caseStatement.expr)
    )
  }

  def patternToSExpression(pattern: TipSmtPattern): SExpression = {
    pattern match {
      case TipSmtDefault =>
        LSymbol("default")
      case p @ TipSmtConstructorPattern(_, _) =>
        LFun(p.constructor.name, p.identifiers.map { identifierToSExpression(_) }*)
    }
  }

  def identifierToSExpression(identifier: TipSmtIdentifier): SExpression = {
    LSymbol(identifier.name)
  }

  def iteToSExpression(expression: TipSmtIte): SExpression = {
    LFun(
      "ite",
      expressionToSExpression(expression.cond),
      expressionToSExpression(expression.ifTrue),
      expressionToSExpression(expression.ifFalse)
    )
  }

  def funToSExpression(expression: TipSmtFun): SExpression = {
    LFun(expression.name, expression.arguments.map { expressionToSExpression(_) }*)
  }

  def distinctToSExpression(expression: TipSmtDistinct): SExpression = {
    LFun("distinct", expression.expressions.map { expressionToSExpression(_) }*)
  }
}
