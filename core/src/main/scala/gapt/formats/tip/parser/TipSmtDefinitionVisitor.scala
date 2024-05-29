package gapt.formats.tip.parser

abstract class TipSmtDefinitionVisitor[T, R] {

  def dispatch(definition: TipSmtCommand, data: T): R =
    definition match {
      case d @ TipSmtFunctionDefinition(_, _, _, _, _) =>
        visit(d, data)
      case d @ TipSmtDatatypesDeclaration(_) =>
        visit(d, data)
      case d @ TipSmtSortDeclaration(_, _) =>
        visit(d, data)
      case d @ TipSmtFunctionDeclaration(_, _, _, _) =>
        visit(d, data)
      case d @ TipSmtMutualRecursiveFunctionDefinition(_) =>
        visit(d, data)
      case d @ TipSmtGoal(_, _) =>
        visit(d, data)
      case d @ TipSmtAssertion(_, _) =>
        visit(d, data)
      case d @ TipSmtCheckSat() =>
        visit(d, data)
      case d @ TipSmtConstantDeclaration(_, _, _) =>
        visit(d, data)
    }

  def visit(definition: TipSmtFunctionDefinition, data: T): R
  def visit(definition: TipSmtDatatypesDeclaration, data: T): R
  def visit(definition: TipSmtSortDeclaration, data: T): R
  def visit(definition: TipSmtFunctionDeclaration, data: T): R
  def visit(definition: TipSmtMutualRecursiveFunctionDefinition, data: T): R
  def visit(definition: TipSmtGoal, data: T): R
  def visit(definition: TipSmtAssertion, data: T): R
  def visit(definition: TipSmtCheckSat, data: T): R
  def visit(definition: TipSmtConstantDeclaration, data: T): R

}
