package gapt.formats.tip.transformation

import gapt.formats.tip.parser.TipSmtAssertion
import gapt.formats.tip.parser.TipSmtCheckSat
import gapt.formats.tip.parser.TipSmtCommand
import gapt.formats.tip.parser.TipSmtConstantDeclaration
import gapt.formats.tip.parser.TipSmtDatatypesDeclaration
import gapt.formats.tip.parser.TipSmtDefinitionVisitor
import gapt.formats.tip.parser.TipSmtFunctionDeclaration
import gapt.formats.tip.parser.TipSmtFunctionDefinition
import gapt.formats.tip.parser.TipSmtGoal
import gapt.formats.tip.parser.TipSmtMutualRecursiveFunctionDefinition
import gapt.formats.tip.parser.TipSmtSortDeclaration

abstract class TipSmtDefinitionTransformation[T] extends //
TipSmtDefinitionVisitor[T, TipSmtCommand] {
  override def visit(
    definition: TipSmtFunctionDefinition,
    data:       T ): TipSmtCommand = definition

  override def visit(
    definition: TipSmtDatatypesDeclaration,
    data:       T ): TipSmtCommand = definition

  override def visit(
    definition: TipSmtSortDeclaration,
    data:       T ): TipSmtCommand = definition

  override def visit(
    definition: TipSmtFunctionDeclaration,
    data:       T ): TipSmtCommand = definition

  override def visit(
    definition: TipSmtMutualRecursiveFunctionDefinition,
    data:       T ): TipSmtCommand = definition

  override def visit(
    definition: TipSmtGoal,
    data:       T ): TipSmtCommand = definition

  override def visit(
    definition: TipSmtAssertion,
    data:       T ): TipSmtCommand = definition

  override def visit(
    definition: TipSmtCheckSat,
    data:       T ): TipSmtCommand = definition

  override def visit(
    definition: TipSmtConstantDeclaration,
    data:       T ): TipSmtCommand = definition
}
