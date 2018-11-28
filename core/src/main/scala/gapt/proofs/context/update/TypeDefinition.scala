package gapt.proofs.context.update

import gapt.expr.TBase

/**
 * Represents the definition of a base type ( uninterpreted base type,
 * the base type of a structurally inductive type, etc. )
 */
trait TypeDefinition extends Update {
  def ty: TBase
}
