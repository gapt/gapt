package gapt.proofs.lk

import gapt.expr.Var

/**
 * Use this trait for rules that use eigenvariables.
 *
 */
trait Eigenvariable {
  def eigenVariable: Var
}
