package gapt.proofs.gaptic

import gapt.formats.babel.BabelSignature

import language.experimental.macros

trait LemmaHelper[T] {
  def apply[U]( tacticsProof: => Tactic[U] ): T = ???

  // Implementations need to define a function with the following signature:
  // (Overloading is implemented ad-hoc since we allow subclasses to add implicit arguments.)
  //
  // def handleTacticBlock( block: ProofState => ProofState ): T
}
