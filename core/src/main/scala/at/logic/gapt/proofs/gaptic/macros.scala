package at.logic.gapt.proofs.gaptic

import at.logic.gapt.formats.babel.BabelSignature

import language.experimental.macros

trait LemmaHelper[T] {
  def apply[U]( tacticsProof: => Tactical[U] ): T = macro LemmaMacros.helperImpl

  // Implementations need to define a function with the following signature:
  // (Overloading is implemented ad-hoc since we allow subclasses to add implicit arguments.)
  //
  // def handleTacticBlock( block: ProofState => ProofState ): T
}

object LemmaMacros {

  def use[T]( proofState: ProofState, tactical: Tactical[T] )( implicit sig: BabelSignature ): ProofState =
    ( try tactical( proofState ) catch {
      case t: Throwable =>
        throw new TacticFailureException(
          s"Exception when applying $tactical to proof state with sub goals:\n" +
            proofState.subGoals.map { _.toPrettyString }.mkString( "\n" ),
          t )
    } ) match {
      case Right( ( _, newState ) ) => newState
      case Left( error ) =>
        throw new TacticFailureException( error.toSigRelativeString )
    }

  import reflect.macros._
  def constructProofState( c: blackbox.Context )( proofState0: c.Tree, tacticsProof: c.Tree ): c.Tree = {
    import c.universe._
    val proofState = TermName( c.freshName( "proofState" ) )

    val lemmaMacros = symbolOf[LemmaMacros.type].asClass.module
    val tacticsStmts = tacticsProof match {
      case q"{..$stmts}" =>
        for ( stmt <- stmts )
          yield atPos( stmt.pos )( q"$proofState = $lemmaMacros.use($proofState, $stmt)" )
    }

    q"""
      var $proofState = $proofState0

      ..$tacticsStmts

      $proofState
    """
  }

  def helperImpl( c: blackbox.Context )( tacticsProof: c.Tree ): c.Tree = {
    import c.universe._
    val proofState0 = TermName( c.freshName( "proofState" ) )
    val helper = c.prefix
    q"""
       $helper.handleTacticBlock(${q"val $proofState0 = $EmptyTree"} =>
          ${c untypecheck constructProofState( c )( Ident( proofState0 ), tacticsProof )})
     """
  }
}
