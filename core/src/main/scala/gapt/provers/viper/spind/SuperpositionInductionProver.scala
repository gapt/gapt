package gapt.provers.viper.spind

import gapt.expr.{ Const, Formula, Var, constants }
import gapt.proofs.lk.LKProof
import gapt.proofs.Sequent
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.lk.rules.CutRule
import gapt.provers.escargot.Escargot
import gapt.provers.viper.aip.axioms.{ Axiom, StandardInductionAxioms }

object SuperpositionInductionProver extends SuperpositionInductionProver

class SuperpositionInductionProver {

  private implicit def labeledSequentToHOLSequent( sequent: Sequent[( String, Formula )] ): Sequent[Formula] =
    sequent map { case ( _, f ) => f }

  /**
   * Proves the given sequent by using induction.
   *
   * @param sequent The sequent to be proven.
   * @param ctx Defines the constants, types, etc.
   * @return An inductive proof the sequent is provable with the prover's induction schemes, otherwise None or
   *         the method does not terminate.
   */
  def inductiveLKProof( sequent: Sequent[( String, Formula )] )( implicit ctx: MutableContext ): Option[LKProof] = {
    val nameGen = ctx.newNameGenerator

    def replaceConst( f: Formula, c: Const, v: Var ): Formula =
      f.find( c ).foldLeft( f )( ( f, pos ) => f.replace( pos, v ) )

    def isInductive( c: Const ) = ctx getConstructors c.ty isDefined

    val seq = labeledSequentToHOLSequent( sequent )

    def go( axioms: Seq[Axiom] ): Option[LKProof] = {
      val prf = Escargot.getLKProof( axioms.map( _.formula ) ++: seq )

      prf match {
        case None =>
          val clses = Escargot.state.workedOff.clauses

          val candidates = clses flatMap ( cls => cls.clause.antecedent flatMap ( f =>
            constants( f ) filter isInductive map ( ( f, _ ) ) ) )

          val newAxioms = candidates flatMap {
            case ( f, c ) =>
              val v = Var( nameGen.fresh( c.name ), c.ty )
              val target = replaceConst( f, c, v )
              StandardInductionAxioms( v, target ) toOption
          } filterNot ( a1 => axioms.exists( a2 => a1.formula.alphaEquals( a2.formula ) ) )

          if ( newAxioms.isEmpty )
            None
          else
            go( axioms ++ newAxioms )
        case Some( lk ) =>
          val cut = cutAxioms( lk, axioms.toList )
          Some( cut )
      }
    }

    go( Seq() )
  }

  /**
   * Cuts the specified axioms from the proof.
   *
   * @param proof The proof from which some axioms are to be cut. The end-sequent of this proof must
   *              contain the given axioms.
   * @param axioms The axioms to be cut out of the proof.
   * @return A proof whose end-sequent does not contain the specified axioms.
   */
  private def cutAxioms( proof: LKProof, axioms: List[Axiom] ): LKProof =
    axioms.foldRight( proof ) { ( axiom, mainProof ) =>
      if ( mainProof.conclusion.antecedent contains axiom.formula )
        CutRule( axiom.proof, mainProof, axiom.formula )
      else
        mainProof
    }

}

