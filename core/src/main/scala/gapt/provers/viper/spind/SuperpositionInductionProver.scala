package gapt.provers.viper.spind

import gapt.expr.{ Atom, Const, Formula, Neg, Var, constants }
import gapt.proofs.lk.LKProof
import gapt.proofs.{ Sequent, withSection }
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.macros.WeakeningContractionMacroRule
import gapt.proofs.resolution.{ ResolutionToLKProof, mapInputClauses, structuralCNF }
import gapt.provers.escargot.Escargot
import gapt.provers.escargot.impl.Cls
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

    val seq0 = labeledSequentToHOLSequent( sequent )

    def go( axioms: Seq[Axiom] ): Option[LKProof] =
      withSection { section =>
        val seq = axioms.map( _.formula ) ++: seq0
        val ground = section.groundSequent( seq )

        val cnf = structuralCNF( ground )( ctx )
        val cnfMap = cnf.view.map( p => p.conclusion -> p ).toMap

        val prf = Escargot.getResolutionProofOrClauses( cnfMap.keySet.map( _.map( _.asInstanceOf[Atom] ) ) )

        prf match {
          case Left( clses ) =>
            val candidates = clses flatMap ( cls => cls.clause.elements flatMap ( f =>
              constants( f ) filter isInductive map ( ( cls, _ ) ) ) )

            val newAxioms = candidates flatMap {
              case ( cls, c ) =>
                val v = Var( nameGen.fresh( c.name ), c.ty )
                val target = Neg( cls.clause map ( replaceConst( _, c, v ) ) toFormula )
                StandardInductionAxioms( v, target ) toOption
            } filterNot ( a1 => axioms.exists( a2 => a1.formula.alphaEquals( a2.formula ) ) )

            if ( newAxioms.isEmpty )
              None
            else
              go( axioms ++ newAxioms )
          case Right( resolution ) =>
            val res = mapInputClauses( resolution )( cnfMap )
            val lk = ResolutionToLKProof( res )
            val wlk = WeakeningContractionMacroRule( lk, seq )
            val cut = cutAxioms( wlk, axioms.toList )
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

