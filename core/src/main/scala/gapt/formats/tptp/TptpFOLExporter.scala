package gapt.formats.tptp

import gapt.expr._
import gapt.expr.formula.Formula
import gapt.expr.formula.hol.universalClosure
import gapt.expr.util.freeVariables
import gapt.proofs.{ HOLClause, HOLSequent, RichFormulaSequent }

object TptpFOLExporter {
  def apply( formula: Formula ): TptpFile =
    TptpFile( Seq( AnnotatedFormula( "fof", "formula", "conjecture", formula, Seq() ) ) )

  def apply( sequent: HOLSequent ): TptpFile = {
    require( freeVariables( sequent ).isEmpty, s"Sequent $sequent is not ground! " )

    val file = Seq.newBuilder[TptpInput]

    sequent.antecedent.zipWithIndex foreach {
      case ( formula, i ) =>
        file += AnnotatedFormula( "fof", s"ant_$i", "axiom", formula, Seq() )
    }

    if ( sequent.succedent.size <= 1 ) {
      sequent.succedent foreach ( formula =>
        file += AnnotatedFormula( "fof", "suc_0", "conjecture", formula, Seq() ) )
    } else {
      sequent.succedent.zipWithIndex foreach {
        case ( formula, i ) =>
          file += AnnotatedFormula( "fof", s"suc_$i", "axiom", -formula, Seq() )
      }
    }

    TptpFile( file.result() )
  }

  def apply( sequentSet: Iterable[HOLSequent] ): TptpFile =
    TptpFile( for ( ( seq, i ) <- sequentSet.toSeq.zipWithIndex )
      yield AnnotatedFormula( "fof", s"seq_$i", "axiom", universalClosure( seq.toDisjunction ), Seq() ) )

  def exportLabelledCNF( cnf: Iterable[( String, HOLClause )] ): TptpFile =
    TptpFile( cnf.toSeq.map( c => exportClause( c._2, c._1 ) ) )

  def exportCNF( cnf: Iterable[HOLClause] ): TptpFile =
    exportLabelledCNF( for ( ( c, i ) <- cnf.zipWithIndex ) yield s"clause_$i" -> c )

  def exportClause( clause: HOLClause, name: String ): TptpInput = {
    val ( _, disj: Formula ) = TptpToString.renameVars( freeVariables( clause ).toSeq, clause.toDisjunction )
    AnnotatedFormula( "cnf", name, "axiom", disj, Seq() )
  }

  /**
   * convert a named list of clauses to a CNF refutation problem.
   */
  def tptpProblemNamed( ss: List[( String, HOLClause )] ): TptpFile = exportLabelledCNF( ss )

  /**
   * Convert a sequent into a tptp proof problem.
   */
  def tptpProofProblem( seq: HOLSequent ) =
    apply( seq.toImplication )

  def tptpProofProblemSplit( seq: HOLSequent ) =
    apply( seq )

  /**
   * convert a list of clauses to a CNF refutation problem.
   */
  def tptpProblem( ss: List[HOLClause] ): TptpFile = exportCNF( ss )

}
