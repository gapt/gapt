package at.logic.gapt.formats.tptp

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ HOLClause, HOLSequent }

object TPTPFOLExporter {
  def apply( formula: HOLFormula ): TptpFile =
    TptpFile( Seq( AnnotatedFormula( "fof", "formula", "conjecture", formula, Seq() ) ) )

  def apply( sequent: HOLSequent ): TptpFile = {
    require( freeVariables( sequent ).isEmpty )

    val file = Seq.newBuilder[TptpInput]

    sequent.antecedent.zipWithIndex foreach {
      case ( formula: FOLFormula, i ) =>
        file += AnnotatedFormula( "fof", s"ant_$i", "axiom", formula, Seq() )
    }

    if ( sequent.succedent.size <= 1 ) {
      sequent.succedent foreach {
        case formula: FOLFormula =>
          file += AnnotatedFormula( "fof", "suc_0", "conjecture", formula, Seq() )
      }
    } else {
      sequent.succedent.zipWithIndex foreach {
        case ( formula: FOLFormula, i ) =>
          file += AnnotatedFormula( "fof", s"suc_$i", "axiom", -formula, Seq() )
      }
    }

    TptpFile( file.result() )
  }

  def exportLabelledCNF( cnf: Iterable[( String, HOLClause )] ): TptpFile =
    TptpFile( cnf.toSeq.map( c => exportClause( c._2, c._1 ) ) )

  def exportCNF( cnf: Iterable[HOLClause] ): TptpFile =
    exportLabelledCNF( for ( ( c, i ) <- cnf.zipWithIndex ) yield s"clause_$i" -> c )

  def exportClause( clause: HOLClause, name: String ): TptpInput = {
    val ( _, disj: HOLFormula ) = tptpToString.renameVars( freeVariables( clause ).toSeq, clause.toDisjunction )
    AnnotatedFormula( "cnf", name, "axiom", disj, Seq() )
  }

  // convert a named list of clauses to a CNF refutation problem.
  def tptp_problem_named( ss: List[( String, HOLClause )] ) = exportLabelledCNF( ss )

  // Convert a sequent into a tptp proof problem.
  def tptp_proof_problem( seq: HOLSequent ) =
    apply( seq.toImplication )

  def tptp_proof_problem_split( seq: HOLSequent ) =
    apply( seq )

  // convert a list of clauses to a CNF refutation problem.
  def tptp_problem( ss: List[HOLClause] ) = exportCNF( ss )

}
