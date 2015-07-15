package at.logic.gapt.formats.dimacs

import at.logic.gapt.expr._
import at.logic.gapt.models.MapBasedInterpretation
import at.logic.gapt.proofs.resolution._

/**
 * A helper class that provides core functionality for both DIMACSExporter (SAT)
 * as well as WDIMACSExporter (MaxSAT).
 */
class DIMACSHelper( val clauses: List[HOLClause] ) {
  val atoms = clauses.flatMap( c => c.negative ++ c.positive ).distinct
  val atom_map = atoms.zip( 1 to atoms.size ).toMap
  val reverseAtomMap = atom_map.map( _.swap )
  val nl = System.getProperty( "line.separator" )

  def getAtom( i: Int ): Option[HOLFormula] = reverseAtomMap get i
}

object readDIMACS {
  def apply( dimacs_out: String, helper: DIMACSHelper ) = {
    val lines = dimacs_out.split( helper.nl )
    val res = if ( lines( 0 ).equals( "SAT" ) ) {
      Some( lines( 1 ).split( " " ).
        filter( lit => !lit.equals( "" ) && !lit.charAt( 0 ).equals( '0' ) ).
        map( lit =>
          if ( lit.charAt( 0 ) == '-' ) {
            // negative literal
            ( helper.getAtom( lit.substring( 1 ).toInt ).get, false )
          } else {
            // positive literal
            ( helper.getAtom( lit.toInt ).get, true )
          } )
        .toSet.toMap )
    } else {
      // unsatisfiable
      None
    }

    res match {
      case Some( model ) => Some( new MapBasedInterpretation( model ) )
      case None          => None
    }
  }
}

object writeDIMACS {
  def apply( helper: DIMACSHelper ) = {
    def getDIMACSString1( atom: HOLAtom, pos: Boolean ): String =
      if ( pos ) helper.atom_map.get( atom ).get.toString else "-" + helper.atom_map.get( atom ).get

    def getDIMACSString( clause: HOLClause ): String =
      {
        val sb = new StringBuilder()

        def atoms_to_str( as: Seq[HOLAtom], pol: Boolean ) = as.foreach( a => {
          sb.append( getDIMACSString1( a, pol ) );
          sb.append( " " );
        } )

        atoms_to_str( clause.positive, true )
        atoms_to_str( clause.negative, false )

        sb.toString()
      }

    val sb = new StringBuilder()

    sb.append( "p cnf " + helper.atom_map.size + " " + helper.clauses.size + helper.nl )

    // construct minisat text input
    helper.clauses.foreach( c =>
      {
        sb.append( getDIMACSString( c ) )
        sb.append( " 0" )
        sb.append( helper.nl )
      } )

    sb.toString()
  }
}

