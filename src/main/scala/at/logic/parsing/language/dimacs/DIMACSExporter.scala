package at.logic.parsing.language.dimacs

import at.logic.language.hol._
import at.logic.calculi.resolution._
import at.logic.models.MapBasedInterpretation

class DIMACSExporter( val clauses: List[FClause] ) {
  val atoms = clauses.flatMap( c => c.neg ++ c.pos ).distinct;
  val atom_map = atoms.zip( 1 to atoms.size ).toMap
  val nl = System.getProperty( "line.separator" )

  private def getAtom( i: Int ) = {
    atom_map.find( p => i == p._2 ) match {
      case Some( ( a, n ) ) => Some( a )
      case _                => None
    }
  }

  private def getDIMACSString( atom: HOLFormula, pos: Boolean ): String =
    if ( pos ) atom_map.get( atom ).get.toString else "-" + atom_map.get( atom ).get

  private def getDIMACSString( clause: FClause ): String =
    {
      val sb = new StringBuilder()

      def atoms_to_str( as: Seq[HOLFormula], pol: Boolean ) = as.foreach( a => {
        sb.append( getDIMACSString( a, pol ) );
        sb.append( " " );
      } )

      atoms_to_str( clause.pos, true )
      atoms_to_str( clause.neg, false )

      sb.toString()
    }

  def getDIMACSString(): String = {
    val sb = new StringBuilder()

    sb.append( "p cnf " + atom_map.size + " " + clauses.size + nl )

    // construct minisat text input
    clauses.foreach( c =>
      {
        sb.append( getDIMACSString( c ) )
        sb.append( " 0" )
        sb.append( nl )
      } )

    sb.toString()
  }

  def getInterpretation( dimacs_out: String ) = {
    val lines = dimacs_out.split( nl )
    val res = if ( lines( 0 ).equals( "SAT" ) ) {
      Some( lines( 1 ).split( " " ).
        filter( lit => !lit.equals( "" ) && !lit.charAt( 0 ).equals( '0' ) ).
        map( lit =>
          if ( lit.charAt( 0 ) == '-' ) {
            // negative literal
            ( getAtom( lit.substring( 1 ).toInt ).get, false )
          } else {
            // positive literal
            ( getAtom( lit.toInt ).get, true )
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
