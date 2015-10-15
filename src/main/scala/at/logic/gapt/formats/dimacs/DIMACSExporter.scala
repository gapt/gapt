package at.logic.gapt.formats.dimacs

import at.logic.gapt.expr._
import at.logic.gapt.models.MapBasedInterpretation
import at.logic.gapt.proofs.{ Clause, HOLClause }

import scala.collection.mutable

object DIMACS {
  type Atom = Int
  type Literal = Int
  type Clause = Seq[Literal]
  type CNF = Seq[Clause]
  type Model = Seq[Literal]

  def maxAtom( cnf: CNF ) = {
    val atoms = cnf.flatten.map( math.abs )
    if ( atoms.nonEmpty ) atoms.max else 0
  }
}

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

class DIMACSEncoding {
  private val atomMap = mutable.Map[HOLAtom, DIMACS.Atom]()
  private val reverseAtomMap = mutable.Map[DIMACS.Atom, HOLAtom]()
  private var atomIndex = 1

  def encodeAtom( atom: HOLAtom ): DIMACS.Atom =
    atomMap.getOrElse( atom, {
      val idx = atomIndex
      atomIndex += 1

      atomMap( atom ) = idx
      reverseAtomMap( idx ) = atom

      idx
    } )

  def encodeClause( clause: HOLClause ): DIMACS.Clause =
    clause.map( encodeAtom ).map( -_, +_ ).elements

  def encodeCNF( cnf: TraversableOnce[HOLClause] ): DIMACS.CNF =
    cnf.map( encodeClause ).toSeq

  def decodeAtom( i: DIMACS.Atom ) = reverseAtomMap( i )
  def decodeAtomOption( i: DIMACS.Atom ) = reverseAtomMap.get( i )

  def decodeClause( clause: DIMACS.Clause ) =
    Clause( clause.filter( _ < 0 ), clause.filter( _ > 0 ) ).map( l => decodeAtom( math.abs( l ) ) )

  def decodeModel( model: DIMACS.Model ) =
    new MapBasedInterpretation( model map {
      case l if l > 0 => decodeAtom( l ) -> true
      case l if l < 0 => decodeAtom( -l ) -> false
    } toMap )
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

  def applyNew( dimacsOutput: String ): Option[DIMACS.Model] = {
    val lines = dimacsOutput.split( "\n" )
    if ( lines.nonEmpty && lines( 0 ) == "SAT" ) {
      Some( lines.tail.flatMap( _.trim split " " ).takeWhile( _ != "0" ).map( _.toInt ) )
    } else {
      None
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

  def applyNew( cnf: DIMACS.CNF ): String = {
    val dimacsInput = new StringBuilder

    dimacsInput ++= s"p cnf ${DIMACS maxAtom cnf} ${cnf size}\n"
    cnf foreach { clause =>
      dimacsInput ++= s"${clause mkString " "} 0\n"
    }

    dimacsInput.result()
  }
}

object writeWDIMACS {
  def apply( wcnf: Seq[( DIMACS.Clause, Int )], threshold: Int ): String = {
    val dimacsInput = new StringBuilder
    dimacsInput ++= s"p wcnf ${DIMACS maxAtom wcnf.map( _._1 )} ${wcnf size} $threshold\n"
    wcnf foreach {
      case ( clause, weight ) =>
        dimacsInput ++= s"$weight ${clause mkString " "} 0\n"
    }
    dimacsInput.result()
  }

  def apply( hard: DIMACS.CNF, soft: Seq[( DIMACS.Clause, Int )] ): String = {
    val threshold = soft.map( _._2 ).sum + 1
    writeWDIMACS( hard.map( _ -> threshold ) ++ soft, threshold )
  }
}

object readWDIMACS {
  def apply( dimacsOutput: String ): Option[DIMACS.Model] = {
    val lines = dimacsOutput.split( "\n" )
    if ( lines exists { _ startsWith "o " } ) {
      Some( lines
        filter { _ startsWith "v " }
        map { _ substring 2 trim }
        flatMap { _ split " " }
        map { _ replace ( "x", "" ) } // toysat :-(
        map { _ toInt } )
    } else {
      None
    }
  }
}
