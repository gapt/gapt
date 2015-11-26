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
    new MapBasedInterpretation( model flatMap {
      case l if l > 0 => decodeAtomOption( l ) map { _ -> true }
      case l if l < 0 => decodeAtomOption( -l ) map { _ -> false }
    } toMap )

  override def toString = s"DIMACSEncoding(${atomMap.map( x => s"${x._1} -> ${x._2}" ).mkString( ", " )})"
}

object readDIMACS {
  private val whitespace = """\s""".r

  def apply( dimacsOutput: String ): DIMACS.Model =
    whitespace split dimacsOutput.trim diff Seq( "SAT", "0", "" ) map { _.toInt }
}

object writeDIMACS {
  def apply( cnf: DIMACS.CNF ): String = {
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
