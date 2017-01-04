package at.logic.gapt.cutintro

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ simplify, instantiate, CNFp, CNFn }
import at.logic.gapt.proofs.{ FOLClause, SequentIndex, Suc, Ant }

import scala.collection.mutable

object beautifySolution {

  def apply( ehs: SolutionStructure ): SolutionStructure = {
    val esCNFs = ehs.endSequent.zipWithIndex map {
      case ( All.Block( vs, f ), i: Ant ) => vs -> CNFp( f )
      case ( Ex.Block( vs, f ), i: Suc )  => vs -> CNFn( f )
    }
    val unitAxioms = for ( ( vs, cnfs ) <- esCNFs ) yield vs -> cnfs.filter { _.size == 1 }

    val addUs = mutable.Buffer[( SequentIndex, List[FOLTerm] )]()

    val newCFs = ehs.formulas.zipWithIndex map {
      case ( cf, k ) =>
        var cnf = CNFp( cf )

        // subsumption
        cnf = cnf filter { cls =>
          val subsumingFormulas = for {
            ( ( vs, cnfs ), j ) <- esCNFs.zipWithIndex.elements
            esCNF <- cnfs
            subst <- clauseSubsumption( esCNF, cls )
          } yield ( j, subst.asFOLSubstitution( vs ).toList )
          subsumingFormulas.headOption match {
            case Some( ( j, inst ) ) =>
              for ( s <- ehs.sehs.ss( k )._2 )
                addUs += j -> FOLSubstitution( ehs.sehs.ss( k )._1 zip s )( inst ).toList
              false
            case None => true
          }
        }

        // unit resolution
        cnf = cnf map {
          _.zipWithIndex filter {
            case ( atom, i ) =>
              val possibleAxioms = for {
                ( ( vs, axs ), j ) <- unitAxioms.zipWithIndex.elements
                ax <- axs
                if !ax.indices.head.sameSideAs( i )
                subst <- syntacticMatching( ax.elements.head, atom )
              } yield ( j, subst( vs ).toList )
              possibleAxioms.headOption match {
                case Some( u ) =>
                  addUs += u
                  false
                case None =>
                  true
              }
          } map { _._1 }
        }

        simplify( And( cnf map { _.toImplication } ) )
    }

    val newUs = for ( ( ( u, uInst ), j ) <- ehs.sehs.us.zipWithIndex ) yield u -> ( uInst ++ addUs.filter { _._1 == j }.map { _._2 } )

    val nonTrivialIndices = newCFs.indices.filterNot { i =>
      newCFs.drop( i ).contains( Top() ) ||
        newCFs( i ) == Bottom()
    }
    val nontrivialSS = nonTrivialIndices.map( ehs.sehs.ss )
    val nontrivialCFs = nonTrivialIndices.map( newCFs )

    val grounding = FOLSubstitution( newCFs.indices.diff( nonTrivialIndices ).
      flatMap( ehs.sehs.eigenVariables ).
      map( v => v -> FOLConst( v.name ) ) )

    val newSEHS = SchematicExtendedHerbrandSequent( grounding( newUs ), nontrivialSS.map( ss => ss._1 -> grounding( ss._2 ) ) )
    SolutionStructure( newSEHS, grounding( nontrivialCFs ) )
  }

}
