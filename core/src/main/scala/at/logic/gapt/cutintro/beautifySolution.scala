package at.logic.gapt.cutintro

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ simplify, instantiate, CNFp, CNFn }
import at.logic.gapt.proofs.{ FOLClause, SequentIndex, Suc, Ant }

import scala.collection.mutable

object beautifySolution {

  def apply( ehs: ExtendedHerbrandSequent ): ExtendedHerbrandSequent = {
    val esCNFs = ehs.endSequent.zipWithIndex map {
      case ( All.Block( vs, f ), i: Ant ) => vs -> CNFp.toClauseList( f ).toSet
      case ( Ex.Block( vs, f ), i: Suc )  => vs -> CNFn.toClauseList( f ).toSet
    }
    val unitAxioms = for ( ( vs, cnfs ) <- esCNFs ) yield vs -> cnfs.filter { _.size == 1 }

    val addUs = mutable.Buffer[( SequentIndex, List[FOLTerm] )]()

    val qfCFs = for ( ( cf, ev ) <- ehs.cutFormulas zip ehs.sehs.eigenVariables ) yield instantiate( cf, ev )
    val newCFs = qfCFs.zipWithIndex map {
      case ( cf, k ) =>
        var cnf = CNFp.toClauseList( cf )

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

        simplify( And( cnf map { _.toImplication } ) )
    }

    val newUs = for ( ( ( u, uInst ), j ) <- ehs.sehs.us.zipWithIndex ) yield u -> ( uInst ++ addUs.filter { _._1 == j }.map { _._2 } )

    val ( nontrivialSS, nontrivialCFs ) = ( ehs.sehs.ss zip newCFs ).filter { _._2 != Top() }.unzip

    val newSEHS = SchematicExtendedHerbrandSequent( newUs, nontrivialSS )
    ExtendedHerbrandSequent( newSEHS, ( newSEHS.eigenVariables, nontrivialCFs ).zipped map { All.Block( _, _ ) } )
  }

}
