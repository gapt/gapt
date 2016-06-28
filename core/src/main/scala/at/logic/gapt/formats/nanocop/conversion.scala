package at.logic.gapt.formats.nanocop

import at.logic.gapt.expr.{ Ex, FOLAtom, FOLTerm, FOLVar, Substitution }
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.expansion.{ ETAnd, ETAtom, ETBottom, ETNeg, ETOr, ETTop, ETWeakQuantifierBlock, ExpansionTree, eliminateMerges }

import scala.collection.mutable

object nanocopToExpansion {
  def getInstances( deep: Seq[NanocopProof] ): Map[Int, Seq[Seq[FOLTerm]]] = {
    val res = mutable.Map[Int, Seq[Seq[FOLTerm]]]().withDefaultValue( Seq() )
    def walk( n: NanocopProof ): Unit = n match {
      case NanocopMatrix( i1, i2, children ) => children foreach walk
      case NanocopClause( i1, i2, terms, children ) =>
        res( i1 ) :+= terms
        children foreach walk
      case NanocopAtom( atom, pol ) =>
    }
    deep foreach walk
    res.toMap
  }

  val trueAtom = FOLAtom( "true___" )
  val falseAtom = FOLAtom( "false___" )

  def apply( shallow: Seq[NanocopProof], deep: Seq[NanocopProof] ): ExpansionTree = {
    val insts = getInstances( deep )

    def conv( sh: NanocopProof ): ExpansionTree = sh match {
      case NanocopMatrix( i1, i2, children ) =>
        ETOr( children.sortBy( _.index ).map( conv ), polarity = true )
      case NanocopClause( _, _, _, Seq( NanocopAtom( `trueAtom`, true ), NanocopAtom( `trueAtom`, false ) ) )   => ETTop( true )
      case NanocopClause( _, _, _, Seq( NanocopAtom( `falseAtom`, true ), NanocopAtom( `falseAtom`, false ) ) ) => ETTop( true )
      case NanocopClause( i1, i2, terms, children ) =>
        val etChild = ETAnd( children.sortBy( _.index ).map( conv ), polarity = true )
        val vars = terms.map( _.asInstanceOf[FOLVar] )
        ETWeakQuantifierBlock(
          Ex.Block( vars.reverse, etChild.shallow ), vars.size, true,
          for ( is <- insts.getOrElse( i1, Seq() ) ) yield is.reverse -> Substitution( vars zip is )( etChild )
        )
      case NanocopAtom( `trueAtom`, false ) | NanocopAtom( `falseAtom`, true ) => ETBottom( true )
      case NanocopAtom( `trueAtom`, true ) | NanocopAtom( `falseAtom`, false ) => ETTop( true )
      case NanocopAtom( atom, true ) => ETAtom( atom, true )
      case NanocopAtom( atom, false ) => ETNeg( ETAtom( atom, false ) )
    }

    eliminateMerges.unsafe( Sequent() :+ conv( NanocopMatrix( 0, 0, shallow ) ) ).succedent.head
  }
}