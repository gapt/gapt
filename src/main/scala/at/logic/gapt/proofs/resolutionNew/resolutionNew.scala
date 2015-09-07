package at.logic.gapt.proofs.resolutionNew

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.proofs.SequentProof
import at.logic.gapt.proofs.lk.base.{ Ant, Suc, Sequent, SequentIndex }
import at.logic.gapt.proofs.lkNew.OccConnector
import at.logic.gapt.proofs.resolution.{ FOLClause, HOLClause, Clause }

trait ResolutionProof extends SequentProof[FOLAtom, ResolutionProof]

trait InitialClause extends ResolutionProof {
  override def mainIndices = conclusion.indices
  override def occConnectors = Seq()
  override def auxIndices = Seq()
  override def immediateSubProofs = Seq()
}

case class InputClause( conclusion: FOLClause ) extends InitialClause
case class ReflexivityClause( term: FOLTerm ) extends InitialClause {
  override def conclusion = FOLClause() :+ Eq( term, term )
}
case class TautologyClause( atom: FOLAtom ) extends InitialClause {
  override def conclusion = atom +: FOLClause() :+ atom
}

case class Instance( subProof: ResolutionProof, substitution: FOLSubstitution ) extends ResolutionProof {
  override def conclusion = subProof.conclusion.map { substitution( _ ) }
  override def occConnectors = Seq( OccConnector( conclusion, subProof.conclusion,
    subProof.conclusion.indicesSequent map { Seq( _ ) } ) )

  override def mainIndices = conclusion.indices
  override def auxIndices = Seq( subProof.conclusion.indices )

  override def immediateSubProofs = Seq( subProof )
}

case class Factor( subProof: ResolutionProof, literal1: SequentIndex, literal2: SequentIndex ) extends ResolutionProof {
  require( literal1 sameSideAs literal2 )
  require( literal1 < literal2 )

  override def conclusion = subProof.conclusion delete literal2
  override def occConnectors = Seq( OccConnector( conclusion, subProof.conclusion,
    subProof.conclusion.indicesSequent.delete( literal2 ).map { Seq( _ ) }.updated( literal1, Seq( literal1, literal2 ) ) ) )

  override def mainIndices = Seq( literal1 )
  override def auxIndices = Seq( Seq( literal1, literal2 ) )

  override def immediateSubProofs = Seq( subProof )
}

object Factor {
  def apply( subProof: ResolutionProof, literals: Traversable[SequentIndex] ): ( ResolutionProof, OccConnector ) = {
    val lit0 :: lits = literals.toList.sorted
    lits.reverse.foldLeft( subProof -> OccConnector( subProof.conclusion ) ) {
      case ( ( subProof_, occConn ), lit ) =>
        val subProof__ = Factor( subProof_, lit0, lit )
        subProof__ -> ( subProof__.occConnectors.head * occConn )
    }
  }
}

case class Resolution( subProof1: ResolutionProof, literal1: SequentIndex,
                       subProof2: ResolutionProof, literal2: SequentIndex ) extends ResolutionProof {
  require( subProof1.conclusion isDefinedAt literal1, s"$literal1 not a valid index in ${subProof1.conclusion}" )
  require( subProof2.conclusion isDefinedAt literal2, s"$literal2 not a valid index in ${subProof2.conclusion}" )
  require( !( literal1 sameSideAs literal2 ) )

  override def conclusion = ( subProof1.conclusion delete literal1 ) ++ ( subProof2.conclusion delete literal2 )
  override def occConnectors = Seq(
    OccConnector( conclusion, subProof1.conclusion,
      ( subProof1.conclusion.indicesSequent delete literal1 map { Seq( _ ) } ) ++ ( subProof2.conclusion.indicesSequent delete literal2 map { _ => Seq() } ) ),
    OccConnector( conclusion, subProof2.conclusion,
      ( subProof1.conclusion.indicesSequent delete literal1 map { _ => Seq() } ) ++ ( subProof2.conclusion.indicesSequent delete literal2 map { Seq( _ ) } ) )
  )

  override def mainIndices = Seq()
  override def auxIndices = Seq( Seq( literal1 ), Seq( literal2 ) )

  override def immediateSubProofs = Seq( subProof1, subProof2 )
}

case class Paramodulation( subProof1: ResolutionProof, equation: SequentIndex,
                           subProof2: ResolutionProof, literal: SequentIndex,
                           positions: Seq[LambdaPosition], leftToRight: Boolean ) extends ResolutionProof {
  require( equation isSuc )
  val ( t, s ) = ( subProof1.conclusion( equation ), leftToRight ) match {
    case ( Eq( a: FOLTerm, b: FOLTerm ), true )  => ( a, b )
    case ( Eq( a: FOLTerm, b: FOLTerm ), false ) => ( b, a )
  }

  positions foreach { position =>
    require( subProof2.conclusion( literal )( position ) == t )
  }

  override def conclusion = subProof1.conclusion.delete( equation ) ++
    subProof2.conclusion.updated( literal, positions.foldLeft( subProof2.conclusion( literal ) ) { _.replace( _, s ).asInstanceOf[FOLAtom] } )
  override def occConnectors = Seq(
    OccConnector( conclusion, subProof1.conclusion,
      subProof1.conclusion.indicesSequent.delete( equation ).map { Seq( _ ) } ++ subProof2.conclusion.indicesSequent.map { _ => Seq() } ),
    OccConnector( conclusion, subProof2.conclusion,
      subProof1.conclusion.indicesSequent.delete( equation ).map { _ => Seq() } ++ subProof2.conclusion.indicesSequent.map { Seq( _ ) } )
  )

  override def mainIndices = occConnectors( 1 ).children( literal )
  override def auxIndices = Seq( Seq( equation ), Seq( literal ) )

  override def immediateSubProofs = Seq( subProof1, subProof2 )
}

object Paramodulation {
  def applyOption( subProof1: ResolutionProof, equation: SequentIndex,
                   subProof2: ResolutionProof, literal: SequentIndex,
                   newAtom: FOLAtom, leftToRight: Boolean ): Option[Paramodulation] = {
    val ( t, s ) = ( subProof1.conclusion( equation ), leftToRight ) match {
      case ( Eq( a, b ), true )  => a -> b
      case ( Eq( a, b ), false ) => b -> a
    }

    val oldAtom = subProof2.conclusion( literal )
    val positions = LambdaPosition.getPositions( oldAtom, _ == t ).filter { newAtom( _ ) == s }
    val newAtom_ = positions.foldLeft( oldAtom ) { _.replace( _, s ).asInstanceOf[FOLAtom] }
    if ( newAtom == newAtom_ )
      Some( Paramodulation( subProof1, equation, subProof2, literal, positions, leftToRight ) )
    else
      None
  }
  def apply( subProof1: ResolutionProof, equation: SequentIndex,
             subProof2: ResolutionProof, literal: SequentIndex,
             newAtom: FOLAtom ): Paramodulation =
    applyOption( subProof1, equation, subProof2, literal, newAtom, leftToRight = true ).
      orElse( applyOption( subProof1, equation, subProof2, literal, newAtom, leftToRight = false ) ).
      getOrElse {
        throw new IllegalArgumentException( s"Can't rewrite ${subProof2.conclusion( literal )} into $newAtom using ${subProof1.conclusion( equation )}" )
      }
}
