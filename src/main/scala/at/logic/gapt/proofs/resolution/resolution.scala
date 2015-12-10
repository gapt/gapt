package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs._

/**
 * First-order resolution proof.
 *
 * Clauses are stored as sequents of HOLAtoms; the succedent consists of the
 * positive literals, the antecedent of the negative literals.
 *
 * Substitutions are not absorbed into resolution, factoring, and
 * paramodulation; they are explicitly represented using [[Instance]].
 */
trait ResolutionProof extends SequentProof[HOLAtom, ResolutionProof]

/**
 * Initial clause of a resolution proof.
 *
 * This also includes some initial clauses which arise during proof
 * transformations, e.g. [[ReflexivityClause]] or [[TautologyClause]].
 *
 * Clauses that come from the input CNF we're refuting are stored as
 * [[InputClause]].
 */
trait InitialClause extends ResolutionProof {
  override def mainIndices = conclusion.indices
  override def occConnectors = Seq()
  override def auxIndices = Seq()
  override def immediateSubProofs = Seq()
}

/**
 * Input clause from the CNF that we're refuting.
 *
 * <pre>
 *   ----------
 *   conclusion
 * </pre>
 */
case class InputClause( conclusion: HOLClause ) extends InitialClause
/**
 * Reflexivity.
 *
 * <pre>
 *   -----------
 *   term = term
 * </pre>
 */
case class ReflexivityClause( term: LambdaExpression ) extends InitialClause {
  override val conclusion = Clause() :+ Eq( term, term )
}
/**
 * Tautology.
 *
 * <pre>
 *   -------------
 *   -atom \/ atom
 * </pre>
 */
case class TautologyClause( atom: HOLAtom ) extends InitialClause {
  override val conclusion = atom +: Clause() :+ atom
}

/**
 * Instantiation.
 *
 * <pre>
 *        (subProof)
 *         premise
 *   ---------------------
 *   substitution(premise)
 * </pre>
 */
case class Instance( subProof: ResolutionProof, substitution: Substitution ) extends ResolutionProof {
  override val conclusion = subProof.conclusion.map { substitution( _ ).asInstanceOf[HOLAtom] }
  override def occConnectors = Seq( OccConnector( conclusion, subProof.conclusion,
    subProof.conclusion.indicesSequent map { Seq( _ ) } ) )

  override def mainIndices = conclusion.indices
  override def auxIndices = Seq( subProof.conclusion.indices )

  override def immediateSubProofs = Seq( subProof )
}

/**
 * Factoring.
 *
 * This rule merges two literals that have the same polarity, i.e. which
 * are on the same side of the sequent.
 *
 * <pre>
 *            (subProof)
 *   premise \/ literal1 \/ literal2
 *   -------------------------------
 *        premise \/ literal1
 * </pre>
 */
case class Factor( subProof: ResolutionProof, literal1: SequentIndex, literal2: SequentIndex ) extends ResolutionProof {
  require( literal1 sameSideAs literal2 )
  require( literal1 < literal2 )
  require( subProof.conclusion( literal1 ) == subProof.conclusion( literal2 ) )

  override val conclusion = subProof.conclusion delete literal2
  override def occConnectors = Seq( OccConnector( conclusion, subProof.conclusion,
    subProof.conclusion.indicesSequent.delete( literal2 ).map { Seq( _ ) }.updated( literal1, Seq( literal1, literal2 ) ) ) )

  override def mainIndices = Seq( literal1 )
  override def auxIndices = Seq( Seq( literal1, literal2 ) )

  override def immediateSubProofs = Seq( subProof )
}

object Factor {
  def apply( subProof: ResolutionProof, literals: Traversable[SequentIndex] ): ( ResolutionProof, OccConnector[HOLAtom] ) = {
    val lit0 :: lits = literals.toList.sorted
    lits.reverse.foldLeft( subProof -> OccConnector( subProof.conclusion ) ) {
      case ( ( subProof_, occConn ), lit ) =>
        val subProof__ = Factor( subProof_, lit0, lit )
        subProof__ -> ( subProof__.occConnectors.head * occConn )
    }
  }

  def apply( subProof: ResolutionProof, newConclusion: HOLClause ): ( ResolutionProof, OccConnector[HOLAtom] ) = {
    var ( p, occConn ) = ( subProof, OccConnector( subProof.conclusion ) )

    newConclusion.polarizedElements.toSet[( HOLAtom, Boolean )] foreach {
      case ( atom, pol ) =>
        val countInNewConcl = newConclusion.polarizedElements.count( _ == ( atom, pol ) )
        val countInOldConcl = subProof.conclusion.polarizedElements.count( _ == ( atom, pol ) )
        if ( countInOldConcl > countInNewConcl ) {
          val ( p_, occConn_ ) = Factor( p, p.conclusion.
            indicesWhere( _ == atom ).
            filter( _.isSuc == pol ).
            take( countInOldConcl - countInNewConcl + 1 ) )
          p = p_
          occConn = occConn_ * occConn
        }
    }

    ( p, occConn )
  }

  def apply( subProof: ResolutionProof ): ( ResolutionProof, OccConnector[HOLAtom] ) =
    Factor( subProof, subProof.conclusion.distinct )
}

object MguFactor {
  def apply( subProof: ResolutionProof, literal1: SequentIndex, literal2: SequentIndex ): Factor = {
    val Some( mgu ) = syntacticMGU( subProof.conclusion( literal1 ), subProof.conclusion( literal2 ) )
    Factor( Instance( subProof, mgu ), literal1, literal2 )
  }
}

/**
 * Resolution.
 *
 * The positive literal must be in the first sub-proof.
 *
 * <pre>
 *       (subProof1)               (subProof2)
 *   premise1 \/ literal     -literal \/ premise2
 *   --------------------------------------------
 *             premise1 \/ premise2
 * </pre>
 */
case class Resolution( subProof1: ResolutionProof, literal1: SequentIndex,
                       subProof2: ResolutionProof, literal2: SequentIndex ) extends ResolutionProof {
  require( subProof1.conclusion isDefinedAt literal1, s"$literal1 not a valid index in ${subProof1.conclusion}" )
  require( subProof2.conclusion isDefinedAt literal2, s"$literal2 not a valid index in ${subProof2.conclusion}" )
  require( subProof1.conclusion( literal1 ) == subProof2.conclusion( literal2 ) )
  require( literal1 isSuc )
  require( literal2 isAnt )

  override val conclusion = ( subProof1.conclusion delete literal1 ) ++ ( subProof2.conclusion delete literal2 )
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

object MguResolution {
  def apply( subProof1: ResolutionProof, literal1: Suc,
             subProof2: ResolutionProof, literal2: Ant ): Resolution = {
    val Some( ( mgu1, mgu2 ) ) = syntacticMGU.twoSubstitutions(
      subProof1.conclusion( literal1 ), subProof2.conclusion( literal2 )
    )
    Resolution(
      Instance( subProof1, mgu1 ), literal1,
      Instance( subProof2, mgu2 ), literal2
    )
  }
}

/**
 * Paramodulation.
 *
 * We allow rewriting any number of positions inside a single literal.
 *
 * <pre>
 *     (subProof1)            (subProof2)
 *   premise1 \/ t=s      premise2 \/ literal[t]
 *   -------------------------------------------
 *        premise1 \/ premise2 \/ literal[s]
 * </pre>
 */
case class Paramodulation( subProof1: ResolutionProof, equation: SequentIndex,
                           subProof2: ResolutionProof, literal: SequentIndex,
                           positions: Seq[LambdaPosition], leftToRight: Boolean ) extends ResolutionProof {
  require( equation isSuc )
  val ( t, s ) = ( subProof1.conclusion( equation ), leftToRight ) match {
    case ( Eq( a, b ), true )  => ( a, b )
    case ( Eq( a, b ), false ) => ( b, a )
  }

  positions foreach { position =>
    require( subProof2.conclusion( literal )( position ) == t )
  }

  val rewrittenAtom = positions.foldLeft( subProof2.conclusion( literal ) ) { _.replace( _, s ).asInstanceOf[HOLAtom] }

  override val conclusion = subProof1.conclusion.delete( equation ) ++
    subProof2.conclusion.updated( literal, rewrittenAtom )
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
                   newAtom: HOLAtom, leftToRight: Boolean ): Option[Paramodulation] = {
    val ( t, s ) = ( subProof1.conclusion( equation ), leftToRight ) match {
      case ( Eq( a, b ), true )  => a -> b
      case ( Eq( a, b ), false ) => b -> a
    }

    val oldAtom = subProof2.conclusion( literal )
    val positions = LambdaPosition.getPositions( oldAtom, _ == t ).filter { newAtom.get( _ ) == Some( s ) }
    val proof = Paramodulation( subProof1, equation, subProof2, literal, positions, leftToRight )
    if ( proof.mainFormulas.head == newAtom ) Some( proof ) else None
  }
  def apply( subProof1: ResolutionProof, equation: SequentIndex,
             subProof2: ResolutionProof, literal: SequentIndex,
             newAtom: HOLAtom ): Paramodulation =
    applyOption( subProof1, equation, subProof2, literal, newAtom, leftToRight = true ).
      orElse( applyOption( subProof1, equation, subProof2, literal, newAtom, leftToRight = false ) ).
      getOrElse {
        throw new IllegalArgumentException( s"Can't rewrite ${subProof2.conclusion( literal )} into $newAtom using ${subProof1.conclusion( equation )}" )
      }
}
