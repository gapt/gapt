package gapt.provers.escargot

import gapt.expr._
import gapt.models.PropositionalModel
import gapt.proofs.lk.LKProof
import gapt.proofs._
import gapt.proofs.resolution._
import gapt.provers.escargot.impl.EscargotState
import gapt.provers.escargot.impl.EscargotLogger._
import gapt.provers.groundFreeVariables

import scala.annotation.tailrec

class EscargotChaud( allowedAtoms: Seq[Atom] ) {
  implicit val ctx: MutableContext = MutableContext.guess( allowedAtoms )

  val state = new EscargotState( ctx )
  import state._

  def removeAssertions( p: ResolutionProof ): ResolutionProof =
    new ResolutionProofVisitor {
      override def visitAvatarComponent( p: AvatarComponent ): ResolutionProof =
        Input( p.conclusion )
    }.apply( p )

  val ( Sequent( groundAtoms, _ ), renaming ) = groundFreeVariables( allowedAtoms :- Seq() )
  val atomMap = allowedAtoms.zip( groundAtoms ).toMap

  Escargot.setupDefaults( state, splitting = false, equality = true, propositional = true )
  nameGen = rename.awayFrom( containedNames( groundAtoms ) )
  termOrdering = Escargot.lpoHeuristic( groundAtoms.map( Sequent() :+ _ ), ctx.constants )

  val assertions = Map() ++ ( for ( atom <- groundAtoms; p <- Polarity.values )
    yield ( atom, p ) -> PropAtom( nameGen.fresh( "a" ) ) )
  case class AvDef( atom: Formula, polarity: Polarity, ass: Atom ) extends AvatarDefinition {
    def clause = Sequent( Seq( atom -> polarity ) )
    def assertion = Sequent() :+ ass
    def inducedDefinitions = Map()
  }
  for ( ( ( atom, p ), ass ) <- assertions )
    newlyDerived += InputCls( AvatarComponent( AvDef( atom, p, ass ) ) )

  avatarModel = PropositionalModel( assertions.values.map( _ -> false ) )

  def getResolutionProof( atomicSequent: HOLClause ): Option[ResolutionProof] = {
    val groundAtomicSequent = atomicSequent.map( atomMap )
    val model = PropositionalModel(
      for ( ( ( atom, p ), ass ) <- assertions )
        yield ass -> groundAtomicSequent.contains( atom, !p ) )
    switchToNewModel( model )
    emptyClauses.values.find( isActive ).map( _.proof ).
      orElse( singleModelLoop() ).
      map( removeAssertions )
  }

  def getAtomicLKProof( atomicSequent: HOLClause ): Option[LKProof] =
    getResolutionProof( atomicSequent ).
      map( UnitResolutionToLKProof( _ ) ).
      map( TermReplacement.undoGrounding( _, renaming ) )

  @tailrec final def singleModelLoop(): Option[ResolutionProof] = {
    preprocessing()
    clauseProcessing()

    usable.find( _.clause.isEmpty ) match {
      case Some( c ) =>
        return Some( c.proof )
      case None =>
    }

    if ( usable.isEmpty )
      return None

    val given = choose()
    usable -= given

    val discarded = inferenceComputation( given )

    info( s"[wo=${workedOff.size},us=${usable.size}] ${if ( discarded ) "discarded" else "kept"}: $given".replace( '\n', ' ' ) )

    singleModelLoop()
  }

}
