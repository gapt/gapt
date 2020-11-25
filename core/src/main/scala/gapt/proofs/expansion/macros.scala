package gapt.proofs.expansion
import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.Formula
import gapt.expr.formula.hol.{ HOLPosition, inductionPrinciple }
import gapt.expr.ty.FunctionType
import gapt.expr.ty.TBase
import gapt.expr.ty.To
import gapt.expr.util.syntacticMatching
import gapt.logic.Polarity
import gapt.proofs.context.Context
import gapt.proofs.context.facet.StructurallyInductiveTypes

object ETCut {
  case class Cut( left: ExpansionTree, right: ExpansionTree ) {
    def cutFormula: Formula = left.shallow
    def deep: Formula = toImp.deep
    def toImp: ExpansionTree = ETImp( left, right )
  }
  object Cut {
    def apply( cutFormula: Formula, left: ETt, right: ETt ): Cut =
      ExpansionTree( cutFormula, Polarity.InSuccedent, left ) ->
        ExpansionTree( cutFormula, Polarity.InAntecedent, right )
    implicit def fromPair( pair: ( ExpansionTree, ExpansionTree ) ): Cut =
      Cut( pair._1, pair._2 )
    implicit val closedUnderSub: ClosedUnderSub[Cut] =
      { case ( sub, Cut( left, right ) ) => Cut( sub( left ), sub( right ) ) }
  }

  // We are not using the parser here for performance reasons.
  // Using the parser incurs a ~500ms startup overhead.
  val cutAxiom: Formula = { val X = Var( "X", To ); All( X, X --> X ) }

  def apply( cuts: Iterable[Cut] ): ExpansionTree =
    ETWeakQuantifier.withMerge( cutAxiom, for ( cut <- cuts ) yield cut.cutFormula -> cut.toImp )
  def apply( child1: ExpansionTree, child2: ExpansionTree ): ExpansionTree =
    apply( Some( Cut( child1, child2 ) ) )
  def apply( cuts: Iterable[( ExpansionTree, ExpansionTree )] )( implicit dummyImplicit: DummyImplicit ): ExpansionTree =
    apply( for ( ( left, right ) <- cuts ) yield Cut( left, right ) )
  def apply( cutFormula: Formula, left: ETt, right: ETt ): ExpansionTree =
    apply( Some( Cut( cutFormula, left, right ) ) )

  def isCutExpansion( tree: ExpansionTree ): Boolean =
    tree.polarity.inAnt && tree.shallow == cutAxiom

  def unapply( et: ExpansionTree ): Option[Set[Cut]] =
    if ( isCutExpansion( et ) )
      Some {
        for {
          cut <- et( HOLPosition( 1 ) )
          cut1 <- cut( HOLPosition( 1 ) )
          cut2 <- cut( HOLPosition( 2 ) )
        } yield Cut( cut1, cut2 )
      }
    else None
}

object ETInduction {
  case class Case( constr: Const, evs: Seq[Var], auxiliary: ExpansionSequent )
  case class Induction( constructorsSteps: Seq[Case], hyps: ExpansionTree, suc: ExpansionTree )

  def indAxioms( implicit ctx: Context ): Map[Formula, Vector[Const]] =
    ctx.get[StructurallyInductiveTypes].constructors.map {
      case ( s, cs ) => ( inductionPrinciple( TBase( s, cs.head.params ), cs ), cs )
    }

  def isInductionAxiomExpansion( tree: ExpansionTree )( implicit ctx: Context ): Boolean =
    indAxioms.exists { case ( p, _ ) => syntacticMatching( p, tree.shallow ).isDefined }

  def unapply( et: ExpansionTree )( implicit ctx: Context ): Option[Set[Induction]] = {

    def getETs( et: ExpansionTree, sz: Int ): Seq[ExpansionTree] = {
      et match {
        case ETImp( ch1, ch2 ) if sz > 0 => ch1 +: getETs( ch2, sz - 1 )
        case ret if sz == 0              => Seq( ret )
      }
    }
    def getEvs( et: ExpansionTree, sz: Int ): ( ExpansionTree, Seq[Var] ) = {
      et match {
        case ETStrongQuantifier( _, ev, ch ) if sz > 0 =>
          val ( ret, evs ) = getEvs( ch, sz - 1 )
          ( ret, ev +: evs )
        case ret if sz == 0 => ( ret, Seq.empty )
      }
    }
    def toCase( et: ExpansionTree, constrs: Seq[Const] ): Seq[Case] = {
      val eisp = et.immediateSubProofs
      constrs.zip( ETAnd.Flat( et ) ).map {
        case ( constr, indCase ) =>
          val FunctionType( indTy, argTypes ) = constr.ty
          val ( ch, evs ) = getEvs( indCase, argTypes.length )
          val ets = getETs( ch, argTypes.count( _ == indTy ) )
          val ( hyps, suc ) = ets.splitAt( ets.length - 1 )
          Case( constr, evs, ExpansionSequent( hyps, suc ) )
      }
    }

    ( for {
      ( p0, constrs0 ) <- indAxioms
      subst <- syntacticMatching( p0, et.shallow )
      constrs = subst( constrs0 )
    } yield for {
      sequent <- et( HOLPosition( 1 ) )
      hyps <- sequent( HOLPosition( 1 ) )
      suc <- sequent( HOLPosition( 2 ) )
    } yield Induction( toCase( hyps, constrs ), hyps, suc ) ).headOption
  }
}
