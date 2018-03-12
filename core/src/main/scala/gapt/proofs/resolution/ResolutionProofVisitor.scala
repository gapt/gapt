package gapt.proofs.resolution

import gapt.expr.{ Formula, Polarity }
import gapt.proofs.SequentIndex

import scala.collection.mutable

class ResolutionProofVisitor {

  val memo = mutable.Map[ResolutionProof, ResolutionProof]()

  def apply( proof: ResolutionProof ): ResolutionProof = {
    val result = proof match {
      case p: Input               => visitInput( p )
      case p: Taut                => visitTaut( p )
      case p: Refl                => visitRefl( p )

      case p: Subst               => visitSubst( p )

      case p: Factor              => visitFactor( p )
      case p: Resolution          => visitResolution( p )
      case p: Paramod             => visitParamod( p )
      case p: Flip                => visitFlip( p )

      case p: Defn                => visitDefn( p )
      case p: DefIntro            => visitDefIntro( p )

      case p: AvatarComponent     => visitAvatarComponent( p )
      case p: AvatarContradiction => visitAvatarContradiction( p )
      case p: AvatarSplit         => visitAvatarSplit( p )

      case p: PropositionalResolutionRule =>
        visitPropositional( p )
    }

    Factor( result )
  }

  def recurse( proof: ResolutionProof ): ResolutionProof = memo.getOrElseUpdate( proof, apply( proof ) )

  def copyUnary( old: ResolutionProof, newSub: ResolutionProof, aux: Formula, pol: Polarity ): ResolutionProof =
    newSub.conclusion.indexOfOption( aux, pol ) match {
      case Some( idx ) => copyUnary( old, newSub, idx )
      case None        => newSub
    }
  def copyUnary( old: ResolutionProof, newSub: ResolutionProof, aux: SequentIndex ): ResolutionProof = old match {
    case _: Flip => Flip( newSub, aux )
    case DefIntro( _, _, defAtom, definition ) =>
      DefIntro( newSub, aux, defAtom, definition )

    case _: TopL                     => TopL( newSub, aux )
    case _: BottomR                  => BottomR( newSub, aux )
    case _: NegL                     => NegL( newSub, aux )
    case _: NegR                     => NegR( newSub, aux )
    case _: AndL                     => AndL( newSub, aux )
    case _: AndR1                    => AndR1( newSub, aux )
    case _: AndR2                    => AndR2( newSub, aux )
    case _: OrL1                     => OrL1( newSub, aux )
    case _: OrL2                     => OrL2( newSub, aux )
    case _: OrR                      => OrR( newSub, aux )
    case _: ImpL1                    => ImpL1( newSub, aux )
    case _: ImpL2                    => ImpL2( newSub, aux )
    case _: ImpR                     => ImpR( newSub, aux )

    case AllR( _, _, ev )            => AllR( newSub, aux, ev )
    case ExL( _, _, ev )             => ExL( newSub, aux, ev )

    case AllL( _, _, skTerm, skDef ) => AllL( newSub, aux, skTerm, skDef )
    case ExR( _, _, skTerm, skDef )  => ExR( newSub, aux, skTerm, skDef )
  }

  def visitInput( p: Input ): ResolutionProof = p
  def visitTaut( p: Taut ): ResolutionProof = p
  def visitRefl( p: Refl ): ResolutionProof = p

  def visitSubst( p: Subst ): ResolutionProof = p.copy( subProof = recurse( p.subProof ) )

  def visitFactor( p: Factor ): ResolutionProof = recurse( p.subProof )
  def visitResolution( p: Resolution ): ResolutionProof = {
    val q1 = recurse( p.subProof1 )
    val q2 = recurse( p.subProof2 )
    q1.conclusion.indexOfOption( p.resolvedLiteral, Polarity.InSuccedent ).fold( q1 ) { i1 =>
      q2.conclusion.indexOfOption( p.resolvedLiteral, Polarity.InAntecedent ).fold( q2 ) { i2 =>
        Resolution( q1, i1, q2, i2 )
      }
    }
  }
  def visitParamod( p: Paramod ): ResolutionProof = {
    val q1 = recurse( p.subProof1 )
    val q2 = recurse( p.subProof2 )
    q1.conclusion.indexOfOption( p.subProof1.conclusion( p.eqIdx ), Polarity.InSuccedent ).fold( q1 ) { i1 =>
      q2.conclusion.indexOfOption( p.subProof2.conclusion( p.auxIdx ), p.auxIdx.polarity ).fold( q2 ) { i2 =>
        Paramod( q1, i1, p.leftToRight, q2, i2, p.context )
      }
    }
  }
  def visitFlip( p: Flip ): ResolutionProof =
    copyUnary( p, recurse( p.subProof ), p.subProof.conclusion( p.idx ), p.idx.polarity )

  def visitDefn( p: Defn ): ResolutionProof = p
  def visitDefIntro( p: DefIntro ): ResolutionProof =
    copyUnary( p, recurse( p.subProof ), p.subProof.conclusion( p.idx ), p.idx.polarity )

  def visitAvatarContradiction( p: AvatarContradiction ): ResolutionProof =
    AvatarContradiction( recurse( p.subProof ) )
  def visitAvatarComponent( p: AvatarComponent ): ResolutionProof = p
  def visitAvatarSplit( p: AvatarSplit ): ResolutionProof = AvatarSplit( recurse( p.subProof ), p.component )

  def visitPropositional( p: PropositionalResolutionRule ): ResolutionProof =
    copyUnary( p, recurse( p.subProof ), p.subProof.conclusion( p.idx ), p.idx.polarity )

}
