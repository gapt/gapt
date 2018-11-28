package gapt.proofs.expansion

import gapt.expr.Polarity.{ Negative, Positive }
import gapt.expr._
import gapt.expr.hol.instantiate
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext

import scala.collection.mutable

object atomicExpansionET {
  def mapDefinedAtom( et: ExpansionTree )( f: PartialFunction[( Formula, Formula, Polarity ), ExpansionTree] ): ExpansionTree =
    et match {
      case ETDefinition( sh, ETAtom( at, pol ) ) =>
        f.lift( ( sh, at, pol ) ).getOrElse( et )
      case ETDefinition( sh, ETWeakening( _, pol ) ) => ETWeakening( sh, pol )
      case ETDefinition( sh, ch ) =>
        ETDefinition( sh, mapDefinedAtom( ch )( f ) )
      case ETAtom( _, _ ) | ETWeakening( _, _ ) | ETTop( _ ) | ETBottom( _ ) => et
      case ETMerge( a, b ) => ETMerge( mapDefinedAtom( a )( f ), mapDefinedAtom( b )( f ) )
      case ETNeg( e ) => ETNeg( mapDefinedAtom( e )( f ) )
      case ETAnd( a, b ) => ETAnd( mapDefinedAtom( a )( f ), mapDefinedAtom( b )( f ) )
      case ETOr( a, b ) => ETOr( mapDefinedAtom( a )( f ), mapDefinedAtom( b )( f ) )
      case ETImp( a, b ) => ETImp( mapDefinedAtom( a )( f ), mapDefinedAtom( b )( f ) )
      case ETWeakQuantifier( sh, insts ) =>
        ETWeakQuantifier( sh, Map() ++ insts.mapValues( mapDefinedAtom( _ )( f ) ) )
      case ETStrongQuantifier( sh, ev, ch ) =>
        ETStrongQuantifier( sh, ev, mapDefinedAtom( ch )( f ) )
      case ETSkolemQuantifier( sh, skT, ch ) =>
        ETSkolemQuantifier( sh, skT, mapDefinedAtom( ch )( f ) )
    }

  def mapDefinedAtom( ep: ExpansionProof )( f: PartialFunction[( Formula, Formula, Polarity ), ExpansionTree] ): ExpansionProof =
    ExpansionProof( ep.expansionSequent.map( mapDefinedAtom( _ )( f ) ) )

  def getDefinedAtoms( ep: ExpansionProof ): Set[Const] =
    ep.subProofs.collect { case ETDefinition( _, ETAtom( Apps( c: Const, _ ), _ ) ) => c }

  def apply( ep: ExpansionProof )( implicit ctx: Context ): ExpansionProof =
    apply( ep, getDefinedAtoms( ep ) )

  def apply( ep: ExpansionProof, definedAtoms: Set[Const] )( implicit ctx: Context ): ExpansionProof =
    apply( ep, definedAtoms, purelyPropositional = false )

  def apply( ep: ExpansionProof, definedAtoms: Set[Const], purelyPropositional: Boolean )( implicit ctx: Context ): ExpansionProof =
    loop( ep, definedAtoms, purelyPropositional )( ctx.newMutable )

  private def loop( ep: ExpansionProof, definedAtoms: Set[Const], purelyPropositional: Boolean )( implicit ctx: MutableContext ): ExpansionProof =
    if ( definedAtoms.isEmpty ) ep else {
      val d = definedAtoms.head
      val Some( Abs.Block( xs, fml: Formula ) ) = ctx.definition( d )
      fml match {
        case _ if !ep.subProofs.exists { case ETAtom( Apps( `d`, _ ), _ ) => true case _ => false } =>
          loop( ep, definedAtoms - d, purelyPropositional )

        case Top() | Bottom() | Neg( _ ) | And( _, _ ) | Or( _, _ ) | Imp( _, _ ) | Atom( _, _ ) =>
          val newDefs = mutable.Set[Const]()

          def mkNew( f: Formula ): ( ExpansionTree, ExpansionTree ) =
            f match {
              case Top()    => ( ETTop( Negative ), ETTop( Positive ) )
              case Bottom() => ( ETBottom( Negative ), ETBottom( Positive ) )
              case a: Atom  => ( ETAtom( a, Negative ), ETAtom( a, Positive ) )
              case Neg( a ) =>
                val ( an, ap ) = mkNew( a )
                ( ETNeg( ap ), ETNeg( an ) )
              case And( a, b ) =>
                val ( an, ap ) = mkNew( a )
                val ( bn, bp ) = mkNew( b )
                ( ETAnd( an, bn ), ETAnd( ap, bp ) )
              case Or( a, b ) =>
                val ( an, ap ) = mkNew( a )
                val ( bn, bp ) = mkNew( b )
                ( ETOr( an, bn ), ETOr( ap, bp ) )
              case Imp( a, b ) =>
                val ( an, ap ) = mkNew( a )
                val ( bn, bp ) = mkNew( b )
                ( ETImp( ap, bn ), ETImp( an, bp ) )
              case All( _, _ ) | Ex( _, _ ) =>
                val ys = freeVariables( f ).toSeq
                val df = ctx.addDefinition( Abs( ys, f ), reuse = false )
                newDefs += df
                val dfYs = df( ys ).asInstanceOf[Atom]
                ETDefinition( f, ETAtom( dfYs, Negative ) ) ->
                  ETDefinition( f, ETAtom( dfYs, Positive ) )
            }

          val ( neg, pos ) = mkNew( fml )

          val ep_ = mapDefinedAtom( ep ) {
            case ( _, Apps( `d`, as ), Negative ) => Substitution( xs zip as )( neg )
            case ( _, Apps( `d`, as ), Positive ) => Substitution( xs zip as )( pos )
          }

          loop( ep_, definedAtoms - d ++ newDefs, purelyPropositional )

        case Quant( x_, _, isAll ) =>
          val x = rename( x_, xs )
          val f = instantiate( fml, x )
          val df = ctx.addDefinition( Abs( xs :+ x, f ), reuse = false )

          val strongPol = if ( isAll ) Positive else Negative
          val weakPol = !strongPol

          val newEigens = mutable.Buffer[( Var, Expr )]()
          val nameGen = rename.awayFrom( ep.eigenVariables )
          val ep1 = mapDefinedAtom( ep ) {
            case ( sh, at @ Apps( `d`, as ), `strongPol` ) =>
              val newEigen = nameGen.fresh( x )
              newEigens += ( ( newEigen, at ) )
              ETStrongQuantifier( sh, newEigen,
                ETDefinition(
                  instantiate( sh, newEigen ),
                  ETAtom( df( as :+ newEigen ).asInstanceOf[Atom], strongPol ) ) )
          }

          val ep2 = mapDefinedAtom( ep1 ) {
            case ( sh, at2 @ Apps( `d`, as ), `weakPol` ) =>
              ETWeakQuantifier.withMerge(
                sh,
                for {
                  ( ev, at ) <- newEigens
                  if !purelyPropositional || at == at2
                } yield ev -> ETDefinition(
                  instantiate( sh, ev ),
                  ETAtom( df( as :+ ev ).asInstanceOf[Atom], weakPol ) ) )
          }

          loop( ep2, definedAtoms - d + df, purelyPropositional )
      }
    }
}