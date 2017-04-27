package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr.Polarity.{ Negative, Positive }
import at.logic.gapt.expr._
import at.logic.gapt.formats.babel.{ BabelExporter, BabelSignature }
import at.logic.gapt.utils.Doc
import Doc._

class ExpansionTreePrettyPrinter( sig: BabelSignature ) extends BabelExporter( unicode = true, sig = sig ) {

  def export( et: ExpansionTree ): String = {
    val knownTypesFromSig = knownConstantTypesFromSig( constants( et.deep ) union constants( et.shallow ) )
    group( show( et, knownTypesFromSig.toMap, prio.max )._1 ).render( lineWidth )
  }

  def addPol( doc: Doc, pol: Polarity ) =
    pol match {
      case Positive => doc <> "+"
      case Negative => doc <> "-"
    }

  def show( et: ExpansionTree, t0: Map[String, VarOrConst], p: Int ): ( Doc, Map[String, VarOrConst] ) = et match {
    case ETTop( pol )    => ( addPol( "⊤", pol ), t0 )
    case ETBottom( pol ) => ( addPol( "⊥", pol ), t0 )
    case ETWeakening( f, pol ) =>
      val ( f_, t1 ) = show( f, true, Set(), t0, prio.max )
      ( addPol( "wk", pol ) <> "{" <> f_ <> "}", t1 )
    case ETAtom( a, pol ) =>
      val ( a_, t1 ) = show( a, true, Set(), t0, prio.app + 1 )
      ( addPol( a_, pol ), t1 )
    case ETMerge( a, b ) =>
      val ( a_, t1 ) = show( a, t0, prio.bicond )
      val ( b_, t2 ) = show( b, t1, prio.bicond )
      parenIf( p, prio.bicond, a_ <+> "⊔" </> b_ ) -> t2
    case ETNeg( a ) =>
      val ( a_, t1 ) = show( a, t0, prio.quantOrNeg )
      parenIf( p, prio.quantOrNeg, "¬" <> a_ ) -> t1
    case ETAnd( a, b ) =>
      val ( a_, t1 ) = show( a, t0, prio.conj )
      val ( b_, t2 ) = show( b, t1, prio.conj )
      parenIf( p, prio.conj, a_ <+> "∧" </> b_ ) -> t2
    case ETOr( a, b ) =>
      val ( a_, t1 ) = show( a, t0, prio.disj )
      val ( b_, t2 ) = show( b, t1, prio.disj )
      parenIf( p, prio.disj, a_ <+> "∨" </> b_ ) -> t2
    case ETImp( a, b ) =>
      val ( a_, t1 ) = show( a, t0, prio.impl )
      val ( b_, t2 ) = show( b, t1, prio.impl )
      parenIf( p, prio.impl, a_ <+> "⊃" </> b_ ) -> t2
    case ETStrongQuantifier( sh, ev, child ) =>
      val ( sh_, t1 ) = show( sh, true, Set(), t0, prio.conj )
      val ( ev_, t2 ) = show( ev, true, Set(), t1, prio.max )
      val ( child_, t3 ) = show( child, t2, prio.conj )
      parenIf( p, prio.conj, sh_ <+> "+ev^{" <> ev_ <> "}" </> child_ ) -> t3
    case ETSkolemQuantifier( sh, skTerm, _, child ) =>
      val ( sh_, t1 ) = show( sh, true, Set(), t0, prio.conj )
      val ( skTerm_, t2 ) = show( skTerm, true, Set(), t1, prio.max )
      val ( child_, t3 ) = show( child, t2, prio.conj )
      parenIf( p, prio.conj, sh_ <+> "+sk^{" <> skTerm_ <> "}" </> child_ ) -> t3
    case ETWeakQuantifier( sh, insts ) =>
      val ( sh_, t1 ) = show( sh, true, Set(), t0, prio.conj )
      var t2 = t1
      val insts_ = insts.toList map {
        case ( term, child ) =>
          val ( term_, t3 ) = show( term, true, Set(), t2, prio.max )
          val ( child_, t4 ) = show( child, t3, prio.conj )
          t2 = t4
          ( term_.render( Integer.MAX_VALUE ), group( nest( "+^{" <> term_ <> "}" </> child_ ) ) )
      }
      parenIf( p, prio.conj, sep( sh_ +: insts_.sortBy( _._1 ).map( _._2 ), line ) ) -> t2
    case ETDefinition( shallow, child ) =>
      val ( sh_, t1 ) = show( shallow, true, Set(), t0, prio.conj )
      val ( child_, t2 ) = show( child, t1, prio.conj )
      parenIf( p, prio.conj, sh_ <+> "+def" </> child_ ) -> t2
  }

}