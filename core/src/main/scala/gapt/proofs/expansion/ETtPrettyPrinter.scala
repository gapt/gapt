package gapt.proofs.expansion

import gapt.expr._
import gapt.formats.babel.{ BabelExporter, BabelSignature, Precedence }
import gapt.utils.Doc
import gapt.utils.Doc._

class ETtPrettyPrinter( sig: BabelSignature ) extends BabelExporter( unicode = true, sig = sig ) {
  def export( et: ETt ): Doc =
    group( show( et, Map[String, VarOrConst]() )._1.inPrec( 0 ) )

  def addPol( doc: Doc, pol: Polarity ): Doc =
    doc <> ( if ( pol.positive ) "+" else "-" )

  def show( et: ETt, t0: Map[String, VarOrConst] ): ( Parenable, Map[String, VarOrConst] ) = et match {
    case ETtNullary => ( Parenable( Precedence.max, "∘" ), t0 )
    case ETtWeakening =>
      ( Parenable( Precedence.max, "wk" ), t0 )
    case ETtAtom =>
      ( Parenable( Precedence.max, "□" ), t0 )
    case ETtMerge( a, b ) =>
      val ( a_, t1 ) = show( a, t0 )
      val ( b_, t2 ) = show( b, t1 )
      Parenable( Precedence.iff, a_.inPrec( Precedence.iff ) <+> "⊔" </> b_.inPrec( Precedence.iff + 1 ) ) -> t2
    case ETtUnary( a ) =>
      val ( a_, t1 ) = show( a, t0 )
      Parenable( Precedence.neg, "¬" <> a_.inPrec( Precedence.neg + 1 ) ) -> t1
    case ETtBinary( a, b ) =>
      val ( a_, t1 ) = show( a, t0 )
      val ( b_, t2 ) = show( b, t1 )
      Parenable( Precedence.conj, a_.inPrec( Precedence.conj ) <+> "×" </> b_.inPrec( Precedence.conj + 1 ) ) -> t2
    case ETtStrong( ev, child ) =>
      val t1 = t0
      val ( ev_, t2 ) = show( ev, true, Set(), t1 )
      val ( child_, t3 ) = show( child, t2 )
      Parenable( Precedence.quant, "⟨" <> ev_.inPrec( 0 ) <> "⟩ₑᵥ" </>
        child_.inPrec( Precedence.quant - 1 ) ) -> t3
    case ETtSkolem( skTerm, child ) =>
      val t1 = t0
      val ( skTerm_, t2 ) = show( skTerm, true, Set(), t1 )
      val ( child_, t3 ) = show( child, t2 )
      Parenable( Precedence.quant, "⟨" <> skTerm_.inPrec( 0 ) <> "⟩ₛₖ" </>
        child_.inPrec( Precedence.quant - 1 ) ) -> t3
    case ETtWeak( insts ) =>
      var t2 = t0
      val insts_ = insts.toList.map {
        case ( term, child ) =>
          val ( term_, t3 ) = show( term, true, Set(), t2 )
          val ( child_, t4 ) = show( child, t3 )
          t2 = t4
          (
            term_.inPrec( 0 ).render( Integer.MAX_VALUE ),
            group( "⟨" <> term_.inPrec( 0 ) <> "⟩" <> nest( line <> child_.inPrec( Precedence.quant - 1 ) ) ) )
      }.sortBy( _._1 ).map( _._2 )
      ( insts_ match {
        case Seq()        => Parenable( Precedence.max, "∅" )
        case Seq( inst_ ) => Parenable( Precedence.quant, inst_ )
        case _ =>
          Parenable( Precedence.iff, group( sep( insts_, line ) ) )
      } ) -> t2
    case ETtDef( shallow, child ) =>
      val ( sh_, t1 ) = show( shallow, true, Set(), t0 )
      val ( child_, t2 ) = show( child, t1 )
      Parenable( Precedence.conj, "⦃" <> sh_.inPrec( Precedence.quant ) <> "⦄ᵈᵉᶠ	" </> child_.inPrec( Precedence.quant - 1 ) ) -> t2
  }

}