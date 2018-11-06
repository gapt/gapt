package gapt.proofs.expansion

import gapt.expr._
import gapt.formats.babel.{ BabelExporter, BabelSignature, Precedence }
import gapt.utils.Doc
import Doc._

class ExpansionTreePrettyPrinter( sig: BabelSignature ) extends BabelExporter( unicode = true, sig = sig ) {
  def export( et: ExpansionTree ): Doc =
    group( show( et, Map[String, VarOrConst]() )._1.inPrec( 0 ) )

  def addPol( doc: Doc, pol: Polarity ) =
    doc <> ( if ( pol.positive ) "+" else "-" )

  def show( et: ExpansionTree, t0: Map[String, VarOrConst] ): ( Parenable, Map[String, VarOrConst] ) = et match {
    case ETTop( pol )    => ( Parenable( Precedence.max, addPol( "⊤", pol ) ), t0 )
    case ETBottom( pol ) => ( Parenable( Precedence.max, addPol( "⊥", pol ) ), t0 )
    case ETWeakening( f, pol ) =>
      val ( f_, t1 ) = show( f, true, Set(), t0 )
      ( Parenable( Precedence.max, addPol( "wk", pol ) <> "{" <> f_.inPrec( 0 ) <> "}" ), t1 )
    case ETAtom( a, pol ) =>
      val ( a_, t1 ) = show( a, true, Set(), t0 )
      ( Parenable( Precedence.app, addPol( a_.inPrec( Precedence.app ), pol ) ), t1 )
    case ETMerge( a, b ) =>
      val ( a_, t1 ) = show( a, t0 )
      val ( b_, t2 ) = show( b, t1 )
      Parenable( Precedence.iff, a_.inPrec( Precedence.iff ) <+> "⊔" </> b_.inPrec( Precedence.iff + 1 ) ) -> t2
    case ETNeg( a ) =>
      val ( a_, t1 ) = show( a, t0 )
      Parenable( Precedence.neg, "¬" <> a_.inPrec( Precedence.neg + 1 ) ) -> t1
    case ETAnd( a, b ) =>
      val ( a_, t1 ) = show( a, t0 )
      val ( b_, t2 ) = show( b, t1 )
      Parenable( Precedence.conj, a_.inPrec( Precedence.conj ) <+> "∧" </> b_.inPrec( Precedence.conj + 1 ) ) -> t2
    case ETOr( a, b ) =>
      val ( a_, t1 ) = show( a, t0 )
      val ( b_, t2 ) = show( b, t1 )
      Parenable( Precedence.disj, a_.inPrec( Precedence.disj ) <+> "∨" </> b_.inPrec( Precedence.disj + 1 ) ) -> t2
    case ETImp( a, b ) =>
      val ( a_, t1 ) = show( a, t0 )
      val ( b_, t2 ) = show( b, t1 )
      Parenable( Precedence.impl, a_.inPrec( Precedence.impl + 1 ) <+> "→" </> b_.inPrec( Precedence.impl ) ) -> t2
    case ETStrongQuantifierBlock( sh, evs, child ) if evs.nonEmpty =>
      val ( sh_, t1 ) = show( sh, true, Set(), t0 )
      val ( evs_, t2 ) = shows( evs.toList, true, Set(), t1 )
      val ( child_, t3 ) = show( child, t2 )
      Parenable( Precedence.conj, sh_.inPrec( Precedence.conj ) <+>
        "+ev^{" <> sepByComma( evs_.map( _.inPrec( 0 ) ) ) <> "}" </>
        child_.inPrec( Precedence.conj ) ) -> t3
    case ETSkolemQuantifier( sh, skTerm, _, child ) =>
      val ( sh_, t1 ) = show( sh, true, Set(), t0 )
      val ( skTerm_, t2 ) = show( skTerm, true, Set(), t1 )
      val ( child_, t3 ) = show( child, t2 )
      Parenable( Precedence.conj, sh_.inPrec( Precedence.conj ) <+> "+sk^{" <> skTerm_.inPrec( 0 ) <> "}" </>
        child_.inPrec( Precedence.conj ) ) -> t3
    case ETWeakQuantifierBlock( sh, n, insts ) if n > 0 =>
      val ( sh_, t1 ) = show( sh, true, Set(), t0 )
      var t2 = t1
      val insts_ = insts.toList map {
        case ( terms, child ) =>
          val ( terms_, t3 ) = shows( terms.toList, true, Set(), t2 )
          val ( child_, t4 ) = show( child, t3 )
          t2 = t4
          val termsDoc = sepByComma( terms_.map( _.inPrec( 0 ) ) )
          (
            termsDoc.render( Integer.MAX_VALUE ),
            group( nest( "+^{" <> termsDoc <> "}" </> child_.inPrec( Precedence.conj ) ) ) )
      }
      Parenable( Precedence.conj, sep( sh_.inPrec( Precedence.conj ) +: insts_.sortBy( _._1 ).map( _._2 ), line ) ) -> t2
    case ETDefinition( shallow, child ) =>
      val ( sh_, t1 ) = show( shallow, true, Set(), t0 )
      val ( child_, t2 ) = show( child, t1 )
      Parenable( Precedence.conj, sh_.inPrec( Precedence.conj ) <+> "+def" </> child_.inPrec( Precedence.conj ) ) -> t2
  }

}