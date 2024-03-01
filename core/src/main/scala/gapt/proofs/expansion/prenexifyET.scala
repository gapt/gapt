package gapt.proofs.expansion

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.hol.containsQuantifierOnLogicalLevel
import gapt.expr.subst.Substitution
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.logic.Polarity
import gapt.proofs.Sequent
import gapt.proofs.SequentFlatMapOp
import gapt.proofs.context.Context

object prenexifyET {
  private def weakQuantifier( polarity: Polarity ) =
    if ( polarity.inSuc ) Ex else All

  private def handleBinary(
    f1: Formula, f2: Formula,
    p1: Polarity, p2: Polarity,
    newPol: Polarity,
    shConn: ( Formula, Formula ) => Formula ): Formula = {
    val f1_ = apply( f1, p1 )
    val f2_ = apply( f2, p2 )

    val fvs = freeVariables( Seq( f1, f2 ) )
    val Some( ( vs1_, matrix1_ ) ) = weakQuantifier( p1 ).Block.unapply( f1_ )
    val ( vs1: List[Var] @unchecked, matrix1 ) = Substitution( rename( vs1_, fvs ) )( ( vs1_, matrix1_ ) )
    val Some( ( vs2_, matrix2_ ) ) = weakQuantifier( p2 ).Block.unapply( f2_ )
    val ( vs2: List[Var] @unchecked, matrix2 ) = Substitution( rename( vs2_, fvs ++ vs1 ) )( ( vs2_, matrix2_ ) )

    weakQuantifier( newPol ).Block( vs1 ++ vs2, shConn( matrix1, matrix2 ) )
  }

  private def apply( formula: Formula, pol: Polarity ): Formula = formula match {
    case _ if !containsQuantifierOnLogicalLevel( formula ) => formula
    case Neg( a ) => Neg( apply( a, !pol ) )
    case And( a, b ) => handleBinary( a, b, pol, pol, pol, And( _, _ ) )
    case Or( a, b ) => handleBinary( a, b, pol, pol, pol, Or( _, _ ) )
    case Imp( a, b ) => handleBinary( a, b, !pol, pol, pol, Imp( _, _ ) )
    case All.Block( vs, f ) if vs.nonEmpty && pol.inAnt => All.Block( vs, apply( f, pol ) )
    case Ex.Block( vs, f ) if vs.nonEmpty && pol.inSuc => Ex.Block( vs, apply( f, pol ) )
  }

  private def handleBinary(
    et1: ExpansionTree, et2: ExpansionTree,
    newPol:           Polarity,
    shConn:           ( Formula, Formula ) => Formula,
    etConn:           ( ExpansionTree, ExpansionTree ) => ExpansionTree,
    binaryInPolarity: Polarity ): ExpansionTree = {
    val ETWeakQuantifierBlock( sh1, n1, insts1 ) = apply( et1 )
    val ETWeakQuantifierBlock( sh2, n2, insts2 ) = apply( et2 )

    val fvs = freeVariables( Seq( sh1, sh2 ) )
    val Some( ( vs1_, matrix1_ ) ) = weakQuantifier( et1.polarity ).Block.unapply( sh1 )
    val ( vs1: List[Var] @unchecked, matrix1 ) = Substitution( rename( vs1_, fvs ) )( ( vs1_, matrix1_ ) )
    val Some( ( vs2_, matrix2_ ) ) = weakQuantifier( et2.polarity ).Block.unapply( sh2 )
    val ( vs2: List[Var] @unchecked, matrix2 ) = Substitution( rename( vs2_, fvs ++ vs1 ) )( ( vs2_, matrix2_ ) )

    val sh = weakQuantifier( newPol ).Block( vs1 ++ vs2, shConn( matrix1, matrix2 ) )

    ETWeakQuantifierBlock( sh, n1 + n2,
      if ( newPol == binaryInPolarity ) {
        for {
          ( ts1, inst1 ) <- insts1
          ( ts2, inst2 ) <- insts2
        } yield ts1 ++ ts2 -> etConn( inst1, inst2 )
      } else {
        val weak1 = ETWeakening( matrix1, et1.polarity )
        val weak2 = ETWeakening( matrix2, et2.polarity )
        val insts1New = for ( ( ts, inst ) <- insts1 ) yield ts ++ vs2 -> etConn( inst, weak2 )
        val insts2New = for ( ( ts, inst ) <- insts2 ) yield vs1 ++ ts -> etConn( weak1, inst )
        Seq() ++ insts1New ++ insts2New
      } )
  }

  def apply( et: ExpansionTree ): ExpansionTree = et match {
    case _ if !containsQuantifierOnLogicalLevel( et.shallow ) => et
    case ETNeg( a ) =>
      val ETWeakQuantifierBlock( sh, n, insts ) = apply( a )
      val Some( ( vs, matrix ) ) = weakQuantifier( a.polarity ).Block.unapply( sh )
      ETWeakQuantifierBlock( weakQuantifier( a.polarity ).Block( vs, -matrix ), n,
        Map() ++ insts.view.mapValues( ETNeg( _ ) ).toMap )
    case ETAnd( a, b ) => handleBinary( a, b, et.polarity, And( _, _ ), ETAnd( _, _ ), Polarity.InSuccedent )
    case ETOr( a, b )  => handleBinary( a, b, et.polarity, Or( _, _ ), ETOr( _, _ ), Polarity.InAntecedent )
    case ETImp( a, b ) => handleBinary( a, b, et.polarity, Imp( _, _ ), ETImp( _, _ ), Polarity.InAntecedent )
    case ETWeakQuantifierBlock( sh1, n1, insts1 ) =>
      ETWeakQuantifierBlock( apply( sh1, et.polarity ), n1, Map() ++ insts1.view.mapValues( apply ).toMap )
  }

  def toSequent( et: ExpansionTree ): ExpansionSequent = ( et: @unchecked ) match {
    case ETNeg( a )                         => toSequent( a )
    case ETAnd( a, b ) if et.polarity.inAnt => toSequent( a ) ++ toSequent( b )
    case ETImp( a, b ) if et.polarity.inSuc => toSequent( a ) ++ toSequent( b )
    case ETOr( a, b ) if et.polarity.inSuc  => toSequent( a ) ++ toSequent( b )
    case _ if et.polarity.inSuc             => Sequent() :+ et
    case _ if et.polarity.inAnt             => et +: Sequent()
  }

  def apply( ep: ExpansionProof ): ExpansionProof =
    eliminateMerges( ExpansionProof(
      ep.expansionSequent.elements.
        flatMapS( toSequent ).
        map( apply ) ) )

  def exceptTheory( ep: ExpansionProof )( implicit ctx: Context ): ExpansionProof =
    eliminateMerges( ExpansionProof(
      ep.theoryPart ++ ep.nonTheoryPart.elements.flatMapS( toSequent ).map( apply ) ) )
}
