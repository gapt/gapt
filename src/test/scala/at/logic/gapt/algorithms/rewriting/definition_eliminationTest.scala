package at.logic.gapt.algorithms.rewriting

import at.logic.gapt.proofs.HOLSequent
import org.specs2.mutable._
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.proofs.NullaryProof

class definition_eliminationTest extends Specification {
  object proof1 {
    val List( alphasym, betasym, xsym, ysym ) = List( "\\alpha", "\\beta", "x", "y" )
    val List( p, q, a, b, tsym ) = List( "P", "Q", "A", "B", "t" )
    val List( t ) = List( tsym ) map ( FOLConst.apply )
    val List( alpha, beta, x, y ) = List( alphasym, betasym, xsym, ysym ).map( FOLVar.apply )
    val qa = FOLAtom( q, alpha :: Nil )
    val qx = FOLAtom( q, x :: Nil )
    val pab = FOLAtom( p, List( alpha, beta ) )
    val pay = FOLAtom( p, List( alpha, y ) )
    val pty = FOLAtom( p, List( t, y ) )
    val pxy = FOLAtom( p, List( x, y ) )
    val ax = FOLAtom( a, x :: Nil )
    val at = FOLAtom( a, t :: Nil )
    val aa = FOLAtom( a, alpha :: Nil )
    val bx = FOLAtom( b, x :: Nil )
    val eqxt = Eq( x, t )
    val allypay = All( y, pay )
    val allypty = All( y, pty )
    val allypxy = All( y, pxy )
    val allxypxy = All( x, allypxy )
    val allxax = All( x, ax )
    val exformula = Ex( x, And( qx, ax ) )

    val i1 = Axiom( List( qa ), List( qa ) )
    val i2 = ForallLeftRule( i1, i1.root.antecedent( 0 ), All( x, qx ), alpha )

    val i3 = Axiom( List( pab ), List( pab ) )
    val i4 = ForallLeftRule( i3, i3.root.antecedent( 0 ), allypay, beta )
    val i5 = ForallRightRule( i4, i4.root.succedent( 0 ), allypay, beta )
    val i6 = DefinitionRightRule( i5, i5.root.succedent( 0 ), aa )
    val i7 = ForallLeftRule( i6, i6.root.antecedent( 0 ), allxypxy, alpha )
    val i8 = DefinitionLeftRule( i7, i7.root.antecedent( 0 ), allxax )
    val i9 = AndRightRule( i2, i8, i2.root.succedent( 0 ), i8.root.succedent( 0 ) )
    val i10 = ExistsRightRule( i9, i9.root.succedent( 0 ), exformula, alpha )
    val i11 = DefinitionRightRule( i10, i10.root.succedent( 0 ), Ex( x, bx ) )
    val i12 = AndLeft2Rule( i11, ax, i11.root.antecedent( 0 ) )

    val i13 = Axiom( eqxt :: Nil, eqxt :: Nil )
    val i14 = EquationLeft1Rule( i13, i12, i13.root.succedent( 0 ), i12.root.antecedent( 1 ), And( at, All( x, qx ) ) )

    val def1 = ( ax, All( y, pxy ) )
    val def2 = ( bx, And( qx, ax ) )
    val dmap = Map[LambdaExpression, LambdaExpression]() + def1 + def2

    def getoccids( p: LKProof, l: List[String] ): List[String] = p match {
      case r: NullaryProof[OccSequent] =>
        val line = r.rule + ": " + r.root.antecedent.map( _.id ).mkString( "," ) + " :- " + ( r.root.succedent.map( _.id ).mkString( "," ) )
        line :: Nil
      case r @ UnaryLKProof( _, p1, root, _, _ ) =>
        val line = r.rule + ": " + root.antecedent.map( _.id ).mkString( "," ) + " :- " + ( root.succedent.map( _.id ).mkString( "," ) )
        getoccids( p1, line :: l ) :+ line
      case r @ BinaryLKProof( _, p1, p2, root, _, _, _ ) =>
        val line = r.rule + ": " + root.antecedent.map( _.id ).mkString( "," ) + " :- " + ( root.succedent.map( _.id ).mkString( "," ) )
        val rec1 = getoccids( p1, line :: l )
        val rec2 = getoccids( p2, rec1 )
        ( rec1 ++ rec2 ) :+ line

    }

  }

  "Definition elimination" should {
    "work on formulas" in {
      val f = And( proof1.ax, Or( FOLAtom( proof1.a, proof1.t :: Nil ), proof1.bx ) )
      val f_ = DefinitionElimination( proof1.dmap, f )
      val correct_f = And( proof1.allypxy, Or( proof1.allypty, And( proof1.qx, proof1.allypxy ) ) )
      f_ mustEqual ( correct_f )
    }

    "work on a simple proof" in {
      import proof1._
      val elp = DefinitionElimination( dmap, i12 )
      val expected = HOLSequent( List( All( x, All( y, pxy ) ), And( All( y, pxy ), All( x, qx ) ) ), List( Ex( x, And( qx, All( y, pxy ) ) ) ) )
      expected must beSyntacticFSequentEqual( elp.root.toHOLSequent )
    }

    "work on a simple proof with equality" in {
      val elp = DefinitionElimination( proof1.dmap, proof1.i14 )
      ok
    }

  }

}
