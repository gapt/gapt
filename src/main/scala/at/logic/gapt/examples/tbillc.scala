package at.logic.gapt.examples

import at.logic.gapt.formats.simple.SimpleFOLParser
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base.LKProof

/**
 * This is an example used in the talk[1] at TbiLLC 2013. It generates a (cut-free) LK proof where the extracted
 * expansion tree has nested quantifiers.
 *
 * [1] http://www.illc.uva.nl/Tbilisi/Tbilisi2013/uploaded_files/inlineitem/riener.pdf
 */
object tbillc {
  def pa: LKProof = {
    val pa = SimpleFOLParser( "P(a)" )
    val expxqxy = SimpleFOLParser( "Exists x And P(x) Exists y Q(x,y)" )
    val qfa = SimpleFOLParser( "Q(a,f(a))" )
    val qay = SimpleFOLParser( "Exists y Q(a,y)" )
    val qga = SimpleFOLParser( "Q(a,g(a))" )
    val a = SimpleFOLParser.term( "a" )
    val fa = SimpleFOLParser.term( "f(a)" )
    val ga = SimpleFOLParser.term( "g(a)" )

    val a1 = Axiom( pa :: Nil, pa :: Nil )
    val a2 = Axiom( qfa :: Nil, qfa :: Nil )
    val r2 = ExistsRightRule( a2, a2.root.succedent( 0 ), qay, fa )

    val a3 = Axiom( qga :: Nil, qga :: Nil )
    val r3 = ExistsRightRule( a3, a3.root.succedent( 0 ), qay, ga )

    val r4 = OrLeftRule( r2, r3, r2.root.antecedent( 0 ), r3.root.antecedent( 0 ) )
    val r5 = ContractionRightRule( r4, r4.root.succedent( 0 ), r4.root.succedent( 1 ) )

    val r6 = AndRightRule( a1, r5, a1.root.succedent( 0 ), r5.root.succedent( 0 ) )
    val r7 = ExistsRightRule( r6, r6.root.succedent( 0 ), expxqxy, a )
    r7
  }

  def pb: LKProof = {
    val pb = SimpleFOLParser( "P(b)" )
    val expxqxy = SimpleFOLParser( "Exists x And P(x) Exists y Q(x,y)" )
    val qfb = SimpleFOLParser( "Q(b,f(b))" )
    val qby = SimpleFOLParser( "Exists y Q(b,y)" )
    val qgb = SimpleFOLParser( "Q(b,g(b))" )
    val b = SimpleFOLParser.term( "b" )
    val fb = SimpleFOLParser.term( "f(b)" )

    val gb = SimpleFOLParser.term( "g(b)" )

    val b1 = Axiom( pb :: Nil, pb :: Nil )

    val b2 = Axiom( qfb :: Nil, qfb :: Nil )
    val r2 = ExistsRightRule( b2, b2.root.succedent( 0 ), qby, fb )

    val b3 = Axiom( qgb :: Nil, qgb :: Nil )
    val r3 = ExistsRightRule( b3, b3.root.succedent( 0 ), qby, gb )

    val r4 = OrLeftRule( r2, r3, r2.root.antecedent( 0 ), r3.root.antecedent( 0 ) )
    val r5 = ContractionRightRule( r4, r4.root.succedent( 0 ), r4.root.succedent( 1 ) )

    val r6 = AndRightRule( b1, r5, b1.root.succedent( 0 ), r5.root.succedent( 0 ) )
    val r7 = ExistsRightRule( r6, r6.root.succedent( 0 ), expxqxy, b )
    r7
  }

  def apply() = {
    val a: LKProof = pa
    val b: LKProof = pb

    val allpab = SimpleFOLParser( "Forall x Or Q(x,f(x)) Q(x,g(x))" )
    val ta = SimpleFOLParser.term( "a" )
    val tb = SimpleFOLParser.term( "b" )
    //val x = (SimpleFOLParser.term "x").asInstanceOf[FOLVar]

    val r1 = OrLeftRule( a, b, a.root.antecedent( 0 ), b.root.antecedent( 0 ) )
    val r2 = ForallLeftRule( r1, r1.root.antecedent( 0 ), allpab, ta )
    val r3 = ForallLeftRule( r2, r2.root.antecedent( 0 ), allpab, tb )
    val r4 = ContractionLeftRule( r3, r3.root.antecedent( 1 ), r3.root.antecedent( 2 ) )
    val r5 = ContractionRightRule( r4, r4.root.succedent( 0 ), r4.root.succedent( 1 ) )
    r5
  }

}
