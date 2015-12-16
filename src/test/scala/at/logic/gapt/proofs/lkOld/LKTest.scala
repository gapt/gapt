/*
* LKTest.scala
*
*/

package at.logic.gapt.proofs.lkOld

import at.logic.gapt.expr.Substitution
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.expansionTrees.{ merge, ExpansionSequent, ETAtom, ETWeakQuantifier }
import org.specs2.mutable._
import at.logic.gapt.expr._
import base._

/**
 * The following properties of each rule are tested:
 * 1) The right principal formula is created
 * 2) The principal formula is managed correctly
 * 3) The Auxiliaries formulas are managed in the correct way
 * 4) The context is unchanged with regard to multiset equality
 * 5) The formula occurrences are different from the upper sequents occurrences
 *
 * Still missing for each rule:
 * 1) To check that all exceptions are thrown when needed
 */
class LKTest extends Specification {

  val c1 = Var( "a", Ti -> To )
  val v1 = Var( "x", Ti )
  val f1 = HOLAtom( c1, v1 :: Nil )
  val ax = Axiom( f1 :: Nil, f1 :: Nil )
  val a1 = ax // Axiom return a pair of the proof and a mapping and we want only the proof here
  val c2 = Var( "b", Ti -> To )
  val v2 = Var( "c", Ti )
  val f2 = HOLAtom( c1, v1 :: Nil )
  val f3 = HOLAtom( Var( "e", To ) )
  val a2 = Axiom( f2 :: f3 :: Nil, f2 :: f3 :: Nil )
  val a3 = Axiom( f2 :: f2 :: f3 :: Nil, f2 :: f2 :: f3 :: Nil )
  val ap = Axiom( f1 :: f1 :: Nil, Nil )
  val a4 = ap
  val pr = WeakeningRightRule( ax, f1 )

  val pr1 = OrRightRule( pr, f1, f1 )
  val pr2 = WeakeningLeftRule( ax, f1 )
  val pr3 = AndLeftRule( pr2, f1, f1 )
  "The factories/extractors for LK" should {

    "work for Axioms" in {
      "- Formula occurrences have correct formulas" in {
        ( a1 ) must beLike { case Axiom( OccSequent( x, y ) ) => ( x( 0 ).formula == f1 ) && ( y( 0 ).formula == f1 ) must_== true }
      }
      "- Same formulas on the same side must become different occurrences" in {
        val ant = a4.root.antecedent.toList
        ( ant.length ) must beEqualTo( 2 )
        ( ant.head ) must not be ( ant.last )
      }
    }

    "work for WeakeningLeftRule" in {
      val a = WeakeningLeftRule( a2, f1 )
      val ( up1, OccSequent( x, y ), prin1 ) = WeakeningLeftRule.unapply( a ).get
      "- Principal formula is created correctly" in {
        ( prin1.formula ) must beEqualTo( f1 )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( x ) must contain( prin1 )
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ( ( x.filterNot( _ == prin1 ) ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.antecedent ).toList.map( x => x.formula ) )
        ( ( y ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.succedent ).toList.map( x => x.formula ) )
      }
    }

    "work for WeakeningRightRule" in {
      val a = WeakeningRightRule( a2, f1 )
      val ( up1, OccSequent( x, y ), prin1 ) = WeakeningRightRule.unapply( a ).get
      "- Principal formula is created correctly" in {
        ( prin1.formula ) must beEqualTo( f1 )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( y ) must contain( prin1 )
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ( ( y.filterNot( _ == prin1 ) ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.succedent ).toList.map( x => x.formula ) )
        ( ( x ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.antecedent ).toList.map( x => x.formula ) )
      }
    }

    "work for ContractionLeftRule" in {
      val a = ContractionLeftRule( a3, a3.root.antecedent( 0 ), a3.root.antecedent( 1 ) )
      val ( up1, OccSequent( x, y ), aux1, aux2, prin1 ) = ContractionLeftRule.unapply( a ).get
      "- Principal formula is created correctly" in {
        ( prin1.formula ) must beEqualTo( f2 )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( x.map( x => x.formula ) ) must contain( prin1.formula )
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        ( x.map( x => x.formula ).filter( y => y == aux1.formula ) ) must be_!=( 2 )
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ( ( x.filterNot( _ == prin1 ) ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.antecedent.filterNot( _ == aux1 ).filterNot( _ == aux2 ) ).toList.map( x => x.formula ) )
        ( ( y ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.succedent ).toList.map( x => x.formula ) )
      }
    }

    "work for ContractionRightRule" in {
      val a = ContractionRightRule( a3, a3.root.succedent( 0 ), a3.root.succedent( 1 ) )
      val ( up1, OccSequent( x, y ), aux1, aux2, prin1 ) = ContractionRightRule.unapply( a ).get
      "- Principal formula is created correctly" in {
        ( prin1.formula ) must beEqualTo( f2 )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( y.map( x => x.formula ) ) must contain( prin1.formula )
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        ( y.map( y => y.formula ).filter( x => x == aux1.formula ) ) must be_!=( 2 )
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ( ( y.filterNot( _ == prin1 ) ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.succedent.filterNot( _ == aux1 ).filterNot( _ == aux2 ) ).toList.map( x => x.formula ) )
        ( ( x ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.antecedent ).toList.map( x => x.formula ) )
      }
    }

    "work for CutRule" in {
      val a = CutRule( a2, a3, a2.root.succedent( 0 ), a3.root.antecedent( 0 ) )
      val ( up1, up2, OccSequent( x, y ), aux1, aux2 ) = CutRule.unapply( a ).get
      "- Lower sequent must not contain the auxiliary formulas" in {
        ( y.filter( z => z.formula == f2 ) ).size must beEqualTo( 2 )
        ( x.filter( z => z.formula == f2 ) ).size must beEqualTo( 2 )
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ( ( y ).map( x => x.formula ) ) must beEqualTo( ( ( up1.root.succedent.filterNot( _ == aux1 ) ) ++ up2.root.succedent ).map( x => x.formula ) )
        ( ( x ).map( x => x.formula ) ) must beEqualTo( ( up1.root.antecedent ++ ( up2.root.antecedent.filterNot( _ == aux2 ) ) ).map( x => x.formula ) )
      }
    }

    "work for AndRightRule" in {
      val a = AndRightRule( a1, a2, f1, f2 )
      val ( up1, up2, OccSequent( x, y ), aux1, aux2, prin1 ) = AndRightRule.unapply( a ).get
      "- Principal formula is created correctly" in {
        ( prin1.formula ) must beEqualTo( And( f1, f2 ) )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( y ) must contain( prin1 )
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        ( y.map( z => z.formula ) ) must not contain ( f1 )
        ( y.map( z => z.formula ) ) must not contain ( f2 )
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ( x.toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.antecedent.toList ++ up2.root.antecedent.toList ).map( x => x.formula ) )
        ( ( y.toList.map( x => x.formula ).filterNot( x => x == And( f1, f2 ) ) ) ) must beEqualTo( ( ( up1.root.succedent.filterNot( _ == aux1 ) ).toList ++ ( up2.root.succedent.filterNot( _ == aux2 ) ).toList ).map( x => x.formula ) )
      }
    }

    "work for AndLeft1Rule" in {
      val a = AndLeft1Rule( a2, f2, f1 )
      val ( up1, OccSequent( x, y ), aux1, prin1 ) = AndLeft1Rule.unapply( a ).get
      "- Principal formula is created correctly" in {
        ( prin1.formula ) must beEqualTo( And( f2, f1 ) )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( x ) must contain( prin1 )
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        ( x.map( z => z.formula ) ) must not contain ( f2 )
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ( ( x.filterNot( _ == prin1 ) ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.antecedent.filterNot( _ == aux1 ) ).toList.map( x => x.formula ) )
        ( ( y ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.succedent ).toList.map( x => x.formula ) )
      }
    }

    "work for AndLeft2Rule" in {
      val a = AndLeft2Rule( a2, f1, f2 )
      val ( up1, OccSequent( x, y ), aux1, prin1 ) = AndLeft2Rule.unapply( a ).get
      "- Principal formula is created correctly" in {
        ( prin1.formula ) must beEqualTo( And( f1, f2 ) )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( x ) must contain( prin1 )
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        ( x.map( z => z.formula ) ) must not contain ( f1 )
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ( ( x.filterNot( _ == prin1 ) ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.antecedent.filterNot( _ == aux1 ) ).toList.map( x => x.formula ) )
        ( ( y ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.succedent ).toList.map( x => x.formula ) )
      }
    }

    "work for AndLeftRule" in {
      val a = AndLeftRule( a2, f1, f3 )
      "- Principal formula is created correctly" in {
        ( a.prin.head.formula ) must beEqualTo( And( f1, f3 ) )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( a.root.antecedent ) must contain( a.prin.head )
      }

      "- Lower sequent must not contain the auxiliary formulas" in {
        ( a.root.antecedent ) must not( contain( f1 ) )
        ( a.root.antecedent ) must not( contain( f3 ) )
      }

      "- Principal formula is created correctly when auxiliary formulas are equal" in {
        ( pr3.prin.head.formula ) must beEqualTo( And( f1, f1 ) )
      }

      "- Lower sequent must not contain the auxiliary formulas when auxiliary formulas are equal" in {
        ( pr3.root.antecedent ) must not( contain( f1 ) )
      }
    }

    "work for OrLeftRule" in {
      val a = OrLeftRule( a1, a2, f1, f2 )
      val ( up1, up2, OccSequent( x, y ), aux1, aux2, prin1 ) = OrLeftRule.unapply( a ).get
      "- Principal formula is created correctly" in {
        ( prin1.formula ) must beEqualTo( Or( f1, f2 ) )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( x ) must contain( prin1 )
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        ( x.map( z => z.formula ) ) must not contain ( f1 )
        ( x.map( z => z.formula ) ) must not contain ( f2 )
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ( y.toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.succedent.toList ++ up2.root.succedent.toList ).map( x => x.formula ) )
        ( ( x.filterNot( _ == prin1 ) ).toList.map( x => x.formula ) ) must beEqualTo( ( ( up1.root.antecedent.filterNot( _ == aux1 ) ).toList ++ ( up2.root.antecedent.filterNot( _ == aux2 ) ).toList ).map( x => x.formula ) )
      }

      "- Descendants must be correctly computed" in {
        "(1)" in {
          // get descendant of occurrence of left auxiliary formula
          a.getDescendantInLowerSequent( a1.root.antecedent( 0 ) ) must beLike {
            case Some( x ) => x.formula == Or( f1, f2 ) must_== true
            case None      => ko
          }
        }
        "(2)" in {
          // get descendant of occurrence of left premise context in succedent
          a.getDescendantInLowerSequent( a1.root.succedent( 0 ) ) must beLike {
            case Some( x ) => x.formula == f1 must_== true
            case None      => ko
          }
        }
      }
    }

    "work for OrRightRule" in {
      "- Principal formula is created correctly when auxiliary formulas are equal" in {
        ( pr1.prin.head.formula ) must beEqualTo( Or( f1, f1 ) )
      }

      "- Lower sequent must not contain the auxiliary formulas when auxiliary formulas are equal" in {
        ( pr1.root.succedent ) must not( contain( f1 ) )
      }
    }

    "work for OrRight1Rule" in {
      val a = OrRight1Rule( a2, f2, f1 )
      val ( up1, OccSequent( x, y ), aux1, prin1 ) = OrRight1Rule.unapply( a ).get
      "- Principal formula is created correctly" in {
        ( prin1.formula ) must beEqualTo( Or( f2, f1 ) )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( y ) must contain( prin1 )
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        ( y.map( z => z.formula ) ) must not contain ( f2 )
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ( ( y.filterNot( _ == prin1 ) ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.succedent.filterNot( _ == aux1 ) ).toList.map( x => x.formula ) )
        ( ( x ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.antecedent ).toList.map( x => x.formula ) )
      }
    }

    "work for OrRight2Rule" in {
      val a = OrRight2Rule( a2, f1, f2 )
      val ( up1, OccSequent( x, y ), aux1, prin1 ) = OrRight2Rule.unapply( a ).get
      "- Principal formula is created correctly" in {
        ( prin1.formula ) must beEqualTo( Or( f1, f2 ) )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( y ) must contain( prin1 )
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        ( y.map( z => z.formula ) ) must not contain ( f1 )
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ( ( y.filterNot( _ == prin1 ) ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.succedent.filterNot( _ == aux1 ) ).toList.map( x => x.formula ) )
        ( ( x ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.antecedent ).toList.map( x => x.formula ) )
      }
    }

    "work for ImpLeftRule" in {
      val a = ImpLeftRule( a1, a2, f1, f2 )
      val ( up1, up2, OccSequent( x, y ), aux1, aux2, prin1 ) = ImpLeftRule.unapply( a ).get
      "- Principal formula is created correctly" in {
        ( prin1.formula ) must beEqualTo( Imp( f1, f2 ) )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( x ) must contain( prin1 )
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        ( y.filter( z => z.formula == f1 ) ).size must beEqualTo( 1 )
        ( x.filter( z => z.formula == f2 ) ).size must beEqualTo( 1 )
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        "1" in { ( y.toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.succedent.filterNot( _ == aux1 ).toList ++ ( up2.root.succedent ).toList ).map( x => x.formula ) ) }
        "2" in { ( ( x.filterNot( _ == prin1 ) ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.antecedent.toList ++ ( up2.root.antecedent.filterNot( _ == aux2 ) ).toList ).map( x => x.formula ) ) }
      }
    }

    "work for ImpRightRule" in {
      val a = ImpRightRule( a2, f2, f2 )
      val ( up1, OccSequent( x, y ), aux1, aux2, prin1 ) = ImpRightRule.unapply( a ).get
      "- Principal formula is created correctly" in {
        ( prin1.formula ) must beEqualTo( Imp( f2, f2 ) )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( y ) must contain( prin1 )
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        ( x.map( z => z.formula ) ) must not contain ( f2 )
        ( y.map( z => z.formula ) ) must not contain ( f2 )
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        "1" in { ( ( y.filterNot( _ == prin1 ) ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.succedent.filterNot( _ == aux2 ) ).toList.map( x => x.formula ) ) }
        "2" in { ( ( x ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.antecedent.filterNot( _ == aux1 ) ).toList.map( x => x.formula ) ) }
      }
    }

    "work for NegRightRule" in {
      val a = NegRightRule( a2, f2 )
      val ( up1, OccSequent( x, y ), aux1, prin1 ) = NegRightRule.unapply( a ).get
      "- Principal formula is created correctly" in {
        ( prin1.formula ) must beEqualTo( Neg( f2 ) )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( y ) must contain( prin1 )
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        ( x.map( z => z.formula ) ) must not contain ( f2 )
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ( ( y.filterNot( _ == prin1 ) ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.succedent ).toList.map( x => x.formula ) )
        ( ( x ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.antecedent.filterNot( _ == aux1 ) ).toList.map( x => x.formula ) )
      }
    }

    "work for NegLeftRule" in {
      val a = NegLeftRule( a2, f2 )
      val ( up1, OccSequent( x, y ), aux1, prin1 ) = NegLeftRule.unapply( a ).get
      "- Principal formula is created correctly" in {
        ( prin1.formula ) must beEqualTo( Neg( f2 ) )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( x ) must contain( prin1 )
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        ( y.map( z => z.formula ) ) must not contain ( f2 )
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ( ( x.filterNot( _ == prin1 ) ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.antecedent ).toList.map( x => x.formula ) )
        ( ( y ).toList.map( x => x.formula ) ) must beEqualTo( ( up1.root.succedent.filterNot( _ == aux1 ) ).toList.map( x => x.formula ) )
      }
    }

    "work for ForallLeftRule" in {
      val q = Var( "q", Ti -> To )
      val x = Var( "X", Ti )
      val subst = Abs( x, App( q, x ) ) // lambda x. q(x)
      val p = Var( "p", ( Ti -> To ) -> To )
      val a = Var( "a", Ti )
      val qa = HOLAtom( q, a :: Nil )
      val pl = HOLAtom( p, subst :: Nil )
      val aux = Or( pl, qa ) // p(lambda x. q(x)) or q(a)
      val z = Var( "Z", Ti -> To )
      val pz = HOLAtom( p, z :: Nil )
      val za = HOLAtom( z, a :: Nil )
      val main = All( z, Or( pz, za ) ) // forall lambda z. p(z) or z(a)
      val ax = Axiom( aux :: Nil, Nil )
      val rule = ForallLeftRule( ax, aux, main, subst )
      val ( up1, OccSequent( ant, succ ), aux1, prin1, term ) = ForallLeftRule.unapply( rule ).get
      "- Principal formula is created correctly" in {
        ( prin1.formula ) must beEqualTo( main )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( ant ) must contain( prin1 )
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        ( ant ) must not contain ( aux1 )
      }
    }

    "work for ForallRightRule" in {
      val x = Var( "X", Ti -> To ) // eigenvar
      val p = Var( "p", ( Ti -> To ) -> To )
      val a = Var( "a", Ti )
      val xa = HOLAtom( x, a :: Nil )
      val px = HOLAtom( p, x :: Nil )
      val aux = Or( px, xa ) // p(x) or x(a)
      val z = Var( "Z", Ti -> To )
      val pz = HOLAtom( p, z :: Nil )
      val za = HOLAtom( z, a :: Nil )
      val main = All( z, Or( pz, za ) ) // forall lambda z. p(z) or z(a)
      val ax = Axiom( Nil, aux :: Nil )
      val rule = ForallRightRule( ax, aux, main, x )
      val ( up1, OccSequent( ant, succ ), aux1, prin1, ev ) = ForallRightRule.unapply( rule ).get
      "- Principal formula is created correctly" in {
        ( prin1.formula ) must beEqualTo( main )
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        ( succ ) must contain( prin1 )
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        ( succ ) must not contain ( aux1 )
      }
    }

    "work for weak quantifier rules" in {
      val List( x, y, z ) = List( ( "x", Ti -> Ti ), ( "y", Ti -> Ti ), ( "z", Ti -> Ti ) ) map ( u => Var( u._1, u._2 ) )
      val List( p, a, b ) = List(
        ( "P", ( Ti -> Ti ) -> ( ( Ti -> Ti ) -> ( ( Ti -> Ti ) -> To ) ) ),
        ( "a", Ti -> Ti ),
        ( "b", Ti -> Ti )
      ) map ( u => Const( u._1, u._2 ) )
      val paba = HOLAtom( p, List( a, b, a ) )
      val pxba = HOLAtom( p, List( x, b, a ) )
      val expxba = Ex( x, pxba )
      val allpxba = All( x, pxba )

      val ax1 = Axiom( paba :: Nil, Nil )
      ForallLeftRule( ax1, ax1.root.occurrences( 0 ), allpxba, a ).root.occurrences( 0 ).formula must_== ( allpxba )

      ForallLeftRule( ax1, ax1.root.occurrences( 0 ), allpxba, b ).root.occurrences( 0 ).formula must_== ( allpxba ) must throwAn[Exception]()

      val ax2 = Axiom( Nil, paba :: Nil )
      ExistsRightRule( ax2, ax2.root.occurrences( 0 ), expxba, a ).root.occurrences( 0 ).formula must_== ( expxba )
      ExistsRightRule( ax2, ax2.root.occurrences( 0 ), expxba, b ).root.occurrences( 0 ).formula must_== ( expxba ) must throwAn[Exception]()
    }

    "work for first order proofs (1)" in {
      val List( a, b ) = List( "a", "b" ) map ( FOLConst( _ ) )
      val List( x, y ) = List( "x", "y" ) map ( FOLVar( _ ) )
      val p = "P"
      val pay = FOLAtom( p, List( a, y ) )
      val allxpax = All( x, FOLAtom( p, List( a, x ) ) )
      val ax = Axiom( List( pay ), List( pay ) )
      val i1 = ForallLeftRule( ax, ax.root.antecedent( 0 ), allxpax, y )
      val i2 = ForallRightRule( i1, i1.root.succedent( 0 ), allxpax, y )
      val i3 = OrRight1Rule( i2, i2.root.succedent( 0 ), pay )

      i2.root.toHOLSequent match {
        case HOLSequent( List( f1 ), List( f2 ) ) =>
          f1 mustEqual ( allxpax )
          f2 mustEqual ( allxpax )
          f1 must beAnInstanceOf[FOLFormula]
          f2 must beAnInstanceOf[FOLFormula]
        case fs @ _ =>
          ko( "Wrong result sequent " + fs )
      }

      i3.root.toHOLSequent.formulas map ( _ must beAnInstanceOf[FOLFormula] )
    }

    "work for first order proofs (2)" in {
      val List( a, b ) = List( "a", "b" ) map ( FOLConst( _ ) )
      val List( x, y ) = List( "x", "y" ) map ( FOLVar( _ ) )
      val p = "P"
      val pay = FOLAtom( p, List( a, y ) )
      val allxpax = Ex( x, FOLAtom( p, List( a, x ) ) )
      val ax = Axiom( List( pay ), List( pay ) )
      val i1 = ExistsRightRule( ax, ax.root.succedent( 0 ), allxpax, y )
      val i2 = ExistsLeftRule( i1, i1.root.antecedent( 0 ), allxpax, y )
      i2.root.toHOLSequent match {
        case HOLSequent( List( f1 ), List( f2 ) ) =>
          f1 mustEqual ( allxpax )
          f2 mustEqual ( allxpax )
          f1 must beAnInstanceOf[FOLFormula]
          f2 must beAnInstanceOf[FOLFormula]
        case fs @ _ =>
          ko( "Wrong result sequent " + fs )
      }
    }

  }

  "Equality rules" should {
    val ( s, t ) = ( Const( "s", Ti ), Const( "t", Ti ) )
    val P = Const( "P", Ti -> To )
    val Q = Const( "Q", Ti -> ( Ti -> To ) )
    val est = Eq( s, t )
    val Ps = HOLAtom( P, List( s ) )
    val Pt = HOLAtom( P, List( t ) )

    val Qss = HOLAtom( Q, List( s, s ) )
    val Qst = HOLAtom( Q, List( s, t ) )
    val Qts = HOLAtom( Q, List( t, s ) )
    val Qtt = HOLAtom( Q, List( t, t ) )

    val ax1 = Axiom( List( est ), List( est ) )
    val ax2 = Axiom( List( Ps ), List( Ps ) )
    val ax3 = Axiom( List( Pt ), List( Pt ) )
    val ax4 = Axiom( List( Qss ), List( Qss ) )
    val ax5 = Axiom( List( Qtt ), List( Qtt ) )

    "refuse first auxiliary formulas that are not equations" in {
      EquationLeft1Rule( ax3, ax2, ax3.root.succedent.head, ax2.root.antecedent.head, HOLPosition( 2 ) ) must throwAn[LKRuleCreationException]
      EquationLeft2Rule( ax3, ax2, ax3.root.succedent.head, ax2.root.antecedent.head, HOLPosition( 2 ) ) must throwAn[LKRuleCreationException]
      EquationRight1Rule( ax3, ax2, ax3.root.succedent.head, ax2.root.succedent.head, HOLPosition( 2 ) ) must throwAn[LKRuleCreationException]
      EquationRight2Rule( ax3, ax2, ax3.root.succedent.head, ax2.root.succedent.head, HOLPosition( 2 ) ) must throwAn[LKRuleCreationException]
    }

    "refuse when the wrong term is at the target position" in {
      EquationLeft1Rule( ax1, ax3, ax1.root.succedent.head, ax3.root.antecedent.head, HOLPosition( 2 ) ) must throwAn[LKRuleCreationException]
      EquationLeft2Rule( ax1, ax2, ax1.root.succedent.head, ax2.root.antecedent.head, HOLPosition( 2 ) ) must throwAn[LKRuleCreationException]
      EquationRight1Rule( ax1, ax3, ax1.root.succedent.head, ax3.root.succedent.head, HOLPosition( 2 ) ) must throwAn[LKRuleCreationException]
      EquationRight2Rule( ax1, ax2, ax1.root.succedent.head, ax2.root.succedent.head, HOLPosition( 2 ) ) must throwAn[LKRuleCreationException]
    }

    "refuse when auxiliary formula cannot be transformed to main formula in one step" in {
      EquationLeft1Rule( ax1, ax4, ax1.root.succedent.head, ax4.root.antecedent.head, Qtt ) must throwAn[LKRuleCreationException]
      EquationLeft2Rule( ax1, ax5, ax1.root.succedent.head, ax5.root.antecedent.head, Qss ) must throwAn[LKRuleCreationException]
      EquationRight1Rule( ax1, ax4, ax1.root.succedent.head, ax4.root.succedent.head, Qtt ) must throwAn[LKRuleCreationException]
      EquationRight2Rule( ax1, ax5, ax1.root.succedent.head, ax5.root.succedent.head, Qss ) must throwAn[LKRuleCreationException]
    }

    "correctly perform replacements" in {

      val sequent1 = HOLSequent( List( est, Qst ), List( Qss ) )
      val sequent2 = HOLSequent( List( est, Qts ), List( Qss ) )

      val sequent3 = HOLSequent( List( est, Qts ), List( Qtt ) )
      val sequent4 = HOLSequent( List( est, Qst ), List( Qtt ) )

      val sequent5 = HOLSequent( List( est, Qss ), List( Qst ) )
      val sequent6 = HOLSequent( List( est, Qss ), List( Qts ) )

      val sequent7 = HOLSequent( List( est, Qtt ), List( Qts ) )
      val sequent8 = HOLSequent( List( est, Qtt ), List( Qst ) )

      EquationLeft1Rule( ax1, ax4, ax1.root.succedent.head, ax4.root.antecedent.head, HOLPosition( 2 ) ).root.toHOLSequent must beEqualTo( sequent1 )
      EquationLeft1Rule( ax1, ax4, ax1.root.succedent.head, ax4.root.antecedent.head, Qts ).root.toHOLSequent must beEqualTo( sequent2 )

      EquationLeft2Rule( ax1, ax5, ax1.root.succedent.head, ax5.root.antecedent.head, HOLPosition( 2 ) ).root.toHOLSequent must beEqualTo( sequent3 )
      EquationLeft2Rule( ax1, ax5, ax1.root.succedent.head, ax5.root.antecedent.head, Qst ).root.toHOLSequent must beEqualTo( sequent4 )

      EquationRight1Rule( ax1, ax4, ax1.root.succedent.head, ax4.root.succedent.head, HOLPosition( 2 ) ).root.toHOLSequent must beEqualTo( sequent5 )
      EquationRight1Rule( ax1, ax4, ax1.root.succedent.head, ax4.root.succedent.head, Qts ).root.toHOLSequent must beEqualTo( sequent6 )

      EquationRight2Rule( ax1, ax5, ax1.root.succedent.head, ax5.root.succedent.head, HOLPosition( 2 ) ).root.toHOLSequent must beEqualTo( sequent7 )
      EquationRight2Rule( ax1, ax5, ax1.root.succedent.head, ax5.root.succedent.head, Qst ).root.toHOLSequent must beEqualTo( sequent8 )
    }
  }

  "Weakening macro rules" should {
    val x = FOLVar( "x" )
    val y = FOLVar( "y" )

    val Px = FOLAtom( "P", List( x ) )
    val Py = FOLAtom( "P", List( y ) )

    val ax = Axiom( List( Px ), List( Px ) )
    "perform zero weakenings" in {

      WeakeningLeftMacroRule( ax, Nil ) must beEqualTo( ax )
      WeakeningRightMacroRule( ax, Nil ) must beEqualTo( ax )
      WeakeningMacroRule( ax, Nil, Nil ) must beEqualTo( ax )
    }

    "correctly perform multiple weakenings" in {
      val proof = WeakeningRightRule( WeakeningLeftRule( WeakeningLeftRule( ax, Py ), Neg( Py ) ), Py )

      WeakeningMacroRule( ax, List( Neg( Py ), Py ), List( Py ) ).root.toHOLSequent.multiSetEquals( proof.root.toHOLSequent ) must beTrue
    }
  }

  "Contraction macro rules" should {
    val x = FOLVar( "x" )
    val y = FOLVar( "y" )

    val Px = FOLAtom( "P", List( x ) )
    val Py = FOLAtom( "P", List( y ) )

    val ax = Axiom( List( Px ), List( Px ) )

    "perform zero contractions" in {
      ContractionLeftMacroRule( ax, Nil ) must beEqualTo( ax )
      ContractionLeftMacroRule( ax, List( ax.root.antecedent.head ) ) must beEqualTo( ax )
      ContractionRightMacroRule( ax, Nil ) must beEqualTo( ax )
      ContractionRightMacroRule( ax, List( ax.root.succedent.head ) ) must beEqualTo( ax )
    }

    "return the original proof if there is nothing to do" in {
      ContractionLeftMacroRule( ax, Px ).root.toHOLSequent must beEqualTo( ax.root.toHOLSequent )
      ContractionLeftMacroRule( ax, Py ).root.toHOLSequent must beEqualTo( ax.root.toHOLSequent )
      ContractionRightMacroRule( ax, Px ).root.toHOLSequent must beEqualTo( ax.root.toHOLSequent )
      ContractionRightMacroRule( ax, Py ).root.toHOLSequent must beEqualTo( ax.root.toHOLSequent )
    }

    "correctly perform multiple contractions" in {
      val ax2 = Axiom( List( Px, Px, Py, Px ), List( Px, Neg( Px ), Neg( Px ) ) )

      val sequent1 = HOLSequent( List( Py, Px ), List( Px, Neg( Px ), Neg( Px ) ) )
      val sequent2 = HOLSequent( List( Px, Px, Py, Px ), List( Px, Neg( Px ) ) )
      ContractionLeftMacroRule( ax2, Px ).root.toHOLSequent must beEqualTo( sequent1 )
      ContractionRightMacroRule( ax2, Neg( Px ) ).root.toHOLSequent must beEqualTo( sequent2 )
    }
  }

  "Equality macro rules" should {
    val ( s, t ) = ( Const( "s", Ti ), Const( "t", Ti ) )
    val P = Const( "P", Ti -> To )
    val Q = Const( "Q", Ti -> ( Ti -> To ) )
    val est = Eq( s, t )
    val Ps = HOLAtom( P, List( s ) )
    val Pt = HOLAtom( P, List( t ) )

    val Qss = HOLAtom( Q, List( s, s ) )
    val Qst = HOLAtom( Q, List( s, t ) )
    val Qts = HOLAtom( Q, List( t, s ) )
    val Qtt = HOLAtom( Q, List( t, t ) )

    val ax1 = Axiom( List( est ), List( est ) )
    val ax2 = Axiom( List( Ps ), List( Ps ) )
    val ax3 = Axiom( List( Pt ), List( Pt ) )
    val ax4 = Axiom( List( Qss ), List( Qss ) )
    val ax5 = Axiom( List( Qtt ), List( Qtt ) )

    val eq = ax1.root.succedent.head

    "choose the right rule to use" in {
      val sequent1 = HOLSequent( List( est, Ps ), List( Pt ) )
      val sequent2 = HOLSequent( List( est, Pt ), List( Ps ) )

      EquationLeftRule( ax1, ax3, eq, ax3.root.antecedent.head, Ps ).root.toHOLSequent must beEqualTo( sequent1 )
      EquationLeftRule( ax1, ax2, eq, ax2.root.antecedent.head, Pt ).root.toHOLSequent must beEqualTo( sequent2 )

      EquationRightRule( ax1, ax2, eq, ax2.root.succedent.head, Pt ).root.toHOLSequent must beEqualTo( sequent1 )
      EquationRightRule( ax1, ax3, eq, ax3.root.succedent.head, Ps ).root.toHOLSequent must beEqualTo( sequent2 )

      EquationLeftRule( ax1, ax3, eq, ax3.root.antecedent.head, HOLPosition( 2 ) ).root.toHOLSequent must beEqualTo( sequent1 )
      EquationLeftRule( ax1, ax2, eq, ax2.root.antecedent.head, HOLPosition( 2 ) ).root.toHOLSequent must beEqualTo( sequent2 )

      EquationRightRule( ax1, ax2, eq, ax2.root.succedent.head, HOLPosition( 2 ) ).root.toHOLSequent must beEqualTo( sequent1 )
      EquationRightRule( ax1, ax3, eq, ax3.root.succedent.head, HOLPosition( 2 ) ).root.toHOLSequent must beEqualTo( sequent2 )
    }

    "perform correctly if there is only one replacement to be made" in {

      val sequent1 = HOLSequent( List( est, Qst ), List( Qss ) )
      val sequent2 = HOLSequent( List( est, Qts ), List( Qss ) )

      val sequent3 = HOLSequent( List( est, Qts ), List( Qtt ) )
      val sequent4 = HOLSequent( List( est, Qst ), List( Qtt ) )

      val sequent5 = HOLSequent( List( est, Qss ), List( Qst ) )
      val sequent6 = HOLSequent( List( est, Qss ), List( Qts ) )

      val sequent7 = HOLSequent( List( est, Qtt ), List( Qts ) )
      val sequent8 = HOLSequent( List( est, Qtt ), List( Qst ) )

      val proof1 = EquationLeftMacroRule( ax1, ax4, eq, ax4.root.antecedent.head, Nil, List( HOLPosition( 2 ) ) )
      val proof2 = EquationLeftMacroRule( ax1, ax4, eq, ax4.root.antecedent.head, Qts )
      val proof3 = EquationLeftMacroRule( ax1, ax5, eq, ax5.root.antecedent.head, List( HOLPosition( 2 ) ), Nil )
      val proof4 = EquationLeftMacroRule( ax1, ax5, eq, ax5.root.antecedent.head, Qst )
      val proof5 = EquationRightMacroRule( ax1, ax4, eq, ax4.root.succedent.head, Nil, List( HOLPosition( 2 ) ) )
      val proof6 = EquationRightMacroRule( ax1, ax4, eq, ax4.root.succedent.head, Qts )
      val proof7 = EquationRightMacroRule( ax1, ax5, eq, ax5.root.succedent.head, List( HOLPosition( 2 ) ), Nil )
      val proof8 = EquationRightMacroRule( ax1, ax5, eq, ax5.root.succedent.head, Qst )

      proof1.root.toHOLSequent must beEqualTo( sequent1 )
      proof2.root.toHOLSequent must beEqualTo( sequent2 )

      proof3.root.toHOLSequent must beEqualTo( sequent3 )
      proof4.root.toHOLSequent must beEqualTo( sequent4 )

      proof5.root.toHOLSequent must beEqualTo( sequent5 )
      proof6.root.toHOLSequent must beEqualTo( sequent6 )

      proof7.root.toHOLSequent must beEqualTo( sequent7 )
      proof8.root.toHOLSequent must beEqualTo( sequent8 )
    }

    "perform correctly when several replacements are made" in {
      val sequent1 = HOLSequent( List( est, Qtt ), List( Qss ) )
      val sequent2 = HOLSequent( List( est, Qss ), List( Qtt ) )

      val proof1 = EquationLeftMacroRule( ax1, ax4, eq, ax4.root.antecedent.head, Qtt )
      val proof2 = EquationLeftMacroRule( ax1, ax5, eq, ax5.root.antecedent.head, Qss )
      val proof3 = EquationRightMacroRule( ax1, ax4, eq, ax4.root.succedent.head, Qtt )
      val proof4 = EquationRightMacroRule( ax1, ax5, eq, ax5.root.succedent.head, Qss )

      proof1.root.toHOLSequent must beEqualTo( sequent1 )
      proof2.root.toHOLSequent must beEqualTo( sequent2 )
      proof3.root.toHOLSequent must beEqualTo( sequent2 )
      proof4.root.toHOLSequent must beEqualTo( sequent1 )

    }
  }

  "The induction rule" should {
    val zero = FOLConst( "0" )
    val x = FOLVar( "x" )
    val y = FOLVar( "y" )
    val Sx = FOLFunction( "s", List( x ) )

    val P0y = FOLAtom( "P", List( zero, y ) )
    val Pxy = FOLAtom( "P", List( x, y ) )
    val PSxy = FOLAtom( "P", List( Sx, y ) )

    "correctly construct a small induction proof" in {
      val ax1 = Axiom( List( P0y ), List( P0y ) )
      val occZero = ax1.root.succedent.head

      val ax2 = Axiom( List( Pxy ), List( PSxy ) )
      val occX = ax2.root.antecedent.head
      val occSx = ax2.root.succedent.head

      InductionRule( ax1, ax2, occZero, occX, occSx, x )

      success
    }

    "fail if S does not occur in the right place" in {
      val Tx = FOLFunction( "T", List( x ) )
      val PTxy = FOLAtom( "P", List( Tx, y ) )

      val ax1 = Axiom( List( P0y ), List( P0y ) )
      val occZero = ax1.root.succedent.head

      val ax2 = Axiom( List( Pxy ), List( PTxy ) )
      val occX = ax2.root.antecedent.head
      val occSx = ax2.root.succedent.head

      InductionRule( ax1, ax2, occZero, occX, occSx, x ) must throwAn[LKRuleCreationException]
    }

    "fail if more than one variable needs to be substituted" in {
      val z = FOLVar( "z" )
      val P0z = FOLAtom( "P", List( zero, z ) )

      val ax1 = Axiom( List( P0z ), List( P0z ) )
      val occZero = ax1.root.succedent.head

      val ax2 = Axiom( List( Pxy ), List( PSxy ) )
      val occX = ax2.root.antecedent.head
      val occSx = ax2.root.succedent.head

      InductionRule( ax1, ax2, occZero, occX, occSx, x ) must throwAn[LKRuleCreationException]
    }

    "fail if different variables need to be substituted" in {
      val Sy = FOLFunction( "S", List( y ) )
      val PxSy = FOLAtom( "P", List( x, Sy ) )

      val ax1 = Axiom( List( P0y ), List( P0y ) )
      val occZero = ax1.root.succedent.head

      val ax2 = Axiom( List( Pxy ), List( PxSy ) )
      val occX = ax2.root.antecedent.head
      val occSx = ax2.root.succedent.head

      InductionRule( ax1, ax2, occZero, occX, occSx, x ) must throwAn[LKRuleCreationException]
    }

    "fail if the eigenvariable condition is not satisfied" in {
      val Qx = FOLAtom( "Q", List( x ) )
      val ax1 = Axiom( List( P0y ), List( P0y ) )
      val occZero = ax1.root.succedent.head

      val ax2 = Axiom( List( Pxy, Qx ), List( PSxy ) )
      val occX = ax2.root.antecedent.head
      val occSx = ax2.root.succedent.head

      InductionRule( ax1, ax2, occZero, occX, occSx, x ) must throwAn[LKRuleCreationException]

      val ax2_ = Axiom( List( Pxy ), List( PSxy, Qx ) )
      val occX_ = ax2_.root.antecedent.head
      val occSx_ = ax2_.root.succedent.head

      InductionRule( ax1, ax2, occZero, occX, occSx, x ) must throwAn[LKRuleCreationException]
    }
  }

  "proofFromInstances" should {
    val x = FOLVar( "x" )
    val y = FOLVar( "y" )
    val s1 = FOLConst( "s_1" )
    val s2 = FOLConst( "s_2" )
    val t11 = FOLConst( "t_11" )
    val t12 = FOLConst( "t_12" )
    val t21 = FOLConst( "t_21" )

    def F( x1: FOLTerm, x2: FOLTerm ) = FOLAtom( "F", List( x1, x2 ) )
    def G( x1: FOLTerm, x2: FOLTerm ) = FOLAtom( "G", List( x1, x2 ) )

    val et1 = merge( ETWeakQuantifier(
      All( x, All( y, F( x, y ) ) ),
      List(
        ( ETWeakQuantifier(
          All( y, F( s1, y ) ),
          List(
            ( ETAtom( F( s1, t11 ) ), t11 ),
            ( ETAtom( F( s1, t12 ) ), t12 )
          )
        ), s1 ),
        ( ETWeakQuantifier(
          All( y, F( s2, y ) ),
          List(
            ( ETAtom( F( s2, t21 ) ), t21 )
          )
        ), s2 )
      )
    ) )

    val et2 = merge( ETWeakQuantifier(
      Ex( x, Ex( y, G( x, y ) ) ),
      List(
        ( ETWeakQuantifier(
          Ex( y, G( s1, y ) ),
          List(
            ( ETAtom( G( s1, t11 ) ), t11 ),
            ( ETAtom( G( s1, t12 ) ), t12 )
          )
        ), s1 ),
        ( ETWeakQuantifier(
          Ex( y, G( s2, y ) ),
          List(
            ( ETAtom( G( s2, t21 ) ), t21 )
          )
        ), s2 )
      )
    ) )

    "correctly compute a small proof" in {
      val es = ExpansionSequent( List( et1 ), List( et2 ) )
      val p = Axiom( List( F( s1, t11 ), F( s1, t12 ), F( s2, t21 ) ), List( G( s1, t11 ), G( s1, t12 ), G( s2, t21 ) ) )

      proofFromInstances( p, es )

      success
    }

  }
  /*

  "Unary equality rules" should {
    val (s, t) = (Const("s", Ti), Const("t", Ti))
    val P = Const("P", Ti -> To)
    val Q = Const("Q", Ti -> (Ti -> To))
    val est = Equation(s, t)
    val Ps = Atom(P, List(s))
    val Pt = Atom (P, List(t))

    val Qss = Atom(Q, List(s,s))
    val Qst = Atom(Q, List(s,t))
    val Qts = Atom(Q, List(t,s))
    val Qtt = Atom(Q, List(t,t))

    val ax1 = Axiom(List(est), List(est))
    val ax2 = Axiom(List(Ps), List(Ps))
    val ax3 = Axiom(List(Pt), List(Pt))
    val ax4 = Axiom(List(Qss), List(Qss))
    val ax5 = Axiom(List(Qtt), List(Qtt))

    val eq = ax1.root.succedent.head

    "work correctly in simple cases" in {
      val seq1 = FSequent(List(est, Pt), List(Ps))
      val seq2 = FSequent(List(est, Ps), List(Pt))

      val subProof1 = WeakeningLeftRule(ax2, est)
      val proof1 = UnaryEquationLeft1Rule(subProof1, subProof1.prin(0), subProof1.root.antecedent(0), HOLPosition(2))

      (proof1.root.toHOLSequent multiSetEquals seq1) must beTrue

      val subProof2 = WeakeningLeftRule(ax3, est)
      val proof2 = UnaryEquationLeft2Rule(subProof2, subProof2.prin(0), subProof2.root.antecedent(0), HOLPosition(2))

      (proof2.root.toHOLSequent multiSetEquals seq2) must beTrue

      val subProof3 = WeakeningLeftRule(ax2, est)
      val proof3 = UnaryEquationRight1Rule(subProof3, subProof3.prin(0), subProof3.root.succedent(0), HOLPosition(2))

      (proof3.root.toHOLSequent multiSetEquals seq2) must beTrue

      val subProof4 = WeakeningLeftRule(ax3, est)
      val proof4 = UnaryEquationRight2Rule(subProof4, subProof4.prin(0), subProof4.root.succedent(0), HOLPosition(2))

      (proof4.root.toHOLSequent multiSetEquals seq1) must beTrue
    }

    "be correctly converted to binary rules" in {
      val subProof1 = WeakeningLeftRule(ax2, est)
      val proof1 = UnaryEquationLeft1Rule(subProof1, subProof1.prin(0), subProof1.root.antecedent(0), HOLPosition(2))

     EquationRuleConverter.toBinary(proof1)

      val subProof2 = WeakeningLeftRule(ax3, est)
      val proof2 = UnaryEquationLeft2Rule(subProof2, subProof2.prin(0), subProof2.root.antecedent(0), HOLPosition(2))

      EquationRuleConverter.toBinary(proof2)

      val subProof3 = WeakeningLeftRule(ax2, est)
      val proof3 = UnaryEquationRight1Rule(subProof3, subProof3.prin(0), subProof3.root.succedent(0), HOLPosition(2))

      EquationRuleConverter.toBinary(proof3)

      val subProof4 = WeakeningLeftRule(ax3, est)
      val proof4 = UnaryEquationRight2Rule(subProof4, subProof4.prin(0), subProof4.root.succedent(0), HOLPosition(2))

      EquationRuleConverter.toBinary(proof4)

      ok
    }
  }
*/

}

