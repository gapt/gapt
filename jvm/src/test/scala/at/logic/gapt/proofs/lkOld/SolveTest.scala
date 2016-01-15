package at.logic.gapt.proofs.lkOld

import at.logic.gapt.examples.BussTautology
import at.logic.gapt.expr._
import at.logic.gapt.expr.StringSymbol
import at.logic.gapt.expr.schema._
import at.logic.gapt.proofs.{ SequentMatchers, Sequent, HOLSequent }
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.lkOld.base._
import at.logic.gapt.proofs.lk.{ BottomAxiom, TopAxiom }
import at.logic.gapt.proofs.occurrences.{ FormulaOccurrence, defaultFormulaOccurrenceFactory }
import org.specs2.mutable._

class SolveTest extends Specification with SequentMatchers {
  implicit val factory = defaultFormulaOccurrenceFactory
  "SolveTest" should {
    "solve the sequents" in {
      skipped( "BigOr, BigAnd in solve needs to be adapted to subsequent invariant" )
      val k = IntVar( "k" )
      val real_n = IntVar( "n" )
      val n = k
      val n1 = Succ( k ); val n2 = Succ( n1 ); val n3 = Succ( n2 )
      val k1 = Succ( k ); val k2 = Succ( n1 ); val k3 = Succ( n2 )
      val s = Set[FormulaOccurrence]()

      val i = IntVar( "i" )
      val A = IndexedPredicate( "A", i )
      val B = IndexedPredicate( "B", i )
      val C = IndexedPredicate( "C", i )
      val zero = IntZero(); val one = Succ( IntZero() ); val two = Succ( Succ( IntZero() ) ); val three = Succ( Succ( Succ( IntZero() ) ) )
      val four = Succ( three ); val five = Succ( four ); val six = Succ( Succ( four ) ); val seven = Succ( Succ( five ) )
      val A0 = IndexedPredicate( "A", IntZero() )
      val A1 = IndexedPredicate( "A", one )
      val A2 = IndexedPredicate( "A", two )
      val A3 = IndexedPredicate( "A", three )

      val B0 = IndexedPredicate( "B", IntZero() )

      val Ak = IndexedPredicate( "A", k )
      val Ai = IndexedPredicate( "A", i )
      val Ai1 = IndexedPredicate( "A", Succ( i ) )
      val orneg = Or( Neg( Ai ).asInstanceOf[SchemaFormula], Ai1.asInstanceOf[SchemaFormula] ).asInstanceOf[SchemaFormula]

      val Ak1 = IndexedPredicate( "A", Succ( k ) )
      val An = IndexedPredicate( "A", k )
      val An1 = IndexedPredicate( "A", n1 )
      val An2 = IndexedPredicate( "A", n2 )
      val An3 = IndexedPredicate( "A", n3 )

      val biga = BigAnd( i, A, zero, one )
      val bigo = BigOr( i, A, zero, one )
      val biga2 = BigAnd( i, A, zero, two )
      val bigo2 = BigOr( i, A, zero, two )

      val fseq = HOLSequent( A0 :: A1 :: Nil, bigo :: Nil )

      val p = solve.solvePropositional( fseq )

      // TODO: something with these...
      solve.solvePropositional( HOLSequent( Neg( And( Neg( A ), Neg( B ) ) ) :: Nil, Or( A, B ) :: Nil ) )
      solve.solvePropositional( HOLSequent( Or( Or( A, B ), C ) :: Nil, A :: B :: C :: Nil ) )
      solve.solvePropositional( HOLSequent( And( A, B ) :: Nil, Neg( Or( Neg( A ), Neg( B ) ) ) :: Nil ) )
      solve.solvePropositional( HOLSequent( A0 :: A1 :: A2 :: Nil, biga2 :: Nil ) )
      solve.solvePropositional( HOLSequent( A :: B :: C :: Nil, And( And( A, B ), C ) :: Nil ) )
      solve.solvePropositional( HOLSequent( bigo2 :: Nil, A0 :: A1 :: A2 :: Nil ) )

      val c2 = Const( new StringSymbol( "c" ), Ti )
      val d2 = Const( new StringSymbol( "d" ), Ti )
      val e2 = Const( new StringSymbol( "e" ), Ti )

      val P = Const( new StringSymbol( "P" ), Ti -> To )

      val Pc2 = HOLAtom( P, c2 :: Nil )
      val Pd2 = HOLAtom( P, d2 :: Nil )
      val Pe2 = HOLAtom( P, e2 :: Nil )
      val andPc2Pd2 = And( Pc2, Pd2 )
      val impPc2Pd2 = Imp( Pc2, Pd2 )
      val imp_andPc2Pd2_Pe2 = Imp( andPc2Pd2, Pe2 )
      val orPc2Pd2 = Or( Pc2, Pd2 )
      val seq11 = HOLSequent( Pc2 :: Nil, Pc2 :: Nil )
      val seq12 = HOLSequent( andPc2Pd2 :: Nil, Pc2 :: Nil )
      val seq13 = HOLSequent( Pc2 :: Nil, orPc2Pd2 :: Nil )
      val seq14 = HOLSequent( andPc2Pd2 :: Nil, orPc2Pd2 :: Nil )
      val seq15 = HOLSequent( Pc2 :: impPc2Pd2 :: imp_andPc2Pd2_Pe2 :: Nil, Pe2 :: Nil )
      val seq16 = HOLSequent( Pc2 :: Nil, Pd2 :: Nil )

      solve.solvePropositional( seq16 ) must beEqualTo( None )
    }

    "prove non-atomic axioms (1)" in {
      import at.logic.gapt.expr.hol._
      val List( x, y, z ) = List( "x", "y", "z" ) map ( x => Var( StringSymbol( x ), Ti ) )
      val List( u, v, w ) = List( "u", "v", "w" ) map ( x => Var( StringSymbol( x ), Ti -> Ti ) )
      val List( a, b, c, zero ) = List( "a", "b", "c", "0" ) map ( x => Const( StringSymbol( x ), Ti ) )
      val List( f, g, h, s ) = List( "f", "g", "h", "s" ) map ( x => Const( StringSymbol( x ), Ti -> Ti ) )
      val List( p, q ) = List( "P", "Q" ) map ( x => Const( StringSymbol( x ), Ti -> Ti ) )
      val List( _Xsym, _Ysym ) = List( "X", "Y" ) map ( x => StringSymbol( x ) )
      val List( _X, _Y ) = List( _Xsym, _Ysym ) map ( x => Var( x, Ti -> To ) )

      val xzero = HOLAtom( _X, List( zero ) )
      val xx = HOLAtom( _X, List( x ) )
      val xsx = HOLAtom( _X, List( HOLFunction( s, List( x ) ) ) )

      val ind = All( _X, Imp( And( xzero, All( x, Imp( xx, xsx ) ) ), All( x, xx ) ) )
      val fs = HOLSequent( ind :: Nil, ind :: Nil )
      val proof = AtomicExpansion( fs )
      //check if the derived end-sequent is correct
      proof.root.toHOLSequent must beMultiSetEqual( fs )

      //check if three different eigenvariables were introduced and nothing more
      /* FIXME: replace toFormula.symbols call with call to getVars from utils
      val psymbols = proof.nodes.flatMap(x => x.asInstanceOf[LKProof].root.toFormula.symbols).filterNot(_.isInstanceOf[LogicalSymbolsA]).toSet
      val fssymbols = fs.formulas.flatMap(_.symbols).filterNot(_.isInstanceOf[LogicalSymbolsA]).toSet
      //println(psymbols)
      (psymbols diff fssymbols).size must_== 3
      (fssymbols diff psymbols) must beEmpty
      */
    }

    "prove non-atomic axioms (2)" in {
      import at.logic.gapt.expr.hol._
      val List( x, y, z ) = List( "x", "y", "z" ) map ( x => Var( StringSymbol( x ), Ti ) )
      val List( u, v, w ) = List( "u", "v", "w" ) map ( x => Var( StringSymbol( x ), Ti -> Ti ) )
      val List( a, b, c, zero ) = List( "a", "b", "c", "0" ) map ( x => Const( StringSymbol( x ), Ti ) )
      val List( f, g, h, s ) = List( "f", "g", "h", "s" ) map ( x => Const( StringSymbol( x ), Ti -> Ti ) )
      val List( psym, qsym ) = List( "P", "Q" ) map ( x => StringSymbol( x ) )
      val List( _Xsym, _Ysym ) = List( "X", "Y" ) map ( x => StringSymbol( x ) )
      val List( _X, _Y ) = List( _Xsym, _Ysym ) map ( x => Var( x, Ti -> To ) )

      val Q = Const( qsym, Ti -> ( Ti -> To ) )
      val P = Const( qsym, Ti -> To )
      val xzero = HOLAtom( Q, List( y, HOLFunction( s, List( x ) ) ) )

      val formula = All( x, Neg( Ex( y, xzero ) ) )
      val fs = HOLSequent( List( HOLAtom( P, x :: Nil ), formula ), List( formula, HOLAtom( P, y :: Nil ) ) )
      val proof = AtomicExpansion( fs )
      //check if the derived end-sequent is correct
      proof.root.toHOLSequent must beMultiSetEqual( fs )

      //check if two different eigenvariables were introduced and nothing more
      /* FIXME: replace toFormula.symbols call with call to getVars from utils
      val psymbols = proof.nodes.flatMap(x => x.asInstanceOf[LKProof].root.toFormula.symbols).filterNot(_.isInstanceOf[LogicalSymbolsA]).toSet
      val fssymbols = fs.formulas.flatMap(_.symbols).filterNot(_.isInstanceOf[LogicalSymbolsA]).toSet
      (psymbols diff fssymbols).size must_== 2
      (fssymbols diff psymbols) must beEmpty */
    }

    // tests of expansionProofToLKProof also in MiscTest, such that it can be used in combination with LKToExpansionProof

    "prove sequent where quantifier order matters" in {
      // example from Chaudhuri et.al.: A multi-focused proof system ...
      val List( x, y, u, v ) = List( "x", "y", "u", "v" ) map ( x => Var( StringSymbol( x ), Ti ) )
      val c = Const( StringSymbol( "c" ), Ti )
      val d = Const( StringSymbol( "d" ), Ti -> To )

      val formula = Ex( x, Or( Neg( HOLAtom( d, x :: Nil ) ), All( y, HOLAtom( d, y :: Nil ) ) ) ) // exists x (-d(x) or forall y d(y))

      val inst1 = ETOr(
        ETNeg( ETAtom( HOLAtom( d, u :: Nil ) ) ), // -d(u)
        ETStrongQuantifier( All( y, HOLAtom( d, y :: Nil ) ), v, ETAtom( HOLAtom( d, v :: Nil ) ) ) // forall y d(y) +^v d(v)
      )

      val inst2 = ETOr(
        ETNeg( ETAtom( HOLAtom( d, c :: Nil ) ) ), // -d(c)
        ETStrongQuantifier( All( y, HOLAtom( d, y :: Nil ) ), u, ETAtom( HOLAtom( d, u :: Nil ) ) ) // forall y d(y) +^u d(u)
      )

      // here, the second tree, containing c, must be expanded before u, as u is used as eigenvar in the c branch
      val et = ETWeakQuantifier.applyWithoutMerge( formula, List( ( inst1, u ), ( inst2, c ) ) )
      val etSeq = new ExpansionSequent( Nil, et :: Nil )

      val lkProof = solve.expansionProofToLKProof( toShallow( etSeq ), etSeq )
      lkProof.isDefined must beTrue
    }

    "prove top" in {
      solve.solvePropositional( HOLSequent( Seq(), Seq( Top() ) ) ) must beSome
    }

    "not prove bottom" in {
      solve.solvePropositional( HOLSequent( Seq(), Seq( Bottom() ) ) ) must beNone
    }

    "not refute top" in {
      solve.solvePropositional( HOLSequent( Seq( Top() ), Seq() ) ) must beNone
    }

    "refute bottom" in {
      solve.solvePropositional( HOLSequent( Seq( Bottom() ), Seq() ) ) must beSome
    }

    "prove ( p ∨ p ) ⊃ ( p ∧ p )" in {
      val p = FOLAtom( "p" ) // TODO: should rather be PropAtom
      val F = Imp( Or( p, p ), And( p, p ) )
      solve.solvePropositional( HOLSequent( Seq(), Seq( F ) ) ) must beSome
    }

    "prove ( p ∧ p ) ⊃ ( p ∨ p )" in {
      val p = FOLAtom( "p" ) // TODO: should rather be PropAtom
      val F = Imp( And( p, p ), Or( p, p ) )
      solve.solvePropositional( HOLSequent( Seq(), Seq( F ) ) ) must beSome
    }

    "prove BussTautology(2)" in {
      solve.solvePropositional( BussTautology( 2 ) ) must beSome
    }
  }

  "ExpansionProofToLK" should {
    "top" in {
      ExpansionProofToLK( Sequent() :+ ETTop ) must_== TopAxiom
    }
    "bottom" in {
      ExpansionProofToLK( ETBottom +: Sequent() ) must_== BottomAxiom
    }
  }
}

