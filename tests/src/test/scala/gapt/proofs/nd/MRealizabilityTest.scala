package gapt.proofs.nd

import gapt.examples.Script
import gapt.expr._
import gapt.formats.babel.{ Notation, Precedence }
import gapt.proofs.context.Context
import gapt.proofs.{ Ant, Checkable }
import gapt.proofs.context.Context.{ InductiveType, PrimRecFun }
import org.specs2.mutable.Specification

class MRealizabilityTest extends Specification {

  "addRecorsors" in {
    "naturalNumbers" in {
      var ctx = Context()

      ctx += InductiveType(
        ty"nat",
        hoc"0 : nat",
        hoc"s : nat > nat" )

      implicit var systemT = MRealizability.systemT( ctx )

      val plusTwo = le"natRec(s(s(0)))(^z1 ^z2 (s(z2)))"

      normalize( plusTwo( le"s(s(s(0)))" ) ) must_== le"s(s(s(s(s(0)))))"
    }
    "pairs+naturalNumbers" in {
      var ctx = Context()

      ctx += InductiveType(
        ty"nat",
        hoc"0 : nat",
        hoc"s : nat > nat" )
      ctx += Notation.Infix( "+", Precedence.plusMinus )
      ctx += PrimRecFun(
        hoc"'+': nat>nat>nat",
        "0 + x = x",
        "s(x) + y = s(x + y)" )( ctx )
      ctx += InductiveType(
        ty"conjj ?c  ?b",
        hoc"pairr{?c ?b}: ?c > ?b > conjj ?c ?b" )

      implicit var systemT = MRealizability.systemT( ctx )

      val sumPair = le"conjjRec (^(x:nat) ^(y:nat) (x + y) )"

      normalize( sumPair( le"pairr(s(0),s(s(0)))" ) ) must_== le"s(s(s(0)))"
    }
    "binaryTrees" in {
      var ctx = Context()

      ctx += InductiveType(
        ty"bitree ?a",
        hoc"leaf{?a}: ?a > bitree ?a",
        hoc"node{?a}: bitree ?a > bitree ?a > bitree ?a" )

      implicit var systemT = MRealizability.systemT( ctx )

      systemT += Definition(
        Const( "mirror", ty"bitree ?a > bitree ?a", List( ty"?a" ) ),
        le"bitreeRec( (^(x:?a)leaf(x)), (^(z1:bitree ?a)^(z2:bitree ?a)^(z3:bitree ?a)^(z4:bitree ?a) node(z4,z2)) )" )

      normalize( le"mirror( node(leaf(x), node(leaf(y), node(leaf(z1), leaf(z2)))) )" ) must_==
        le"node(node(node(leaf(z2), leaf(z1)), leaf(y)), leaf(x))"
    }
    "lists" in {
      var ctx = Context()

      ctx += InductiveType(
        ty"nat",
        hoc"0 : nat",
        hoc"s : nat > nat" )
      ctx += Notation.Infix( "+", Precedence.plusMinus )
      ctx += PrimRecFun(
        hoc"'+': nat>nat>nat",
        "0 + x = x",
        "s(x) + y = s(x + y)" )( ctx )
      ctx += InductiveType(
        ty"list ?a",
        hoc"nil{?a}: list ?a",
        hoc"cons{?a}: ?a > list ?a > list ?a" )

      implicit var systemT = MRealizability.systemT( ctx )

      systemT += Definition(
        Const( "length", ty"list ?a > nat", List( ty"?a" ) ),
        le"listRec(0,^(z1:?a)^(z2: list ?a)^(z3:nat) s(z3))" )

      normalize( le"length( cons(1, cons(2, cons(3,nil))) )" ) must_== le"s(s(s(0)))"

      val sumList = le"listRec(0,(^v ^l ^r v+r))"

      normalize( sumList( le"cons(0, cons(s(0), cons(s(s(0)), nil)))" ) ) must_== le"s(s(s(0)))"
    }
  }

  "empty" in {
    var ctx = Context()
    ctx += InductiveType(
      ty"nat",
      hoc"0 : nat",
      hoc"s : nat > nat" )

    implicit var systemT = MRealizability.systemT( ctx )

    "emptyType" in {
      MRealizability.remEmpProgType( ty"1" ) must_== ty"1"
      MRealizability.remEmpProgType( ty"nat > nat" ) must_== ty"nat > nat"
      MRealizability.remEmpProgType( ty"1 > nat" ) must_== ty"nat"
      MRealizability.remEmpProgType( ty"(nat > nat) > 1" ) must_== ty"1"
      MRealizability.remEmpProgType( TBase( "conj", List( ty"1 > nat", ty"1" ) ) ) must_== ty"nat"
    }
    "emptyTerm" in {
      MRealizability.remEmpProg( le"x:nat>1" ) must_== le"i"
      MRealizability.remEmpProg( le"inl(x:nat>1)" ) must_== le"inl(i)"
      MRealizability.remEmpProg( le"natRec(i, (^x^y y), s(0))" ) must_== le"i"
      MRealizability.remEmpProg( le"natRec(0, (^x^y y), s(0))" ) must_== le"natRec(0, (^x^y y), s(0))"
      MRealizability.remEmpProg( le"natRec(pair(0,i), (^x^y y), s(0))" ) must_== le"natRec(0, (^x^y y), s(0))"
      MRealizability.remEmpProg( le"natRec(inr(i), (^x^y y), s(0))" ) must_== le"natRec(inr(i), (^x^y y), s(0))"
    }
  }

  "mrealizers" in {

    implicit var ctx = Context()

    ctx += InductiveType(
      ty"nat",
      hoc"0 : nat",
      hoc"s : nat > nat" )
    ctx += Notation.Infix( "+", Precedence.plusMinus )
    ctx += PrimRecFun(
      hoc"'+': nat>nat>nat",
      "0 + x = x",
      "s(x) + y = s(x + y)" )( ctx )
    ctx += InductiveType(
      ty"list ?a",
      hoc"nil{?a}: list ?a",
      hoc"cons{?a}: ?a > list ?a > list ?a" )
    ctx += PrimRecFun(
      hoc"app{?a}: list ?a > list ?a > list ?a",
      "app(nil{?a},x) = x",
      "app(cons{?a}(x,y),z) = cons{?a}(x,app(y,z))" )
    ctx += PrimRecFun(
      hoc"sumList: list nat > nat",
      "sumList(nil) = 0",
      "sumList(cons(x,xs)) = x + (sumList(xs))" )
    ctx += InductiveType(
      ty"bitree ?a",
      hoc"leaf{?a}: ?a > bitree ?a",
      hoc"node{?a}: bitree ?a > bitree ?a > bitree ?a" )

    def mrealizer( proof: NDProof ) = MRealizability.mrealize( proof, false )( ctx )._2

    val one = TBase( "1" )
    val i = Const( "i", one )

    def conj( left: Ty, right: Ty ) = TBase( "conj", left, right )
    def pair( left: Ty, right: Ty ) = Const( "pair", left ->: right ->: conj( left, right ), List( left, right ) )
    def pi1( left: Ty, right: Ty ) = Const( "pi1", conj( left, right ) ->: right, List( left, right ) )
    def pi2( left: Ty, right: Ty ) = Const( "pi2", conj( left, right ) ->: left, List( left, right ) )

    def sum( left: Ty, right: Ty ) = TBase( "sum", List( left, right ) )
    def inl( left: Ty, right: Ty ) = Const( "inl", left ->: sum( left, right ), List( left, right ) )
    def inr( left: Ty, right: Ty ) = Const( "inr", right ->: sum( left, right ), List( left, right ) )
    def matchSum( left: Ty, right: Ty, result: Ty ) =
      Const( "matchSum", sum( left, right ) ->: ( left ->: result ) ->: ( right ->: result ) ->: result, List( left, right, result ) )

    val nat = TBase { "nat" }
    val zero = Const( "0", nat )
    val suc = Const( "s", nat ->: nat )
    def natRec( resultType: Ty ) =
      Const( "natRec", resultType ->: ( nat ->: resultType ->: resultType ) ->: nat ->: resultType, List( resultType ) )

    def list( ty: Ty ) = TBase( "list", ty )
    def nil( ty: Ty ) = Const( "nil", list( ty ), List( ty ) )
    def cons( ty: Ty ) = Const( "cons", ty ->: list( ty ), List( ty ) )
    val sumList = Const( "sumList", list( nat ) ->: nat )

    def listRec( listType: Ty, resultType: Ty ) =
      Const( "listRec", resultType ->: ( listType ->: list( listType ) ->: resultType ->: resultType ) ->: list( listType ) ->: resultType, List( listType, resultType ) )

    def bitree( ty: Ty ) = TBase( "bitree", ty )
    def leaf( ty: Ty ) = Const( "leaf", ty ->: bitree( ty ), List( ty ) )
    def node( ty: Ty ) = Const( "node", bitree( ty ) ->: bitree( ty ) ->: bitree( ty ), List( ty ) )
    def bitreeRec( bitreeType: Ty, resultType: Ty ) =
      Const( "bitreeRec", ( bitreeType ->: resultType ) ->: ( bitree( bitreeType ) ->: resultType ->: bitree( bitreeType ) ->: resultType ->: resultType ) ->: bitree( bitreeType ) ->: resultType, List( bitreeType, resultType ) )

    "logicalaxiom" in {
      val p1 = LogicalAxiom( hof"(x:nat) = y" )
      mrealizer( p1 ) must_== Var( "y_0", one )

      val p2 = LogicalAxiom( hof"x = 0 & y = 0" )
      mrealizer( p2 ) must_== Var( "y_0", conj( one, one ) )

      val p3 = LogicalAxiom( hof" 0 + 0 = 0" )
      mrealizer( p3 ) must_== Var( "y", one )

      val p4 = LogicalAxiom( hof"!x ?y x + y = s(x)" )
      mrealizer( p4 ) must_== Var( "y", nat ->: conj( nat, one ) )
    }
    "equalityintro" in {
      val p1 = EqualityIntroRule( le"s(s(s(0)))" )
      mrealizer( p1 ) must_== i

      val p2 = EqualityIntroRule( le"x + s(y + z)" )
      mrealizer( p2 ) must_== i
    }
    "weakening" in {
      val p1 = EqualityIntroRule( le"s(s(y))" )
      val p2 = WeakeningRule( p1, hof"!x x = x + (0 + s(z))" )
      mrealizer( p2 ) must_== i

      val p11 = LogicalAxiom( hof"s(x) = s(s(y))" )
      val p22 = WeakeningRule( p11, hof"!x x = x + (0 + s(z))" )
      mrealizer( p22 ) must_== Var( "y_1", one )

      val p111 = LogicalAxiom( hof"(x : nat) = y" )
      val p222 = WeakeningRule( p111, hof"!(x:nat) x = z" )
      val p333 = WeakeningRule( p222, hof"?(x : nat) x = y" )
      mrealizer( p333 ) must_== Var( "y_2", one )
    }
    "contraction" in {
      val p1 = LogicalAxiom( hof"x = 0" )
      val p2 = WeakeningRule( p1, hof"(x:nat) = z" )
      val p3 = WeakeningRule( p2, hof"(x:nat) = y" )
      val p4 = WeakeningRule( p3, hof"(x:nat) = y" )
      mrealizer( p4 ) must_== Var( "y_3", one )

      val p5 = ContractionRule( p4, hof"(x:nat) = y" )
      mrealizer( p5 ) must_== Var( "y_2", one )

      val p55 = ContractionRule( p4, Ant( 1 ), Ant( 0 ) )
      mrealizer( p55 ) must_== Var( "y_2", one )

      val p6 = WeakeningRule( p5, hof"0 = 0" )
      mrealizer( p6 ) must_== Var( "y_3", one )
    }
    "contraction2" in {
      val p1 = LogicalAxiom( hof"0=0" )
      val p2 = LogicalAxiom( hof"0=0" )
      val p3 = AndIntroRule( p1, p2 )
      val p4 = ContractionRule( p3, hof"0=0" )
      mrealizer( p4 ) must_== pair( one, one )( Var( "y", one ), Var( "y", one ) )
    }
    "andelim1" in {
      val p1 = LogicalAxiom( hof"0 = 0 & s(0) = s(0)" )
      val p2 = AndElim1Rule( p1 )
      mrealizer( p2 ) must_== pi1( one, one )( Var( "y", conj( one, one ) ) )
    }
    "andelim2" in {
      val p1 = LogicalAxiom( hof"x = 0 & y = 0" )
      val p2 = AndElim2Rule( p1 )
      mrealizer( p2 ) must_== pi2( one, one )( Var( "y_0", conj( one, one ) ) )
    }
    "andintro" in {
      val p1 = LogicalAxiom( hof"x = 0" )
      val p2 = LogicalAxiom( hof"s(0) = s(0)" )
      val p3 = AndIntroRule( p1, p2 )
      val p4 = AndElim1Rule( p3 )
      mrealizer( p4 ) must_== pi1( one, one )( pair( one, one )( Var( "y", one ), Var( "y_0", one ) ) )
    }
    "impintro" in {
      val p1 = LogicalAxiom( hof"s(0) = s(0) -> 0 = 0" )
      val p2 = LogicalAxiom( hof"s(0) = s(0)" )
      val p3 = ImpElimRule( p1, p2 )
      mrealizer( p3 ) must_== Var( "y", one ->: one )( Var( "y_0", one ) )
    }
    "impelim" in {
      val p1 = LogicalAxiom( hof"0 = 0" )
      val p2 = WeakeningRule( p1, hof"s(0) = s(0)" )
      val p3 = ImpIntroRule( p2, Ant( 0 ) )
      mrealizer( p3 ) must_== Abs( Var( "y_0", one ), Var( "y", one ) )

      val p4 = ImpIntroRule( p3 )
      mrealizer( p4 ) must_== Abs( Var( "y", one ), Abs( Var( "y_0", one ), Var( "y", one ) ) )
    }
    "forallintro" in {
      val p1 = EqualityIntroRule( le"x + s(y)" )
      val p2 = ForallIntroRule( p1, hov"x:nat", hov"z:nat" )
      mrealizer( p2 ) must_== Abs( Var( "x", nat ), i )

      val p3 = ForallIntroRule( p2, hov"y:nat", hov"y:nat" )
      mrealizer( p3 ) must_== Abs( Var( "y", nat ), Abs( Var( "x", nat ), i ) )
    }
    "existselim" in {
      val p1 = LogicalAxiom( hof"?x (x = 0)" )
      val p2 = EqualityIntroRule( le"0" )
      val p3 = WeakeningRule( p2, hof"y = 0" )
      val p4 = ExistsElimRule( p1, p3, hov"y:nat" )
      mrealizer( p4 ) must_== i
    }
    "equalityelim" in {
      val p1 = LogicalAxiom( hof"(x2:nat) = x3" )
      val p2 = LogicalAxiom( hof"!(x0:nat) !(x1:nat) s(x2) = x2 + s(0)" )
      val p3 = EqualityElimRule( p1, p2 )
      mrealizer( p3 ) must_== Var( "y_0", nat ->: nat ->: one )

      val p11 = LogicalAxiom( hof"s(0) = 0 + s(0)" )
      val p22 = LogicalAxiom( hof"s(x) = x + s(0)" )
      val p33 = LogicalAxiom( hof"!z s(x) = z" )
      val p44 = EqualityElimRule( p22, p33 )
      val p55 = EqualityElimRule( p11, p44 )
      mrealizer( p55 ) must_== Var( "y_1", nat ->: one )
    }
    "forallelim" in {
      val p1 = LogicalAxiom( hof"!x ?y x = s(y)" )
      val p2 = ForallElimRule( p1, le"s(s(0))" )
      mrealizer( p2 ) must_== Var( "y", nat ->: conj( nat, one ) )( suc( suc( zero ) ) )
    }
    "existsintro" in {
      val p1 = EqualityIntroRule( le"s(s(x))" )
      val p2 = ExistsIntroRule( p1, hof"y = s(s(x))", le"s(s(x))", hov"y:nat" )
      mrealizer( p2 ) must_== pair( nat, one )( suc( suc( Var( "x", nat ) ) ), i )
    }
    "botelim" in {
      val p1 = LogicalAxiom( hof"⊥" )
      val p2 = WeakeningRule( p1, hof"!x ?y y = s(x)" )
      val p3 = BottomElimRule( p2, hof"!x ?y x = s(y)" )
      mrealizer( p3 ) must_== Var( "y_1", nat ->: conj( nat, one ) )
    }
    "topintro" in {
      val p1 = TopIntroRule
      mrealizer( p1 ) must_== Abs( Var( "y", one ), Var( "y", one ) )
    }
    "negelim" in {
      val p1 = LogicalAxiom( hof"¬ 0=0" )
      val p2 = LogicalAxiom( hof"0=0" )
      val p3 = NegElimRule( p1, p2 )
      mrealizer( p3 ) must_== Var( "y", one ->: one )( Var( "y_0", one ) )
    }
    "negintro" in {
      val p1 = LogicalAxiom( hof"¬ 0=0" )
      val p2 = LogicalAxiom( hof"0=0" )
      val p3 = NegElimRule( p1, p2 )
      val p4 = NegIntroRule( p3, Ant( 0 ) )
      mrealizer( p4 ) must_== Abs( Var( "y_0", one ->: one ), Var( "y_0", one ->: one )( Var( "y", one ) ) )
    }
    "orintro1" in {
      val p1 = EqualityIntroRule( le"0" )
      val p2 = OrIntro1Rule( p1, hof"s(0) = 0" )
      mrealizer( p2 ) must_== inl( one, one )( i )
    }
    "orintro2" in {
      val p1 = EqualityIntroRule( le"0" )
      val p2 = OrIntro2Rule( p1, hof"s(0) = 0" )
      mrealizer( p2 ) must_== inr( one, one )( i )
    }
    "orelim" in {
      val p1 = LogicalAxiom( hof"x = 0 & x = s(0)" )
      val p2 = AndElim1Rule( p1 )
      val p3 = LogicalAxiom( hof"x = 0 & x = s(s(0))" )
      val p4 = AndElim1Rule( p3 )
      val p5 = LogicalAxiom( hof"(x = 0 & x = s(0)) | (x = 0 & x = s(s(0)))" )
      val p6 = OrElimRule( p5, p2, p4 )
      mrealizer( p6 ) must_== matchSum( conj( one, one ), conj( one, one ), one )(
        Var( "y", sum( conj( one, one ), conj( one, one ) ) ),
        Abs( Var( "y_0", conj( one, one ) ), pi1( one, one )( Var( "y_0", conj( one, one ) ) ) ),
        Abs( Var( "y_1", conj( one, one ) ), pi1( one, one )( Var( "y_1", conj( one, one ) ) ) ) )
    }
    "theoryaxiom" in {
      val p1 = TheoryAxiom( hof"y + 0 = 0" )
      mrealizer( p1 ) must_== Var( s"mrealizer(${hof"y + 0 = 0"})", one )

      val p2 = TheoryAxiom( hof"¬ s(z) = 0" )
      mrealizer( p2 ) must_== Var( s"mrealizer(${hof"¬ s(z) = 0"})", one ->: one )
    }
    "excludedmiddle" in {
      val p1 = LogicalAxiom( hof"0=0" )
      val p2 = LogicalAxiom( hof"¬0=0" )
      val p3 = OrIntro1Rule( p1, hof"¬0=0" )
      val p4 = OrIntro2Rule( p2, hof"0=0" )
      val p5 = ExcludedMiddleRule( p3, Ant( 0 ), p4, Ant( 0 ) )
      mrealizer( p5 ) must_== matchSum( one, one ->: one, sum( one, one ->: one ) )(
        Var( s"mrealizer(${hof"0 = 0 ∨ ¬0 = 0"})", sum( one, one ->: one ) ),
        Abs( Var( "y", one ), inl( one, one ->: one )( Var( "y", one ) ) ),
        Abs( Var( "y_0", one ->: one ), inr( one, one ->: one )( Var( "y_0", one ->: one ) ) ) )

      val a1 = LogicalAxiom( hof"¬ ¬0=0" )
      val a2 = LogicalAxiom( hof"¬0=0" )
      val a3 = NegElimRule( a1, a2 )
      val a4 = BottomElimRule( a3, hof"0=0" )
      val b1 = LogicalAxiom( hof"0=0" )
      val c1 = LogicalAxiom( hof"0=0" )
      val c2 = LogicalAxiom( hof"¬0=0" )
      val c3 = OrIntro1Rule( c1, hof"¬0=0" )
      val c4 = OrIntro2Rule( c2, hof"0=0" )
      val c5 = ExcludedMiddleRule( c3, Ant( 0 ), c4, Ant( 0 ) )
      val a5 = OrElimRule( c5, b1, a4 )
      val a6 = ImpIntroRule( a5 )
      mrealizer( a6 ) must_== Abs(
        Var( "y", ( one ->: one ) ->: one ),
        matchSum( one, one ->: one, one )(
          matchSum( one, one ->: one, sum( one, one ->: one ) )(
            Var( s"mrealizer(${hof"0 = 0 ∨ ¬0 = 0"})", sum( one, one ->: one ) ),
            Abs( Var( "y", one ), inl( one, one ->: one )( Var( "y", one ) ) ),
            Abs( Var( "y_0", one ->: one ), inr( one, one ->: one )( Var( "y_0", one ->: one ) ) ) ),
          Abs( Var( "y_0", one ), Var( "y_0", one ) ),
          Abs( Var( "y_1", one ->: one ), Var( "y_4", one ) ) ) )
    }
    "ind-nat" in {
      val s0 = LogicalAxiom( hof"!x x + 0 = x" )
      val s01 = ForallElimRule( s0, le"0" )
      val s1 = LogicalAxiom( hof"!x !y s(x) + y = s(x + y)" )
      val s2 = ForallElimRule( s1, le"x0: nat" )
      val s3 = ForallElimRule( s2, le"0" )
      val s4 = LogicalAxiom( hof"x0 + 0 = x0" )
      val s5 = EqualityElimRule( s4, s3, hof"s(x0) + 0 = s(z)", hov"z: nat" )
      val cases = Seq(
        InductionCase( s01, hoc"0", Seq.empty, Seq.empty ),
        InductionCase( s5, hoc"s", Seq( Ant( 0 ) ), Seq( hov"x0: nat" ) ) )
      val p = InductionRule( cases, Abs( Var( "x", TBase( "nat" ) ), hof"x + 0 = x" ), le"x : nat" )
      mrealizer( p ) must_== natRec( one )(
        Var( "y", nat ->: one )( zero ),
        Abs( Var( "x0", nat ), Abs( Var( "y_1", one ), Var( "y_0", nat ->: nat ->: one )( Var( "x0", nat ), zero ) ) ),
        Var( "x", nat ) )

      val a1 = LogicalAxiom( hof"P(0)" )
      val b1 = LogicalAxiom( hof"!x (P(x) -> P(s(x)))" )
      val b2 = ForallElimRule( b1, le"x:nat" )
      val b3 = LogicalAxiom( hof"P(x:nat)" )
      val b4 = ImpElimRule( b2, b3 )
      val casess = Seq(
        InductionCase( a1, hoc"0", Seq(), Seq() ),
        InductionCase( b4, hoc"s", Seq( Ant( 1 ) ), Seq( hov"x:nat" ) ) )
      val c3 = InductionRule( casess, Abs( hov"x:nat", hof"P(x:nat)" ), le"x:nat" )
      val d1 = ForallIntroRule( c3, hov"x:nat", hov"x:nat" )
      val d2 = ImpIntroRule( d1, Ant( 0 ) )
      val d3 = ImpIntroRule( d2 )
      mrealizer( d3 ) must_== Abs( Var( "y", nat ->: one ->: one ), Abs( Var( "y_0", one ), Abs( Var( "x", nat ), natRec( one )(
        Var( "y_0", one ),
        Abs( Var( "x", nat ), Abs( Var( "y_1", one ), Var( "y", nat ->: one ->: one )( Var( "x", nat ), Var( "y_1", one ) ) ) ),
        Var( "x", nat ) ) ) ) )
    }
    "ind-list" in {
      val s0 = LogicalAxiom( hof"!x app(x,nil) = x" )
      val s01 = ForallElimRule( s0, le"nil" )
      val s1 = LogicalAxiom( hof"!a !x !y app(cons(a,x),y) = cons(a,app(x,y))" )
      val s11 = ForallElimRule( s1, le"a" )
      val s2 = ForallElimRule( s11, le"x0 : list ?a" )
      val s3 = ForallElimRule( s2, le"nil" )
      val s4 = LogicalAxiom( hof"app(x0,nil) = x0" )
      val s5 = EqualityElimRule( s4, s3, hof"app(cons(a, x0),nil) = cons(a, z)", hov"z: list ?a" )
      val cases = Seq(
        InductionCase( s01, hoc"nil", Seq.empty, Seq.empty ),
        InductionCase( s5, hoc"cons", Seq( Ant( 0 ) ), Seq( hov"a : ?a", hov"x0: list ?a" ) ) )
      val p = InductionRule( cases, Abs( Var( "x", ty"list ?a" ), hof"app(x,nil) = x" ), le"x : list ?a" )

      val y = Var( "y", list( TVar( "a" ) ) ->: one )
      val a = Var( "a", TVar( "a" ) )
      val x0 = Var( "x0", list( TVar( "a" ) ) )
      val y1 = Var( "y_1", one )
      val y0 = Var( "y_0", TVar( "a" ) ->: list( TVar( "a" ) ) ->: list( TVar( "a" ) ) ->: one )
      val x = Var( "x", list( TVar( "a" ) ) )

      mrealizer( p ) must_== listRec( TVar( "a" ), one )( y( nil( TVar( "a" ) ) ), Abs( Seq( a, x0, y1 ), y0( a, x0, nil( TVar( "a" ) ) ) ), x )
    }
    "ind-bitree" in {
      val a1 = LogicalAxiom( hof"!a P(leaf{?a}(a))" )
      val a11 = ForallElimRule( a1, le"a:?a" )
      val b1 = LogicalAxiom( hof"!x !y (P(x) -> (P(y) -> P(node{?a}(x,y))))" )
      val b2 = ForallElimRule( b1, le"x:bitree ?a" )
      val b22 = ForallElimRule( b2, le"y:bitree ?a" )
      val b3 = LogicalAxiom( hof"P(x:bitree ?a)" )
      val b33 = LogicalAxiom( hof"P(y:bitree ?a)" )
      val b4 = ImpElimRule( b22, b3 )
      val b44 = ImpElimRule( b4, b33 )
      val casess = Seq(
        InductionCase( a11, hoc"leaf{?a}", Seq(), Seq( hov"a:?a" ) ),
        InductionCase( b44, hoc"node{?a}", Seq( Ant( 1 ), Ant( 2 ) ), Seq( hov"x:bitree ?a", hov"y:bitree ?a" ) ) )
      val c3 = InductionRule( casess, Abs( hov"x:bitree ?a", hof"P(x:bitree ?a)" ), le"x:bitree ?a" )
      val d1 = ForallIntroRule( c3, hov"x:bitree ?a", hov"x:bitree ?a" )
      val d2 = ImpIntroRule( d1, Ant( 0 ) )
      val d3 = ImpIntroRule( d2 )

      val y = Var( "y", bitree( TVar( "a" ) ) ->: bitree( TVar( "a" ) ) ->: one ->: one ->: one )
      val y_0 = Var( "y_0", TVar( "a" ) ->: one )
      val x = Var( "x", bitree( TVar( "a" ) ) )
      val a = Var( "a", TVar( "a" ) )
      val y_1 = Var( "y_1", one )
      val xy = Var( "y", bitree( TVar( "a" ) ) )
      val y_2 = Var( "y_2", one )

      mrealizer( d3 ) must_== Abs( Seq( y, y_0, x ), bitreeRec( TVar( "a" ), one )(
        Abs( a, y_0( a ) ),
        Abs( Seq( x, y_1, xy, y_2 ), y( x, xy, y_1, y_2 ) ),
        x ) )
    }
    "sucfunction" in {
      val p1 = EqualityIntroRule( le"s(x)" )
      val p2 = DefinitionRule( p1, hof"s(x) = s(0) + x" )
      Checkable.requireDefEq( p1.conclusion.succedent( 0 ), p2.conclusion.succedent( 0 ) )
      val p3 = ExistsIntroRule( p2, hof"y = s(0) + x", le"s(x)", hov"y:nat" )
      val p4 = ForallIntroRule( p3, hov"x:nat", hov"x:nat" )
      mrealizer( p4 ) must_== Abs( Var( "x", nat ), pair( nat, one )( suc( Var( "x", nat ) ), i ) )
    }
    "sumlistfunction" in {
      val p1 = EqualityIntroRule( le"sumList(x)" )
      val p2 = ExistsIntroRule( p1, hof"y = sumList(x)", le"sumList(x)", hov"y:nat" )
      val p3 = ForallIntroRule( p2, hov"x : list nat", hov"x : list nat" )
      mrealizer( p3 ) must_== Abs( Var( "x", list( nat ) ), pair( nat, one )( sumList( Var( "x", list( nat ) ) ), i ) )
    }
  }

}