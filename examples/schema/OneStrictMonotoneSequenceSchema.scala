package gapt.examples

import gapt.expr._
import gapt.proofs.Context._
import gapt.proofs.Context
import gapt.proofs.Sequent
import gapt.proofs.gaptic._

object OneStrictMonotoneSequenceSchema extends TacticsProof {
  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Context.Sort( "i" )
  ctx += hoc"f:i>nat"
  ctx += hoc"suc:i>i"
  ctx += hoc"z:i"
  ctx += hoc"E: nat>nat>o"
  ctx += hoc"LE: nat>nat>o"
  ctx += hoc"Top: nat>nat"

  ctx += hoc"omega: nat>nat>nat"
  ctx += hoc"nu: nat>nat>i>nat"
  ctx += hoc"mu: nat>nat>i>nat"
  ctx += hoc"theta: nat>nat>i>nat"
  ctx += hoc"chi: nat>i>nat"
  ctx += hoc"epsilon: nat>nat>nat>i>nat"
  ctx += hoc"delta: nat>nat>i>nat"

  ctx += hoc"phi: nat>nat>nat"
  ctx += PrimRecFun( hoc"POR:nat>i>o", "POR 0 x = E 0 (f x) ", "POR (s y) x = (E (s y) (f x) ∨ POR y x)" )
  ctx += PrimRecFun( hoc"iNum:nat>i>i", "iNum 0 x = x ", "iNum (s y) x = (suc (iNum y x))" )
  ctx += PrimRecFun( hoc"CSeq:nat>nat>i>o", "CSeq 0 n x = (E n (f (iNum 0 x)))", "CSeq (s y) n x = ((E n (f (iNum (s y) x) ) ) ∧ (CSeq y n x))" )
  ctx += PrimRecFun( hoc"EndSeq:nat>i>o", "EndSeq 0 x = (E (f x) (f x))", "EndSeq (s y) x = ((E (f x ) (f (iNum (s y) x) )) ∧ (EndSeq y x))" )
  // Correct axiom
  // ctx += "LEDefinition" -> hos"POR(n,iNum(m,a)) :- LE(f(a), s(n))"
  //Incorrect axiom which is inconsistent outside this proof
  ctx += "LEDefinitionSingle" -> hos" E(n,f(iNum(m,a))) :- LE(f(a), k)"
  ctx += "NumericTransitivity" -> hos"E(n,f(a)),E(n,f(suc(a))) :- E(f(a), f(suc(a)))"
  ctx += "NumericTransitivityBase" -> hos"E(n,f(a)) :- E(f(a), f(a))"
  ctx += "NumericTransitivityStep" -> hos"E(n,f(iNum(s(k),a))), E(n,f(iNum(k,a))), E(f(a), f(iNum(k,a))) :- E(f(a), f(iNum(s(k),a)))"
  ctx += "minimalElement" -> hos"LE(f(z),0) :- "
  ctx += "ordcon" -> hos"LE(f(iNum(m,a)),s(n)) :- E(n,f(iNum(m,a))), LE(f(a),n)"
  val repeating = le"(s (s 0))"
  val esTop = Sequent(
    Seq( hof"!x POR(n,x)" ),
    Seq( hof"?x ( EndSeq($repeating,x) )" ) )
  ctx += Context.ProofNameDeclaration( le"Top n", esTop )
  val esOmega = Sequent(
    Seq( hof"!x POR(n,x)" ),
    Seq( hof"?x ( EndSeq(k,x) )" ) )
  ctx += Context.ProofNameDeclaration( le"omega n k", esOmega )
  val esPhi = Sequent(
    Seq( hof"?x(CSeq(k,n,x)) | !y (LE(f(y),n))" ),
    Seq( hof"?x (EndSeq(k,x) )" ) )
  ctx += Context.ProofNameDeclaration( le"phi n k", esPhi )
  val esMu = Sequent(
    Seq( hof"CSeq(k,n,a) " ),
    Seq( hof"EndSeq(k,a) " ) )
  ctx += Context.ProofNameDeclaration( le"mu k n a", esMu )
  val esNu = Sequent(
    Seq( hof"!x POR(n,x)" ),
    Seq( hof"CSeq(k,n,a)", hof"LE(f(a),n)" ) )
  ctx += Context.ProofNameDeclaration( le"nu k n a", esNu )
  val esTheta = Sequent(
    Seq( hof"!x LE(f(x),s(n))" ),
    Seq( hof"LE(f(a),n)", hof"CSeq(k,n,a)" ) )
  ctx += Context.ProofNameDeclaration( le"theta k n a", esTheta )

  val eschi = Sequent(
    Seq( hof" POR(n,a) " ),
    Seq( hof"POR(n,a)" ) )
  ctx += Context.ProofNameDeclaration( le"chi n a", eschi )
  val esEpsilon = Sequent(
    Seq( hof" POR(n,iNum(m,a)) " ),
    Seq( hof" LE(f(a), k)" ) )
  ctx += Context.ProofNameDeclaration( le"epsilon n m k a", esEpsilon )
  val esDelta = Sequent(
    Seq(
      hof" E(n, f(iNum(s(k), a)))",
      hof"CSeq(k, n, a)" ),
    Seq( hof"E(f(a), f(iNum(s(k), a)))" ) )
  ctx += Context.ProofNameDeclaration( le"delta k n a", esDelta )

  //The base case of  Top
  val esTopBc =
    Sequent(
      Seq( "Ant_0" -> hof"!x POR(0,x)" ),
      Seq( "Suc_0" -> hof"?x (EndSeq($repeating ,x))" ) )
  val TopBc = Lemma( esTopBc ) {
    ref( "omega" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"Top 0", TopBc )
  val esTopSc =
    Sequent(
      Seq( "Ant_0" -> hof"!x POR(s(n),x)" ),
      Seq( "Suc_0" -> hof"?x (EndSeq($repeating ,x))" ) )
  val TopSc = Lemma( esTopSc ) {
    ref( "omega" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"Top (s n)", TopSc )

  //The base case of  omega
  val esOmegaBc =
    Sequent(
      Seq( "Ant_0" -> hof"!x POR(0,x)" ),
      Seq( "Suc_0" -> hof"?x (EndSeq(k,x))" ) )
  val omegaBc = Lemma( esOmegaBc ) {
    cut( "cut", hof"?x (CSeq(k,0,x)) | !y (LE(f(y),0))" )
    orR
    allR( "cut_1", fov"a" )
    exR( "cut_0", fov"a" )
    ref( "nu" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega 0 k", omegaBc )
  val esOmegaSc =
    Sequent(
      Seq( "Ant_0" -> hof"!x POR(s(n),x)" ),
      Seq( "Suc_0" -> hof"?x (EndSeq(k,x))" ) )
  val omegaSc = Lemma( esOmegaSc ) {
    cut( "cut", hof"?x (CSeq(k,s(n),x)) | !y (LE(f(y),s(n)))" )
    orR
    allR( "cut_1", fov"a" )
    exR( "cut_0", fov"a" )
    ref( "nu" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega (s n) k", omegaSc )

  val esPhiBc1 =
    Sequent(
      Seq( "Ant_0" -> hof"?x (CSeq(0,0,x)) | !y (LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x (EndSeq(0,x) )" ) )
  val phiBc1 = Lemma( esPhiBc1 ) {
    orL
    exL( fov"a" )
    exR( fov"a" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    unfold( "iNum" ) atMost 1 in "Ant_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    ref( "NumericTransitivityBase" )
    allL( foc"z" )
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0 0", phiBc1 )

  val esPhiBc2 =
    Sequent(
      Seq( "Ant_0" -> hof"?x (CSeq(s(k),0,x)) | !y (LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x (EndSeq(s(k),x) )" ) )
  val phiBc2 = Lemma( esPhiBc2 ) {
    orL
    exL( fov"a" )
    exR( fov"a" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    andL
    andR
    ref( "delta" )
    ref( "mu" )
    allL( foc"z" )
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0 (s k)", phiBc2 )

  val esPhiSc1 =
    Sequent(
      Seq( "Ant_0" -> hof"?x (CSeq(0,s(n),x)) | !y (LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x (EndSeq(0,x) )" ) )
  val phiSc1 = Lemma( esPhiSc1 ) {
    cut( "cut", hof"?x(CSeq(0,n,x)) | !y (LE(f(y),n))" )
    orR
    orL
    exL( "Ant_0", fov"a" )
    exR( "Suc_0", fov"a" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    unfold( "iNum" ) atMost 1 in "Ant_0"
    ref( "NumericTransitivityBase" )
    allR( fov"b" )
    exR( "cut_0", fov"b" )
    allL( le"(iNum 0 b)" )
    unfold( "CSeq" ) atMost 1 in "cut_0_0"
    ref( "ordcon" )

    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n) 0", phiSc1 )

  val esPhiSc2 =
    Sequent(
      Seq( "Ant_0" -> hof"?x (CSeq(s(k),s(n),x)) | !y (LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x (EndSeq(s(k),x) )" ) )
  val phiSc2 = Lemma( esPhiSc2 ) {
    cut( "cut", hof"?x(CSeq(s(k),n,x)) | !y (LE(f(y),n))" )
    orR
    orL
    exL( "Ant_0", fov"a" )
    exR( "Suc_0", fov"a" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    andL
    andR
    ref( "delta" )
    ref( "mu" )
    allR( fov"b" )
    exR( "cut_0", fov"b" )
    allL( le"(iNum (s k) b)" )
    unfold( "CSeq" ) atMost 1 in "cut_0_0"
    andR
    ref( "ordcon" )
    ref( "theta" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n) (s k)", phiSc2 )

  val esmuBc =
    Sequent(
      Seq( "Ant_0" -> hof"CSeq(0,n,a)" ),
      Seq( "Suc_0" -> hof"EndSeq(0,a)" ) )
  val muBc = Lemma( esmuBc ) {
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0"
    unfold( "iNum" ) atMost 1 in "Suc_0"
    unfold( "iNum" ) atMost 1 in "Ant_0"
    ref( "NumericTransitivityBase" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"mu 0 n a", muBc )

  val esmuSc =
    Sequent(
      Seq( "Ant_0" -> hof"CSeq(s(k),n,a)" ),
      Seq( "Suc_0" -> hof"EndSeq(s(k),a)" ) )
  val muSc = Lemma( esmuSc ) {
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0"
    andL
    andR
    ref( "delta" )
    ref( "mu" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"mu (s k) n a", muSc )

  val esThetaBc =
    Sequent(
      Seq( "Ant_0" -> hof"!x LE(f(x),s(n))" ),
      Seq(
        "Suc_0" -> hof"CSeq(0,n,a)",
        "Suc_1" -> hof"LE(f(a),n)" ) )
  val thetaBc = Lemma( esThetaBc ) {
    unfold( "CSeq" ) atMost 1 in "Suc_0"
    allL( le"(iNum 0 a)" )
    ref( "ordcon" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"theta 0 n a", thetaBc )

  val esThetaSc =
    Sequent(
      Seq( "Ant_0" -> hof"!x LE(f(x),s(n))" ),
      Seq(
        "Suc_0" -> hof"CSeq(s(k),n,a)",
        "Suc_1" -> hof"LE(f(a),n)" ) )
  val thetaSc = Lemma( esThetaSc ) {
    unfold( "CSeq" ) atMost 1 in "Suc_0"
    andR
    allL( le"(iNum (s k) a)" )
    ref( "ordcon" )
    ref( "theta" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"theta (s k) n a", thetaSc )
  // The Basecase of chi
  val esChiBc = Sequent(
    Seq(
      "Ant_2" -> hof" POR(0,a)" ),
    Seq(
      "Suc_0" -> hof"POR(0,a)" ) )
  val chiBc = Lemma( esChiBc ) {
    unfold( "POR" ) atMost 1 in "Suc_0"
    unfold( "POR" ) atMost 1 in "Ant_2"
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi 0 a", chiBc )

  //The step case of chi
  val esChiSc = Sequent(
    Seq(
      "Ant_2" -> hof" POR(s(n),a)" ),
    Seq(
      "Suc_0" -> hof"POR(s(n),a)" ) )
  val chiSc = Lemma( esChiSc ) {
    unfold( "POR" ) atMost 1 in "Suc_0"
    unfold( "POR" ) atMost 1 in "Ant_2"
    orR
    orL
    trivial
    ref( "chi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi (s n) a", chiSc )

  val esEpsilonBc = Sequent(
    Seq(
      "Ant_2" -> hof" POR(0,iNum(m,a))" ),
    Seq(
      "Suc_0" -> hof"LE(f(a), k)" ) )
  val epsilonBc = Lemma( esEpsilonBc ) {
    unfold( "POR" ) atMost 1 in "Ant_2"
    unfold( "POR" ) atMost 1 in "Ant_2"
    ref( "LEDefinitionSingle" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon 0 m k a", epsilonBc )
  val esEpsilonSc = Sequent(
    Seq(
      "Ant_2" -> hof" POR(s(n),iNum(m,a))" ),
    Seq(
      "Suc_0" -> hof"LE(f(a), k)" ) )
  val epsilonSc = Lemma( esEpsilonSc ) {
    unfold( "POR" ) atMost 1 in "Ant_2"
    orL
    ref( "LEDefinitionSingle" )
    ref( "epsilon" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon (s n) m k a", epsilonSc )

  val esDeltaBc = Sequent(
    Seq(
      "Ant_0" -> hof" E(n, f(iNum(s(0), a)))",
      "Ant_1" -> hof"CSeq(0, n, a)" ),
    Seq(
      "Suc_0" -> hof"E(f(a), f(iNum(s(0), a)))" ) )
  val deltaBc = Lemma( esDeltaBc ) {
    unfold( "CSeq" ) atMost 1 in "Ant_1"
    unfold( "iNum" ) atMost 1 in "Ant_1"
    unfold( "iNum" ) in "Suc_0"
    unfold( "iNum" ) in "Ant_0"

    ref( "NumericTransitivity" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"delta 0 n a", deltaBc )
  val esDeltaSc = Sequent(
    Seq(
      "Ant_0" -> hof" E(n, f(iNum(s(s(k)), a)))",
      "Ant_1" -> hof"CSeq(s(k), n, a)" ),
    Seq(
      "Suc_0" -> hof"E(f(a), f(iNum(s(s(k)), a)))" ) )
  val deltaSc = Lemma( esDeltaSc ) {
    unfold( "CSeq" ) atMost 1 in "Ant_1"
    andL
    cut( "cut", hof"E(f(a), f(iNum(s(k), a)))" )
    ref( "delta" )
    ref( "NumericTransitivityStep" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"delta (s k) n a", deltaSc )
}

