package gapt.examples

import gapt.expr._
import gapt.proofs.Context._
import gapt.proofs.Context
import gapt.proofs.Sequent
import gapt.proofs.gaptic._

object GradedStrictMonotoneSequenceSchema extends TacticsProof {
  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Context.Sort( "i" )
  ctx += hoc"f:i>nat"
  ctx += hoc"suc:i>i"
  ctx += hoc"z:i"
  ctx += hoc"E: nat>nat>o"
  ctx += hoc"LE: nat>nat>o"
  ctx += hoc"iLEQ:i>i>o"
  ctx += hoc"omega: nat>nat>nat>nat"
  ctx += hoc"phi: nat>nat>nat>nat"
  ctx += hoc"chi: nat>nat>nat>i>nat"
  ctx += hoc"nu: nat>nat>i>nat"
  ctx += hoc"mu: nat>nat>i>nat"
  ctx += hoc"delta: nat>nat>i>nat"
  ctx += hoc"epsilon: nat>nat>nat>i>nat"
  ctx += hoc"psi: nat>nat>i>nat"
  ctx += hoc"zeta: nat>nat>i>nat"
  ctx += hoc"theta: nat>nat>i>nat"
  ctx += hoc"xi: nat>nat>i>i>nat"

  ctx += PrimRecFun( hoc"POR:nat>i>o", "POR 0 x = E 0 (f x) ", "POR (s y) x = (E (s y) (f x) ∨ POR y x)" )
  ctx += PrimRecFun( hoc"iNum:nat>i>i", "iNum 0 x = x ", "iNum (s y) x = (suc (iNum y x))" )
  ctx += PrimRecFun( hoc"CSeq:nat>nat>i>o", "CSeq 0 n x = (E n (f (iNum 0 x)))", "CSeq (s y) n x = ((E n (f (iNum (s y) x) ) ) ∧ (CSeq y n x))" )
  ctx += PrimRecFun( hoc"EndSeq:nat>i>o", "EndSeq 0 x = (E (f x) (f x))", "EndSeq (s y) x = ((E (f x ) (f (iNum (s y) x) )) ∧ (EndSeq y x))" )
  ctx += PrimRecFun( hoc"JumpSeq:nat>nat>i>o", "JumpSeq 0 m x = (EndSeq m x) ", "JumpSeq (s y) m x = ( (EndSeq m x) ∧ ∃p ((iLEQ (suc x) (suc p)) ∧ (JumpSeq y m p) ))" )

  // Correct axiom
  // ctx += "LEDefinition" -> hos"POR(n,iNum(m,a)) :- LE(f(a), s(n))"
  //Incorrect axiom which is inconsistent outside this proof
  ctx += "LEDefinitionSingle" -> hos" E(n,f(iNum(m,a))) :- LE(f(a), k)"
  ctx += "NumericTransitivity" -> hos"E(n,f(a)),E(n,f(suc(a))) :- E(f(a), f(suc(a)))"
  ctx += "NumericTransitivityBase" -> hos"E(n,f(a)) :- E(f(a), f(a))"
  ctx += "NumericTransitivityStep" -> hos"E(n,f(iNum(s(k),a))), E(n,f(iNum(k,a))), E(f(a), f(iNum(k,a))) :- E(f(a), f(iNum(s(k),a)))"
  ctx += "minimalElement" -> hos"LE(f(z),0) :- "
  ctx += "ordcon" -> hos"LE(f(iNum(m,a)),s(n)) :- E(n,f(iNum(m,a))), LE(f(a),n)"
  ctx += "reflexive" -> hos":- iLEQ(a,a)"

  val esOmega = Sequent(
    Seq( hof"!x POR(n,x)" ),
    Seq( hof"?x ( JumpSeq(k,m,x))" ) )
  ctx += Context.ProofNameDeclaration( le"omega n k m", esOmega )
  val esPhi = Sequent(
    Seq( hof"?x ( CSeq(m,n,x) ) | !y (LE(f(y),n))" ),
    Seq( hof"?x (  JumpSeq(k,m,x) )" ) )
  ctx += Context.ProofNameDeclaration( le"phi n k m", esPhi )
  val esChi = Sequent(
    Seq( hof"?x ( iLEQ(suc(a),suc(x)) & CSeq(m,n,x) ) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),n))" ),
    Seq( hof"?x ( iLEQ(suc(a),suc(x)) & JumpSeq(k,m,x) )" ) )
  ctx += Context.ProofNameDeclaration( le"chi n k m a", esChi )
  val esNu = Sequent(
    Seq( hof"!x POR(n,x)" ),
    Seq( hof"CSeq(m,n,a)", hof"LE(f(a),n)" ) )
  ctx += Context.ProofNameDeclaration( le"nu m n a", esNu )
  val esDelta = Sequent(
    Seq(
      hof" E(n, f(iNum(s(k), a)))",
      hof"CSeq(k, n, a)" ),
    Seq( hof"E(f(a), f(iNum(s(k), a)))" ) )
  ctx += Context.ProofNameDeclaration( le"delta k n a", esDelta )
  val esMu = Sequent(
    Seq( hof"CSeq(k,n,a) " ),
    Seq( hof"EndSeq(k,a) " ) )
  ctx += Context.ProofNameDeclaration( le"mu k n a", esMu )
  val esEpsilon = Sequent(
    Seq( hof" POR(n,iNum(m,a)) " ),
    Seq( hof" LE(f(a), k)" ) )
  ctx += Context.ProofNameDeclaration( le"epsilon n m k a", esEpsilon )
  val esPsi = Sequent(
    Seq(
      hof" E(n, f(iNum(s(k), a)))",
      hof"CSeq(k, n, a)" ),
    Seq( hof"E(f(a), f(iNum(s(k), a)))" ) )
  ctx += Context.ProofNameDeclaration( le"psi k n a", esPsi )
  val esZeta = Sequent(
    Seq( hof"CSeq(k,n,a) " ),
    Seq( hof"EndSeq(k,a) " ) )
  ctx += Context.ProofNameDeclaration( le"zeta k n a", esZeta )
  val esTheta = Sequent(
    Seq( hof"!x LE(f(x),s(n))" ),
    Seq( hof"LE(f(a),n)", hof"CSeq(m,n,a)" ) )
  ctx += Context.ProofNameDeclaration( le"theta m n a", esTheta )
  val esXi = Sequent(
    Seq( hof"!y ( iLEQ(suc(a), suc(y)) & LE(f(y),s(n)))" ),
    Seq( hof"LE(f(c),n)", hof"CSeq(m,n,c)" ) )
  ctx += Context.ProofNameDeclaration( le"xi m n a c", esXi )
  //The base case of  omega
  val esOmegaBc =
    Sequent(
      Seq( "Ant_0" -> hof"!x POR(0,x)" ),
      Seq( "Suc_0" -> hof"?x (JumpSeq(k,m,x))" ) )
  val omegaBc = Lemma( esOmegaBc ) {
    cut( "cut", hof"?x ( CSeq(m,0,x)) | !y (LE(f(y),0))" )
    orR
    allR( "cut_1", fov"a" )
    exR( "cut_0", fov"a" )
    ref( "nu" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega 0 k m", omegaBc )

  /**
   *
   * The Parameter N is the size of the range
   * The parameter K is the number of jumps
   * The Parameter M is the number of equivalences in a plateau
   */
  val esOmegaSc =
    Sequent(
      Seq( "Ant_0" -> hof"!x POR(s(n),x)" ),
      Seq( "Suc_0" -> hof"?x ( JumpSeq(k,m,x))" ) )
  val omegaSc = Lemma( esOmegaSc ) {
    cut( "cut", hof"?x ( CSeq(m,s(n),x)) | !y (LE(f(y),s(n)))" )
    orR
    allR( "cut_1", fov"a" )
    exR( "cut_0", fov"a" )
    ref( "nu" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega (s n) k m", omegaSc )
  val esPhiBc =
    Sequent(
      Seq( "Ant_0" -> hof"?x (CSeq(0,0,x)) | !y (LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x (JumpSeq(0,0,x))" ) )
  val phiBc = Lemma( esPhiBc ) {
    orL
    exL( fov"a" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    exR( fov"a" )
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    unfold( "iNum" ) atMost 1 in "Ant_0"
    ref( "NumericTransitivityBase" )
    allL( foc"z" )
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0 0 0", phiBc )
  val esPhiBcm =
    Sequent(
      Seq( "Ant_0" -> hof"?x (CSeq(s(m),0,x)) | !y (LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x (JumpSeq(0,s(m),x))" ) )
  val phiBcm = Lemma( esPhiBcm ) {
    orL
    exL( fov"a" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    exR( fov"a" )
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    andR
    andL
    ref( "psi" )
    andL
    ref( "zeta" )
    allL( foc"z" )
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0 0 (s m)", phiBcm )

  val esPhiBc1 =
    Sequent(
      Seq( "Ant_0" -> hof"?x ( CSeq(0,0,x)) | !y (LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x (JumpSeq(s(k),0,x))" ) )
  val phiBc1 = Lemma( esPhiBc1 ) {
    orL
    exL( fov"a" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    exR( fov"a" )
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    andR
    unfold( "iNum" ) atMost 1 in "Ant_0"
    ref( "NumericTransitivityBase" )
    cut( "cut2", hof"?x (iLEQ(suc(a),suc(x)) & CSeq(0,0,x)) | !y (iLEQ(suc(a),suc(y))  & LE(f(y),0))" )
    orR
    exR( "cut2_0", fov"a" )
    andR
    ref( "reflexive" )
    unfold( "CSeq" ) atMost 1 in "cut2_0_0"
    trivial
    ref( "chi" )
    allL( foc"z" )
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0 (s k) 0", phiBc1 )

  val esPhiBc1m =
    Sequent(
      Seq( "Ant_0" -> hof"?x ( CSeq(s(m),0,x)) | !y (LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x (JumpSeq(s(k),s(m),x))" ) )
  val phiBc1m = Lemma( esPhiBc1m ) {
    orL
    exL( fov"a" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    andL
    exR( fov"a" )
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    andR
    andR
    ref( "delta" )
    ref( "mu" )
    cut( "cut2", hof"?x (iLEQ(suc(a),suc(x)) & CSeq(s(m),0,x)) | !y (iLEQ(suc(a),suc(y))  & LE(f(y),0))" )
    orR
    exR( "cut2_0", fov"a" )
    andR
    ref( "reflexive" )
    unfold( "CSeq" ) atMost 1 in "cut2_0_0"
    andR
    trivial
    unfold( "CSeq" ) atMost 1 in "cut2_0_0"
    unfold( "CSeq" ) atMost 1 in "Ant_0_1"
    trivial
    ref( "chi" )
    allL( foc"z" )
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0 (s k) (s m)", phiBc1m )
  val esPhiSc =
    Sequent(
      Seq( "Ant_0" -> hof"?x ( CSeq(0,s(n),x) ) | !y (LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x ( JumpSeq(0,0,x))" ) )
  val phiSc = Lemma( esPhiSc ) {
    cut( "cut", hof"?x ( CSeq(0,n,x)) | !y (LE(f(y),n))" )
    orR
    orL
    exL( fov"a" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    exR( "Suc_0", fov"a" )
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
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
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n) 0 0", phiSc )

  val esPhiScm =
    Sequent(
      Seq( "Ant_0" -> hof"?x ( CSeq(s(m),s(n),x) ) | !y (LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x ( JumpSeq(0,s(m),x))" ) )
  val phiScm = Lemma( esPhiScm ) {
    cut( "cut", hof"?x ( CSeq(s(m),n,x)) | !y (LE(f(y),n))" )
    orR
    orL
    exL( fov"a" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    andL
    exR( "Suc_0", fov"a" )
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    andR
    ref( "delta" )
    ref( "mu" )
    allR( fov"b" )
    exR( "cut_0", fov"b" )
    allL( le"(iNum (s m) b)" )
    unfold( "CSeq" ) atMost 1 in "cut_0_0"
    andR
    ref( "ordcon" )
    ref( "theta" )
    forget( "Ant_0" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n) 0 (s m)", phiScm )

  val esPhiSc1 =
    Sequent(
      Seq( "Ant_0" -> hof"?x ( CSeq(0,s(n),x) ) | !y (LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x ( JumpSeq(s(k),0,x))" ) )
  val phiSc1 = Lemma( esPhiSc1 ) {
    cut( "cut", hof"?x (CSeq(0,n,x) ) | !y (LE(f(y),n))" )
    orR
    orL
    exL( fov"a" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    exR( "Suc_0", fov"a" )
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    andR
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    unfold( "iNum" ) atMost 1 in "Ant_0"
    ref( "NumericTransitivityBase" )
    cut( "cut2", hof"?x (iLEQ(suc(a),suc(x)) & CSeq(0,s(n),x) ) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),s(n)))" )
    orR
    exR( "cut2_0", fov"a" )
    andR
    ref( "reflexive" )
    unfold( "CSeq" ) atMost 1 in "cut2_0_0"
    trivial
    ref( "chi" )
    allR( fov"b" )
    exR( "cut_0", fov"b" )
    allL( le"(iNum 0 b)" )
    unfold( "CSeq" ) atMost 1 in "cut_0_0"
    ref( "ordcon" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n) (s k) 0", phiSc1 )

  val esPhiSc1m =
    Sequent(
      Seq( "Ant_0" -> hof"?x ( CSeq(s(m),s(n),x) ) | !y (LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x ( JumpSeq(s(k),s(m),x))" ) )
  val phiSc1m = Lemma( esPhiSc1m ) {
    cut( "cut", hof"?x (CSeq(s(m),n,x) ) | !y (LE(f(y),n))" )
    orR
    orL
    exL( fov"a" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    exR( "Suc_0", fov"a" )
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    andR
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    andL
    andR
    ref( "psi" )
    ref( "mu" )
    cut( "cut2", hof"?x (iLEQ(suc(a),suc(x)) & CSeq(s(m),s(n),x) ) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),s(n)))" )
    orR
    exR( "cut2_0", fov"a" )
    andR
    ref( "reflexive" )
    unfold( "CSeq" ) atMost 1 in "cut2_0_0"
    trivial
    ref( "chi" )
    allR( fov"b" )
    exR( "cut_0", fov"b" )
    allL( le"(iNum (s m) b)" )
    unfold( "CSeq" ) atMost 1 in "cut_0_0"
    andR
    ref( "ordcon" )
    ref( "theta" )
    forget( "Ant_0" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n) (s k) (s m)", phiSc1m )

  val esChiBc =
    Sequent(
      Seq( "Ant_0" -> hof"?x (iLEQ(suc(a),suc(x)) & CSeq(0,0,x)) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x ( iLEQ(suc(a),suc(x)) & JumpSeq(0,0,x))" ) )
  val chiBc = Lemma( esChiBc ) {
    orL
    exL( fov"b" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    exR( fov"b" )
    andL
    andR
    trivial
    unfold( "JumpSeq" ) in "Suc_0_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    unfold( "iNum" ) atMost 1 in "Ant_0_1"
    ref( "NumericTransitivityBase" )
    allL( foc"z" )
    andL
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi 0 0 0 a", chiBc )

  val esChiBcm =
    Sequent(
      Seq( "Ant_0" -> hof"?x (iLEQ(suc(a),suc(x)) & CSeq(s(m),0,x)) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x ( iLEQ(suc(a),suc(x)) & JumpSeq(0,s(m),x))" ) )
  val chiBcm = Lemma( esChiBcm ) {
    orL
    exL( fov"b" )
    andL
    unfold( "CSeq" ) atMost 1 in "Ant_0_1"
    exR( fov"b" )
    andR
    trivial
    unfold( "JumpSeq" ) in "Suc_0_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    andR
    andL
    ref( "delta" )
    andL
    ref( "mu" )
    allL( foc"z" )
    andL
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi 0 0 (s m) a", chiBcm )

  val esChi1Bc =
    Sequent(
      Seq( "Ant_0" -> hof"?x (iLEQ(suc(a),suc(x)) & CSeq(0,0,x)) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x ( iLEQ(suc(a),suc(x)) & JumpSeq(s(k),0,x))" ) )
  val chi1Bc = Lemma( esChi1Bc ) {
    orL
    exL( fov"b" )
    andL
    unfold( "CSeq" ) atMost 1 in "Ant_0_1"
    exR( fov"b" )
    andR
    trivial
    unfold( "JumpSeq" ) in "Suc_0_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    unfold( "iNum" ) atMost 1 in "Ant_0_1"
    andR
    ref( "NumericTransitivityBase" )
    cut( "cut2", hof"?x (iLEQ(suc(b),suc(x)) & CSeq(0,0,x)) | !y (iLEQ(suc(b),suc(y))  & LE(f(y),0))" )
    orR
    exR( "cut2_0", fov"b" )
    andR
    ref( "reflexive" )
    unfold( "CSeq" ) atMost 1 in "cut2_0_0"
    unfold( "iNum" ) atMost 1 in "cut2_0_0"
    trivial
    ref( "chi" )
    allL( foc"z" )
    andL
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi 0 (s k) 0 a", chi1Bc )

  val esChi1Bcm =
    Sequent(
      Seq( "Ant_0" -> hof"?x (iLEQ(suc(a),suc(x)) & CSeq(s(m),0,x)) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x ( iLEQ(suc(a),suc(x)) & JumpSeq(s(k),s(m),x))" ) )
  val chi1Bcm = Lemma( esChi1Bcm ) {
    orL
    exL( fov"b" )
    andL
    unfold( "CSeq" ) atMost 1 in "Ant_0_1"
    andL
    exR( fov"b" )
    andR
    trivial
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    andR
    andR
    ref( "delta" )
    ref( "mu" )
    cut( "cut2", hof"?x (iLEQ(suc(b),suc(x)) & CSeq(s(m),0,x)) | !y (iLEQ(suc(b),suc(y))  & LE(f(y),0))" )
    orR
    exR( "cut2_0", fov"b" )
    andR
    ref( "reflexive" )
    unfold( "CSeq" ) atMost 1 in "cut2_0_0"
    andR
    unfold( "CSeq" ) atMost 1 in "cut2_0_0"
    trivial
    trivial
    ref( "chi" )
    allL( foc"z" )
    andL
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi 0 (s k) (s m) a", chi1Bcm )

  val esChiSc =
    Sequent(
      Seq( "Ant_0" -> hof"?x (  iLEQ(suc(a),suc(x)) & CSeq(0,s(n),x) ) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x (  iLEQ(suc(a),suc(x)) & JumpSeq(0,0,x) )" ) )
  val ChiSc = Lemma( esChiSc ) {
    cut( "cut", hof"?x ( iLEQ(suc(a),suc(x)) & CSeq(0,n,x)) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),n))" )
    orR
    orL
    exL( fov"b" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    andL
    exR( "Suc_0", fov"b" )
    andR
    trivial
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    unfold( "iNum" ) atMost 1 in "Ant_0_1"
    ref( "NumericTransitivityBase" )

    allR( fov"c" )
    exR( "cut_0", fov"c" )
    allL( le"(iNum 0 c)" )
    unfold( "CSeq" ) atMost 1 in "cut_0_0"
    andL
    unfold( "iNum" ) atMost 1 in "Ant_0_0_0"
    andR( "cut_1" )
    trivial
    andR( "cut_0_0" )
    trivial
    ref( "ordcon" )
    forget( "Ant_0" )
    ref( "chi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi (s n) 0 0 a", ChiSc )

  val esChiScm =
    Sequent(
      Seq( "Ant_0" -> hof"?x (  iLEQ(suc(a),suc(x)) & CSeq(s(m),s(n),x) ) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x (  iLEQ(suc(a),suc(x)) & JumpSeq(0,s(m),x) )" ) )
  val ChiScm = Lemma( esChiScm ) {
    cut( "cut", hof"?x ( iLEQ(suc(a),suc(x)) & CSeq(s(m),n,x)) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),n))" )
    orR
    orL
    exL( fov"b" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    andL
    andL
    exR( "Suc_0", fov"b" )
    andR
    trivial
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    andR
    ref( "delta" )
    ref( "mu" )

    allR( fov"c" )
    exR( "cut_0", fov"c" )
    allL( le"(iNum (s m) c)" )
    unfold( "CSeq" ) atMost 1 in "cut_0_0"
    andL
    andR( "cut_1" )
    allL( fov"c" )
    andL
    trivial
    andR( "cut_0_0" )
    allL( fov"c" )
    andL
    trivial
    andR
    ref( "ordcon" )
    ref( "xi" )
    forget( "Ant_0" )
    ref( "chi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi (s n) 0 (s m) a", ChiScm )

  val esChi1Sc =
    Sequent(
      Seq( "Ant_0" -> hof"?x (  iLEQ(suc(a),suc(x)) & CSeq(0,s(n),x) ) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x ( iLEQ(suc(a),suc(x)) & JumpSeq(s(k),0,x))" ) )
  val chi1Sc = Lemma( esChi1Sc ) {
    cut( "cut", hof"?x ( iLEQ(suc(a),suc(x)) & CSeq(0,n,x)) | !y (iLEQ(suc(a),suc(y))& LE(f(y),n))" )
    orR
    orL
    exL( fov"b" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    andL
    exR( "Suc_0", fov"b" )
    andR
    trivial
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    andR
    unfold( "iNum" ) atMost 1 in "Ant_0_1"
    ref( "NumericTransitivityBase" )
    cut( "cut2", hof"?x (iLEQ(suc(b),suc(x)) & CSeq(0,s(n),x) ) | !y (iLEQ(suc(b),suc(y)) & LE(f(y),s(n)))" )
    orR
    exR( "cut2_0", fov"b" )
    andR
    ref( "reflexive" )
    unfold( "CSeq" ) atMost 1 in "cut2_0_0"
    trivial
    ref( "chi" )
    allR( fov"b" )
    allL( fov"b" )
    andL
    andR
    trivial
    exR( "cut_0", fov"b" )
    allL( le"(iNum 0 b)" )
    andL
    andR
    trivial
    unfold( "CSeq" ) atMost 1 in "cut_0_0"
    ref( "ordcon" )
    forget( "Ant_0" )
    ref( "chi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi (s n) (s k) 0 a", chi1Sc )

  val esChi1Scm =
    Sequent(
      Seq( "Ant_0" -> hof"?x (  iLEQ(suc(a),suc(x)) & CSeq(s(m),s(n),x) ) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x ( iLEQ(suc(a),suc(x)) & JumpSeq(s(k),s(m),x))" ) )
  val chi1Scm = Lemma( esChi1Scm ) {
    cut( "cut", hof"?x ( iLEQ(suc(a),suc(x)) & CSeq(s(m),n,x)) | !y (iLEQ(suc(a),suc(y))& LE(f(y),n))" )
    orR
    orL
    exL( fov"b" )
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    andL
    andL
    unfold( "JumpSeq" ) atMost 1 in "Suc_0"
    exR( "Suc_0", fov"b" )
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0_0"
    andR
    trivial
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    andR
    andR
    ref( "delta" )
    ref( "mu" )
    cut( "cut2", hof"?x (iLEQ(suc(b),suc(x)) & CSeq(s(m),s(n),x) ) | !y (iLEQ(suc(b),suc(y)) & LE(f(y),s(n)))" )

    orR
    exR( "cut2_0", fov"b" )
    andR
    ref( "reflexive" )
    unfold( "CSeq" ) atMost 1 in "cut2_0_0"
    andR( "cut2_0_0" )
    trivial
    trivial
    ref( "chi" )
    allR( fov"b" )
    allL( fov"b" )
    andL
    andR
    trivial
    exR( "cut_0", fov"b" )
    allL( le"(iNum (s m) b)" )
    andL
    andR
    trivial
    unfold( "CSeq" ) atMost 1 in "cut_0_0"
    andR
    ref( "ordcon" )
    ref( "xi" )
    forget( "Ant_0" )
    ref( "chi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi (s n) (s k) (s m) a", chi1Scm )

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

  val esNuBc = Sequent(
    Seq(
      "Ant_0" -> hof"!x POR(0,x)" ),
    Seq(
      "Suc_0" -> hof"CSeq(0,0,a)",
      "Suc_1" -> hof"LE(f(a),0)" ) )
  val nuBc = Lemma( esNuBc ) {
    allL( le"(iNum 0 a)" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    unfold( "CSeq" ) atMost 1 in "Suc_0"
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"nu 0 0 a", nuBc )
  val esNu1Bc = Sequent(
    Seq(
      "Ant_0" -> hof"!x POR(s(n),x)" ),
    Seq(
      "Suc_0" -> hof"CSeq(0,s(n),a)",
      "Suc_1" -> hof"LE(f(a),s(n))" ) )
  val nu1Bc = Lemma( esNu1Bc ) {
    allL( le"(iNum 0 a)" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    unfold( "CSeq" ) atMost 1 in "Suc_0"
    orL
    trivial
    ref( "epsilon" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"nu 0 (s n) a", nu1Bc )
  val esNu2Bc = Sequent(
    Seq(
      "Ant_0" -> hof"!x POR(0,x)" ),
    Seq(
      "Suc_0" -> hof"CSeq(s(m),0,a)",
      "Suc_1" -> hof"LE(f(a),0)" ) )
  val nu2Bc = Lemma( esNu2Bc ) {
    allL( le"(iNum (s m) a)" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    unfold( "CSeq" ) atMost 1 in "Suc_0"
    andR
    trivial
    ref( "nu" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"nu (s m) 0 a", nu2Bc )
  val esNuSc = Sequent(
    Seq(
      "Ant_0" -> hof"!x POR(s(n),x)" ),
    Seq(
      "Suc_0" -> hof"CSeq(s(m),s(n),a)",
      "Suc_1" -> hof"LE(f(a),s(n))" ) )
  val nuSc = Lemma( esNuSc ) {
    allL( le"(iNum (s m) a)" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    unfold( "CSeq" ) atMost 1 in "Suc_0"
    orL
    andR
    trivial
    ref( "LEDefinitionSingle" )
    andR
    ref( "epsilon" )
    ref( "nu" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"nu (s m) (s n) a", nuSc )

  val esPsiBc = Sequent(
    Seq(
      "Ant_0" -> hof" E(n, f(iNum(s(0), a)))",
      "Ant_1" -> hof"CSeq(0, n, a)" ),
    Seq(
      "Suc_0" -> hof"E(f(a), f(iNum(s(0), a)))" ) )
  val psiBc = Lemma( esPsiBc ) {
    unfold( "CSeq" ) atMost 1 in "Ant_1"
    unfold( "iNum" ) atMost 1 in "Ant_1"
    unfold( "iNum" ) in "Suc_0"
    unfold( "iNum" ) in "Ant_0"

    ref( "NumericTransitivity" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"psi 0 n a", psiBc )
  val esPsiSc = Sequent(
    Seq(
      "Ant_0" -> hof" E(n, f(iNum(s(s(k)), a)))",
      "Ant_1" -> hof"CSeq(s(k), n, a)" ),
    Seq(
      "Suc_0" -> hof"E(f(a), f(iNum(s(s(k)), a)))" ) )
  val psiSc = Lemma( esPsiSc ) {
    unfold( "CSeq" ) atMost 1 in "Ant_1"
    andL
    cut( "cut", hof"E(f(a), f(iNum(s(k), a)))" )
    ref( "delta" )
    ref( "NumericTransitivityStep" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"psi (s k) n a", psiSc )

  val esZetaBc =
    Sequent(
      Seq( "Ant_0" -> hof"CSeq(0,n,a)" ),
      Seq( "Suc_0" -> hof"EndSeq(0,a)" ) )
  val zetaBc = Lemma( esZetaBc ) {
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0"
    unfold( "iNum" ) atMost 1 in "Suc_0"
    unfold( "iNum" ) atMost 1 in "Ant_0"
    ref( "NumericTransitivityBase" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"zeta 0 n a", zetaBc )

  val esZetaSc =
    Sequent(
      Seq( "Ant_0" -> hof"CSeq(s(k),n,a)" ),
      Seq( "Suc_0" -> hof"EndSeq(s(k),a)" ) )
  val zetaSc = Lemma( esZetaSc ) {
    unfold( "CSeq" ) atMost 1 in "Ant_0"
    unfold( "EndSeq" ) atMost 1 in "Suc_0"
    andL
    andR
    ref( "delta" )
    ref( "mu" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"zeta (s k) n a", zetaSc )

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

  val esXiBc =
    Sequent(
      Seq( "Ant_0" -> hof"!y ( iLEQ(suc(a), suc(y)) & LE(f(y),s(n)))" ),
      Seq(
        "Suc_0" -> hof"CSeq(0,n,c)",
        "Suc_1" -> hof"LE(f(c),n)" ) )
  val xiBc = Lemma( esXiBc ) {
    unfold( "CSeq" ) atMost 1 in "Suc_0"
    allL( le"(iNum 0 c)" )
    andL
    ref( "ordcon" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"xi 0 n a c", xiBc )

  val esXiSc =
    Sequent(
      Seq( "Ant_0" -> hof"!y ( iLEQ(suc(a), suc(y)) & LE(f(y),s(n)))" ),
      Seq(
        "Suc_0" -> hof"CSeq(s(k),n,c)",
        "Suc_1" -> hof"LE(f(c),n)" ) )
  val xiSc = Lemma( esXiSc ) {
    unfold( "CSeq" ) atMost 1 in "Suc_0"
    andR
    allL( le"(iNum (s k) c)" )
    andL
    ref( "ordcon" )
    ref( "xi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"xi (s k) n a c", xiSc )
}

