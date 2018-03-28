package at.logic.gapt.examples

  import at.logic.gapt.expr._
  import at.logic.gapt.proofs.Context.PrimRecFun
  import at.logic.gapt.proofs.{ Context, Sequent }
  import at.logic.gapt.proofs.gaptic.TacticsProof
  import at.logic.gapt.proofs.gaptic._

  object VeryWeakPHPSequenceSchema extends TacticsProof {
    ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
    ctx += Context.Sort( "i" )
    ctx += hoc"f:nat>i>nat"
    ctx += hoc"suc:i>i"
    ctx += hoc"z:i"
    ctx += hoc"E: nat>nat>o"
    ctx += hoc"LE: nat>nat>o"

    ctx += hoc"omega: nat>nat>nat"
    ctx += hoc"phi: nat>nat>nat"
    ctx += PrimRecFun( hoc"POR:nat>nat>i>o", "POR 0 m x = E 0 (f m x) ", "POR (s y) m x = (E (s y) (f m x) ∨ POR y m x)" )
    ctx += PrimRecFun( hoc"PAND:nat>nat>o", "(PAND 0 n)= (∀x (POR n 0 x))", "(PAND (s m) n) = ((∀x (POR n (s m) x)) & (PAND m n))" )
    ctx += PrimRecFun( hoc"TopFuncDef:nat>nat>i>o", "(TopFuncDef 0 k x)= (E (f 0 x) (f k x)) ", "(TopFuncDef (s m) k x)= ((E (f (s m) x) (f k x)) | (TopFuncDef m k x))" )
    ctx += PrimRecFun(hoc"CutDistinct:nat>nat>i>o",
      "(CutDistinct 0 n x) =  ( ( (E n (f 0 x)) & (E n (f 0 (suc x))) ) | (∀y (LE (f 0 y) n)))",
      "(CutDistinct (s m) n x) = ((CutDistinct m n x) &  ( (E n (f (s m) x)) & (E n (f (s m) (suc x))) ) | (∀y (LE (f (s m) y) n)))" )
    ctx += "LEDefinition" -> hos"POR(n,m,a) :- LE(f(m,a), s(n))"
    ctx += "LEDefinition2" -> hos"POR(n,m, suc(a)) :- LE(f(m,a), s(n))"
    ctx += "NumericTransitivity" -> hos"E(n,f(m,a)),E(n,f(m,suc(a))) :- E(f(m,a), f(m,suc(a)))"
    ctx += "minimalElement" -> hos"LE(f(m,z),0) :- "
    ctx += "ordcon" -> hos"LE(f(m,a),s(n)) :- E(n,f(m,a)), LE(f(m,a),n)"
    ctx += "ordcon2" -> hos"LE(f(m,suc(a)),s(n)) :- E(n,f(m,suc(a))), LE(f(m,a),n)"

    val esOmega = Sequent(
      Seq( hof"PAND(m,n)",
           hof"!x TopFuncDef(m,s(m),x)"),
      Seq( hof"?x ( E(f(s(m),x), f(s(m),suc(x))) )" ) )
    ctx += Context.ProofNameDeclaration( le"omega n m", esOmega )
    val esPhi = Sequent(
      Seq( hof"?x CutDistinct(m,n,x)",
           hof"!x TopFuncDef(m,s(m),x)"),
      Seq( hof"?x ( E(f(s(m),x), f(s(m),suc(x))) )" ) )
    ctx += Context.ProofNameDeclaration( le"phi n m", esPhi )

    //The base case of  omega
    val esOmegaBc =
      Sequent(
        Seq( "Ant_0" -> hof"PAND(0,0)",
             "Ant_1" -> hof"!x TopFuncDef(0,s(0),x)"),
        Seq( "Suc_0" -> hof"?x (E(f(s(0),x), f(s(0),suc(x))))" ) )
    val omegaBc = Lemma( esOmegaBc ) {
      cut( "cut", hof"?x CutDistinct(0,0,x)" )
      unfold( "CutDistinct" ) atMost 1 in "cut"
      unfold( "PAND" ) atMost 1 in "Ant_0"
      exR( "cut", hoc"z" )
      orR
      andR
      allL( "Ant_0", hoc"z" )
      unfold( "POR" ) atMost 1 in "Ant_0_0"
      trivial
      allL( "Ant_0", le"(suc z)" )
      unfold( "POR" ) atMost 1 in "Ant_0_0"
      trivial
      ref( "phi" )
    }
    ctx += Context.ProofDefinitionDeclaration( le"omega 0 0", omegaBc )

    val esOmegaSc =
      Sequent(
        Seq( "Ant_0" -> hof"PAND(0,s(n))",
             "Ant_1" -> hof"!x TopFuncDef(0,s(0),x)"),
        Seq( "Suc_0" -> hof"?x (E(f(0,x), f(0,suc(x))))" ) )
    val omegaSc = Lemma( esOmegaSc ) {
      cut( "cut", hof"?x CutDistinct(0,s(n),x)" )
      unfold( "CutDistinct" ) atMost 1 in "cut"
      unfold( "PAND" ) atMost 1 in "Ant_0"
      orR
      allR( "cut_1", fov"a" )
      exR( "cut_0", fov"a" )
      andR
      allL( "Ant_0", fov"a" )
      unfold( "POR" ) atMost 1 in "Ant_0_0"
      orL
      trivial
      ref( "LEDefinition" )
      allL( "Ant_0", le"(suc a)" )
      unfold( "POR" ) atMost 1 in "Ant_0_0"
      orL
      trivial
      ref( "LEDefinition2" )
      ref( "phi" )

    }
    ctx += Context.ProofDefinitionDeclaration( le"omega (s n) 0", omegaSc )

    val esPhiBc =
      Sequent(
        Seq( "Ant_0" -> hof"?x ( E(0,f(x)) & E(0,f(suc(x)))) | !y (LE(f(y),0))" ),
        Seq( "Suc_0" -> hof"?x (E(f(x), f(suc(x))) )" ) )
    val phiBc = Lemma( esPhiBc ) {
      orL
      exL( fov"a" )
      andL
      exR( fov"a" )
      ref( "NumericTransitivity" )
      allL( foc"z" )
      ref( "minimalElement" )
    }
    ctx += Context.ProofDefinitionDeclaration( le"phi 0", phiBc )

    val esPhiSc =
      Sequent(
        Seq( "Ant_0" -> hof"?x ( E(s(n),f(x)) & E(s(n),f(suc(x)))) | !y (LE(f(y),s(n)))" ),
        Seq( "Suc_0" -> hof"?x (E(f(x), f(suc(x))) )" ) )
    val phiSc = Lemma( esPhiSc ) {
      cut( "cut", hof"?x ( E(n,f(x)) & E(n,f(suc(x)))) | !y (LE(f(y),n))" )
      orR
      orL
      exL( fov"a" )
      andL
      exR( "Suc_0", fov"a" )
      ref( "NumericTransitivity" )
      allR( fov"b" )
      exR( "cut_0", fov"b" )
      allL( fov"b" )
      andR
      ref( "ordcon" )
      allL( le"(suc b)" )
      ref( "ordcon2" )
      ref( "phi" )
    }
    ctx += Context.ProofDefinitionDeclaration( le"phi (s n)", phiSc )

  }

