import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKProofSchemata
object niaSchema extends TacticsProof {
  ctx += Context.Sort( "i" )
  ctx += Context.Sort( "w" )
  ctx += hoc"E: w>w>o"
  ctx += hoc"LEQ: i>i>o"
  ctx += hoc"LE: i>i>o"
  ctx += hoc"0:w"
  ctx += hoc"0i:i"
  ctx += hoc"si:i>i"
  ctx += hoc"s:w>w"
  ctx += hoc"f:i>w"
  ctx += hoc"POR:w>i>o"
  ctx += hoc"mu: w>w"
  ctx += hoc"omega: w>w"
  ctx += hoc"phi: w>w"
  ctx += hoc"chi: w>i>w"
  ctx += hos"E(f(p),n),E(f(q),n) :- E(f(p),f(q))"
  ctx += hos" :- LEQ(p,p)"
  ctx += hos"LEQ(si(p),q):- LE(p,q)"

//The Name declaration of proof mu
  val esMu = Sequent( Seq(hof"!x?y(LEQ(x,y) & E(f(y),n))") , Seq( hof"?p?q (LE(p,q) & E(f(p),f(q)))" ) )
  ctx += Context.ProofNameDeclaration( le"mu n", esMu )
//The Name declaration of proof omega
  val esOmega = Sequent( 
      Seq(hof"!x!y POR(s(y),x) = (E(f(x),s(y)) |  POR(y,x))", 
          hof"!x POR(0,x) = E(f(x),0)",
          hof"!x POR(n,x)"
         ) , 
      Seq( hof"?p?q (LE(p,q) & E(f(p),f(q)))" ) )
  ctx += Context.ProofNameDeclaration( le"omega n", esOmega )


//The Name declaration of proof phi
  val esphi = Sequent( 
      Seq(hof"!x!y POR(s(y),x) = (E(f(x),s(y)) &  POR(y,x))", 
          hof"!x POR(0,x) = E(f(x),0)",
          hof"!x?y (LEQ(x,y) & POR(n,y) )   "
         ) , 
      Seq( hof"?p?q (LE(p,q) & E(f(p),f(q)))" ) )
  ctx += Context.ProofNameDeclaration( le"phi n", esphi )

//The Name declaration of proof chi
  val eschi = Sequent( 
      Seq(hof"!y POR(s(y),a) = (E(f(a),s(y)) |  POR(y,a))", 
          hof" POR(0,a) = E(f(a),0)",
          hof" POR(n,a) "
         ) , 
      Seq( hof"POR(n,a)" ) )
  ctx += Context.ProofNameDeclaration( le"chi n a", eschi )


//The base case of  mu
   val esMuBc = Sequent(
    Seq(( "Ant_0" -> hof"!x?y (LEQ(x,y) & E(f(y),0))   "   )),
    Seq(( "Suc_0" -> hof"?p?q (LE(p,q) & E(f(p),f(q))) "   ))
  )
  val muBc = Lemma( esMuBc ) {
    allL(hoc"0i:i")
    exL(fov"B")
    allL(le"(si B)")
    exL(fov"A")
    exR(fov"B")
    forget("Suc_0")
    exR(fov"A")
    forget("Suc_0_0")
    andL("Ant_0_1")
    andL
    andR
    foTheory
    foTheory
  }
  ctx += Context.ProofDefinitionDeclaration( le"mu 0", muBc )

//The step case of mu
 val esMuSc = Sequent(
    Seq(( "Ant_0" -> hof"!x?y (LEQ(x,y) & E(f(y),s(n)))   "   )),
    Seq(( "Suc_0" -> hof"?p?q (LE(p,q) & E(f(p),f(q))) "   ))
  )
  val muSc = Lemma( esMuSc ) {
    allL(hoc"0i:i")
    exL(fov"B")
    allL(le"(si B)")
    exL(fov"A")
    exR(fov"B")
    forget("Suc_0")
    exR(fov"A")
    forget("Suc_0_0")
    andL("Ant_0_1")
    andL
    andR
    foTheory
    foTheory
  }
  ctx += Context.ProofDefinitionDeclaration( le"mu (s n)", muSc )

//The base case of  omega
   val esOmegaBc = Sequent(
    Seq(( "Ant_0" -> hof"!x!y POR(s(y),x) = (E(f(x),s(y)) |  POR(y,x))"   ),
        ( "Ant_1" -> hof"!x POR(0,x) = E(f(x),0)"   ),
        ( "Ant_2" -> hof"!x POR(0,x)"   )),
    Seq(( "Suc_0" -> hof"?p?q (LE(p,q) & E(f(p),f(q))) "   ))
  )
  val omegaBc = Lemma( esOmegaBc ) {
    cut("cut", hof"!x?y (LEQ(x,y) & E(f(y),0))")
    allR(fov"A")
    allL("Ant_2",fov"A")
    allL("Ant_1",fov"A")
    exR("cut",fov"A")
    rewrite ltr "Ant_1_0" in "Ant_2_0"
    andR
    foTheory
    trivial
    pLink("mu")
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega 0", omegaBc )


// The Basecase of chi
val esChiBc = Sequent(
    Seq(( "Ant_0" -> hof"!y POR(s(y),a) = (E(f(a),s(y)) | POR(y,a))"   ),
        ( "Ant_1" -> hof"POR(0,a) = E(f(a),0)"   ),
        ( "Ant_2" -> hof" POR(0,a)"   )),
    Seq(
      ( "Suc_0" -> hof"POR(0,a)" )
    )
  )
  val chiBc = Lemma( esChiBc ) {
    rewrite ltr "Ant_1" in "Suc_0"
    rewrite ltr "Ant_1" in "Ant_2"
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi 0 a", chiBc )

//The step case of chi
  val esChiSc = Sequent(
    Seq(( "Ant_0" -> hof"!y POR(s(y),a) = (E(f(a),s(y)) |  POR(y,a))"   ),
        ( "Ant_1" -> hof"POR(0,a) = E(f(a),0)"   ),
        ( "Ant_2" -> hof" POR(s(n),a)"   )),
    Seq(
      ( "Suc_0" -> hof"POR(s(n),a)" )
    )
  )
  val chiSc = Lemma( esChiSc ) {
    rewrite ltr "Ant_0" in "Suc_0"
    rewrite ltr "Ant_0" in "Ant_2"
    orR
    orL
    trivial
    pLink( "chi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi (s n) a", chiSc)

//The base case of phi
  val esphiBc = Sequent(
    Seq(( "Ant_0" -> hof"!x?y (LEQ(x,y) & E(f(y),0))   "   )),
    Seq(( "Suc_0" -> hof"?p?q (LE(p,q) & E(f(p),f(q))) "   ))
  )
   val phiBc = Lemma( esphiBc ) {
    pLink( "mu" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0", phiBc)

//The step case of phi

  val esphiSc = Sequent(
    Seq(( "Ant_0" -> hof"!x?y (LEQ(x,y) & POR(s(n),x))   "   )),
    Seq(( "Suc_0" -> hof"?p?q (LE(p,q) & E(f(p),f(q))) "   ))
  )
   val phiSc = Lemma( esphiSc ) {
          cut("cut", hof"!x?y (LEQ(x,y) & E(f(y),s(n)))")
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n)", phiSc)
}




