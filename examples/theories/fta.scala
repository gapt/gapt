package gapt.examples.theories
import gapt.expr._
import gapt.proofs.gaptic._

object fta extends Theory(natlists, listlength, natdivisible) {
  dfn(hof"primedec l n = (lall prime l & n = prod l)")
  val primedecnil = lemma(hof"primedec nil n <-> n=1", "simp") { simp.w("primedec") }
  val primedeccons = lemma(hof"primedec (cons k d) (k*n) <-> prime k & primedec d n") {
    simp.w("primedec"); destruct("g") onAll decompose onAll simp.h
    simp.h.on("g_0_1").w("primene0")
  }

  val mulsbnd = lemma(hof"1<y&x!=0 -> x<x*y", "simp") {
    induction(hov"y:nat"); simp; simp
    include("mul0eq", "addsmonl", "add0l", "lt0l"); escrgt
  }
  val mulsbndr = lemma(hof"1<y&x!=0 -> x<y*x", "simp") { include("mulsbnd", "mulcomm"); escrgt }

  val dvdnotelemprod = lemma(hof"prime x & lall prime xs & ~elem xs x -> ~dvd(x, prod(xs))") {
    induction(hov"xs:list nat") onAll simp onAll impR onAll simp.h("primene1")
    decompose; simp.w("prime", "ltsl").on("g_0_0_1_0"); decompose
    allL(le"x:nat").forget; simp.h.on("g_0_0_1_0_1"); simp.h.on("g_0_0_0")
  }
  val permconsdel = lemma(hof"elem xs x -> perm xs (cons x (del x xs))", "simp") {
    simp.w("elem", "perm"); decompose; cut("zx", hof"z=(x:?a)") onAll simp.h
  }
  val lalldel = lemma(hof"lall f xs -> lall f (del x xs)") {
    induction(hov"xs:list?a") onAll simp
    decompose; cut("xx0", hof"x = (x_0:?a)") onAll simp.h
  }

  val primelistdvdcnt = lemma(hof"lall prime d1 & lall prime d2 -> dvd (prod d1) (prod d2) <-> !k cnt(k,d1)<=cnt(k,d2)") {
    generalize(hov"d2:list nat"); induction(hov"d1:list nat"); allR; simp
    allR; simp; decompose
    cut("d2x", hof"cnt (x:nat) d2 != 0"); negR("d2x")
    by { // case 1: x not in d2
      cut("dvdxd2", hof"~dvd(x,prod(d2))"); by { simp.h.on("dvdxd2").w("dvdnotelemprod", "elem") }
      cut("dvdxd1d2", hof"~dvd(x*prod(d1_0),prod(d2))"); by { include("dvdtrans", "dvdmul"); escrgt }
      simp.h; exR(le"x:nat").forget; simp.h
    }
    by { // case 2: x in d2
      cut("pd2", hof"prod(d2) = prod(cons(x, del(x, d2)))"); by { forget("g_1"); include("prodperm"); chain("prodperm"); simp.h("elem") }
      cut("g", hof"!(k:nat) (cnt k d1_0 <= cnt k (del x d2) <-> cnt k (cons x d1_0) <= cnt k d2)") right by { simp.h("primene0", "lalldel") }; forget("g_1")
      forget("IHd1_0"); allR; cut("kx", hof"k=(x:nat)") onAll simp.h
    }
  }

  val primedecdvdcnt = lemma(hof"primedec d1 n1 & primedec d2 n2 -> dvd n1 n2 <-> !k cnt(k,d1)<=cnt(k,d2)") {
    simp.w("primedec"); decompose; simp.h.w("primelistdvdcnt")
  }

  val primedecuniq = lemma(hof"primedec d1 n & primedec d2 n -> perm d1 d2") {
    decompose; simp.w("perm"); include("primedecdvdcnt", "leantisymm", "dvdrefl"); escrgt
  }

  val primeexmul = lemma(hof"?d primedec d m & ?d primedec d n -> ?d primedec d (m*n)") {
    simp.w("primedec"); decompose; exR(le"app d (d_0: list nat)").forget; simp.h
  }

  // TODO: well-founded induction
  val primedecexstep = lemma(hof"!m(m<n -> m!=0 -> ?d primedec d m) -> (n!=0 -> ?d primedec d n)") {
    impR; impR; cut("pn", hof"~prime n"); by { negR("pn"); exR(le"cons (n:nat) nil").forget; simp.h("primedec") }
    cut("n1", hof"n!=s(0)"); by { negR("n1"); exR(le"nil: list nat").forget; simp.h("primedec") }
    simp.h.on("pn")("primecomp", "ltsl", "composite"); exL(hov"k:nat"); exL(hov"l:nat")
    simp.h
    include("primeexmul"); chain("primeexmul") onAll forget("primeexmul")
    (chain("g_0") onAll simp.h("ltsl")).onAllSubGoals
  }
  val primedecex = lemma(hof"n!=0 -> ?d primedec d n") {
    cut("gen", hof"~ !m (m<=n -> m!=0 -> ?d primedec d m)"); by { decompose; chain("gen"); simp.on("g_1"); prop }; forget("g"); negL
    induction(hov"n:nat") onAll allR
    by { simp; prop }
    by {
      repeat(impR); include("primedecexstep"); chain("primedecexstep")
      allR; simp.w("lt"); repeat(impR); chain("IHn_0")
      include("letrans", "less"); escrgt
      prop; prop
    }
  }
}
