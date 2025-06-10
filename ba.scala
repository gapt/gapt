import gapt.expr._
import gapt.formats.babel.{Notation, Precedence}
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.proofs.Sequent
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._

object proof extends TacticsProof {
  ctx += Sort("i")

  ctx += Notation.Infix( "⊆", Precedence.infixRel)
  ctx += hof"(A ⊆ B) = (∀(x:i) ((A x) -> (B x)))"

  ctx += Const("0", Ti)
  ctx += Const("1", Ti)
  ctx += Notation.Infix("+", Precedence.plusMinus)
  ctx += hoc"+: i>i>i"
  ctx += Notation.Infix("-", Precedence.plusMinus)
  ctx += hoc"-: i>i"
  ctx += Notation.Infix("*", Precedence.timesDiv)
  ctx += hoc"*: i>i>i"
  ctx += Notation.Infix("**", Precedence.timesDiv)
  ctx += hof"x ** A = ( λy ∃(a:i) ( (A a) ∧ y = x*a ) )"
  ctx += Notation.Infix("++", Precedence.timesDiv)
  ctx += hof"x ++ A = ( λy ∃(a:i) ( (A a) ∧ y = x+a ) )"
  ctx += Notation.Infix("⊕", Precedence.plusMinus)
  ctx += hof"A ⊕ B = ( λy ∃(a:i) ∃(b:i) ( (A a) ∧ (B b) ∧ y = a+b ) )"

  val axioms = 
       ("extens" -> hof"∀A∀B ((A = B) <-> ∀(z:i) (A z <-> B z))")
    +: ("0_element" -> hof"R 0")
    +: ("1_element" -> hof"R 1")
    +: ("plusneutral" -> hof"∀(x:i) (R x → x + 0 = x)")
    +: ("plusclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x + y))")
    +: ("plusassoc" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) + z) = (x + (y + z)))")
    +: ("plusinverse" -> hof"∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))")
    +: ("pluscomm" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → (x + y = y + x))")
    +: ("multneutral" -> hof"∀(x:i) (R x → ((x * 1) = x))")
    +: ("multclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))")
    +: ("multassoc" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x * y) * z) = (x * (y * z)))")
    +: Sequent()

  def minusminus = Lemma(
    Sequent(
      Seq(("plusclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x + y))"),
          ("plusinverse" -> hof"∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))"),
          ("pluscomm" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → (x + y = y + x))")),
      Seq("minusminus" -> hof"∀x (R x -> -(-x) = x)")
      )
    ){
    decompose
    allL("plusinverse",hov"x:i")
    allL("pluscomm",le"-x",hov"x:i")
    impL("plusinverse_0") left by {trivial}
    
  }

  def subReflexivity = Lemma(Sequent() :+ ("ref" -> hof"∀A A ⊆ A")) {
    unfold("⊆") in "ref"
    decompose
    trivial
  }

  def subAntisymmetry = Lemma(
    Sequent(
        Seq("extens" -> hof"∀A∀B ((A = B) <-> ∀(z:i) (A z <-> B z))"),
        Seq("antisym" -> hof"∀A∀B (( A ⊆ B & B ⊆ A ) -> ( A = B ))")
    )
  ) {
    allR("antisym",hov"A:i>o")
    allR("antisym",hov"B:i>o")
    decompose
    allL("extens",hov"A:i>o",hov"B:i>o").forget
    andL
    chain("extens_1")
    forget("extens_0","extens_1")
    decompose
    unfold("⊆") in ("antisym_0_0","antisym_0_1")
    andR left by {
      forget("antisym_0_1")
      allL("antisym_0_0",hov"z:i").forget
      trivial
    }
    forget("antisym_0_0")
    allL("antisym_0_1",hov"z:i").forget
    trivial
  }

  def subTransitivity = Lemma(
    Sequent() :+ ("trans" -> hof"∀A∀B∀C ( ( A ⊆ B ∧ B ⊆ C ) -> ( A ⊆ C ) )")
  ) {
    allR
    allR
    allR
    unfold("⊆") in "trans"
    decompose
    allL("trans_0_0",hov"x:i").forget
    allL("trans_0_1",hov"x:i").forget
    impL("trans_0_0") left by {trivial}
    impL("trans_0_1") left by {trivial}
    trivial
  }

  def sumCompatibility = Lemma(
    Sequent() :+ ("compplus" -> hof"∀A∀B∀C (A ⊆ B -> (C ⊕ A) ⊆ (C ⊕ B))")
  ){
    decompose
    unfold("⊕") in "compplus_1"
    unfold("⊆") in ("compplus_0","compplus_1")
    decompose
    allL("compplus_0",hov"b:i").forget
    impL("compplus_0") left by {trivial}
    exR(hov"a:i",hov"b:i").forget
    andR right by {trivial}
    andR left by{trivial}
    trivial
  }
  

  def multleftCompatibility = Lemma(
    Sequent() :+ ("compmult" -> hof"∀A∀B (A ⊆ B -> ∀x ( x ** A ⊆ x ** B))")
  ){
    decompose
    unfold("**") in "compmult_1"
    unfold("⊆") in ("compmult_0","compmult_1")
    decompose
    allL("compmult_0",hov"a:i").forget
    exR(hov"a:i").forget
    andR right by {trivial}
    impL("compmult_0") left by {trivial}
    trivial
  }

  def multClosed = Lemma(
    Sequent(
      Seq("multclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"), 
      Seq("Rmultclosed" -> hof"∀x (R x → x ** R ⊆ R)")
    )
  ){
    decompose
    unfold("**","⊆") in "Rmultclosed_1"
    decompose
    allL("multclosed",hov"x:i",hov"a:i").forget
    impL left by {
      andR left by {trivial}
      trivial
    }
    eql("Rmultclosed_1_0_1","multclosed")
    trivial
  }

  def multClosed_inv = Lemma(
    Sequent(
      Seq(("multclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"),
          ("extens" -> hof"∀A∀B ((A = B) <-> ∀(z:i) (A z <-> B z))")), 
      Seq("Rmultclosed_inv" -> hof"∀x (R (-x) → x ** R = R)")
    )
  ){
    decompose
    allL("extens",le"x ** R",hov"R:i>o").forget
    andL
    impL("extens_1")
    // unfold("**","⊆") in "Rmultclosed_equ_1"
    // decompose
    // allL("multclosed",hov"x:i",hov"a:i").forget
    // impL left by {
    //   andR left by {trivial}
    //   trivial
    // }
    // eql("Rmultclosed_equ_1_0_1","multclosed")
    // trivial
  }

  def plusClosed = Lemma(
    Sequent(
      Seq("plusclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x + y))"),
      Seq("Rplusclosed" -> hof"∀x (R x → x ++ R ⊆ R)")
    )
  ){
    decompose
    unfold("++","⊆") in "Rplusclosed_1"
    decompose
    allL("plusclosed",hov"x:i",hov"a:i").forget
    impL left by {
      andR left by {trivial}
      trivial
    }
    forget("Rplusclosed_1_0_0","Rplusclosed_0")
    eql("Rplusclosed_1_0_1","plusclosed")
    trivial
  }

  def setPlusClosed = Lemma(
    Sequent(
      Seq("plusclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x + y))"),
      Seq("setplusclosed" -> hof"∀(x:i) R ⊕ R ⊆ R")
    )
  ){
    decompose
    unfold("⊕","⊆") in "setplusclosed"
    decompose
    allL("plusclosed",hov"a:i",hov"b:i").forget
    impL left by {
      andR left by{trivial}
      trivial
    }    
    eql("setplusclosed_0_1","plusclosed")
    trivial
  }

  def multleftAssoc = Lemma(
    Sequent(
        Seq("extens" -> hof"∀A∀B ((A = B) <-> ∀(z:i) (A z <-> B z))",
            "multassoc" -> hof"∀(x:i)∀(y:i)∀(z:i) ((x * y) * z) = (x * (y * z))"),
        Seq("multsetassoc" -> hof"∀x∀y∀R x ** (y ** R) = (x * y) ** R")
    )
  ){
    decompose
    allL("extens",le"x ** (y ** R)",le"(x * y) ** R").forget
    andL
    chain("extens_1")
    decompose
    forget("extens_0","extens_1")
    andR left by {
      impR
      unfold("**") in ("multsetassoc_0","multsetassoc_1")
      decompose
      eql("multsetassoc_0_0_1","multsetassoc_0_1")
      exR(hov"a_0:i").forget
      andR left by {trivial}
      allL("multassoc",hov"x:i",hov"y:i",hov"a_0:i").forget
      eql("multassoc","multsetassoc_0_1")
      trivial
    }
    unfold("**") in "multsetassoc"
    decompose
    exR("multsetassoc_1",le"y * a").forget
    andR 
    exR(hov"a:i").forget
    andR left by {
      trivial
    }
    trivial
    allL("multassoc",hov"x:i",hov"y:i",hov"a:i").forget
    eql("multassoc","multsetassoc_0_1")
    trivial
  }

  def inverse = Lemma(
    Sequent(
        Seq(("extens" -> hof"∀A∀B ((A = B) <-> ∀(z:i) (A z <-> B z))"),
            ("1_element" -> hof"R 1"),
            ("plusclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x + y))"),
            ("plusinverse" -> hof"∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))"),
            ("multclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))")),
        Seq("inverse" -> hof"∀(a:i)∀(b:i) (R a ∧ R b -> (∃(x:i) ( (1 + (- a*b)) * x = 1 ) -> ∃(y:i) ( (1 + (- b*a)) * y = 1 )))")
    )
  ){
    decompose
    cut("ref", hof"∀ A A ⊆ A") left insert(subReflexivity)
    cut("antisym", hof"∀A∀B (( A ⊆ B & B ⊆ A ) -> ( A = B ))") left insert (subAntisymmetry)
    forget("extens")
    allL("multclosed",hov"a:i",hov"b:i")
    allL("plusinverse",le"a*b").forget
    allL("plusclosed",fot"1",le"-(a*b)").forget
    decompose
    impL("multclosed_0") left by {
      andR left by {trivial}
      trivial
    }
    impL("plusinverse") left by {trivial}
    andL("plusinverse")
    forget("multclosed_0")
    forget("plusinverse_0")
    impL("plusclosed") left by {
      andR left by {trivial}
      trivial
    }
    forget("1_element")
    cut("Rmultclosed", hof"∀x (R x → x ** R ⊆ R)") left insert(multClosed)
    forget("multclosed")
    allL("Rmultclosed",le"1+(-(a*b))").forget
  }

}

