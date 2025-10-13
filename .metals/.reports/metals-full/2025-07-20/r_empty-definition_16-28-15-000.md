error id: file:///C:/Users/Bernhard/Documents/TU%20Wien/Bachelorarbeit/github/gapt/ba.scala:`<none>`.
file:///C:/Users/Bernhard/Documents/TU%20Wien/Bachelorarbeit/github/gapt/ba.scala
empty definition using pc, found symbol in pc: `<none>`.
empty definition using semanticdb
empty definition using fallback
non-local guesses:

offset: 1115
uri: file:///C:/Users/Bernhard/Documents/TU%20Wien/Bachelorarbeit/github/gapt/ba.scala
text:
```scala
import gapt.expr._
import gapt.formats.babel.{Notation, Precedence}
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.proofs.Sequent
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._
import scala.languageFeature.implicitConversions

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
  
  ctx += hof"EXT = (∀(A:i>o)∀(B:i>o) ((A = B) <-> ∀(z:i) (A z <-> B z))"
  ctx += hof"P0 = @@R 0"
  ctx += hof"PNEUT = ∀(x:i) (R x → x + 0 = x)"
  ctx += hof"PCLOSED = ∀(x:i)∀(y:i) ((R x ∧ R y) → R(x + y))"
  ctx += hof"PASSOC = ∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) + z) = (x + (y + z)))"
  ctx += hof"PINV = ∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))"
  ctx += hof"PCOMM = ∀(x:i)∀(y:i) ((R x ∧ R y) → (x + y = y + x))"
  ctx += hof"MNEUTL = ∀(x:i) (R x → (x = 1 * x))"
  ctx += hof"MNEUTR = ∀(x:i) (R x → (x * 1 = x))"
  ctx += hof"MCLOSED = ∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"
  ctx += hof"MASSOC = ∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x * y) * z) = (x * (y * z)))"
  ctx += hof"DISTL = ∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → (x * (y + z)) = (x * y) + (x * z))"
  ctx += hof"DISTR = ∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) * z) = (x * z) + (y * z))"
  ctx += hof"RINGAX = P0 ∧ PNEUT ∧ PCLOSED ∧ PASSOC ∧ PINV ∧ PCOMM ∧ MNEUTL ∧ MNEUTR ∧ MCLOSED ∧ MASSOC ∧ DISTL ∧ DISTR"

  val axioms = 
       ("extens" -> hof"∀(A:i>o)∀(B:i>o) ((A = B) <-> ∀(z:i) (A z <-> B z))")
    +: ("0_element" -> hof"R 0")
    +: ("1_element" -> hof"R 1")
    +: ("plusneutral" -> hof"∀(x:i) (R x → x + 0 = x)")
    +: ("plusclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x + y))")
    +: ("plusassoc" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) + z) = (x + (y + z)))")
    +: ("plusinverse" -> hof"∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))")
    +: ("pluscomm" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → (x + y = y + x))")
    +: ("multrightneutral" -> hof"∀(x:i) (R x → (x * 1 = x))")
    +: ("multleftneutral" -> hof"∀(x:i) (R x → (x = 1 * x))")
    +: ("multclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))")
    +: ("multassoc" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x * y) * z) = (x * (y * z)))")
    +: ("leftdist" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → (x * (y + z)) = (x * y) + (x * z))")
    +: ("rightdist" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) * z) = (x * z) + (y * z))")
    +: Sequent()

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

  def setMultClosed = Lemma(
    Sequent(
      Seq("r-is-ring" -> hof"RINGAX",
          "multclosed" -> hof"∀(R:i>o)∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"), 
      Seq("setmultclosed" -> hof"∀R∀x (R x → x ** R ⊆ R)")
    )
  ){
    decompose
    unfold("**","⊆") in "setmultclosed_1"
    decompose
    allL("multclosed",hov"R:i>o",hov"x:i",hov"a:i").forget
    impL left by {
      andR left by {trivial}
      trivial
    }
    eql("setmultclosed_1_0_1","multclosed")
    trivial
  }

  def multClosed_inv = Lemma(
    Sequent(
      Seq(("multclosed" -> hof"∀(R:i>o)∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"),
          ("multassoc" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x * y) * z) = (x * (y * z)))"),
          ("multleftneutral" -> hof"∀(R:i>o)∀(x:i) (R x → (x = 1 * x))")), 
      Seq("Rmultclosed_inv" -> hof"∀x (∃y (R x ∧ R y ∧ x * y = 1) → R ⊆ x ** R)")
    )
  ){
    unfold("**","⊆") in "Rmultclosed_inv"
    decompose
    exR("Rmultclosed_inv_1_1",le"y*x_0").forget
    allL("multclosed",hov"R:i>o",hov"y:i",hov"x_0:i").forget
    andR left by {
      impL("multclosed") left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    allL("multassoc",hov"R:i>o",hov"x:i",hov"y:i",hov"x_0:i").forget
    impL("multassoc") left by {
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    allL("multleftneutral",hov"R:i>o",hov"x_0:i").forget
    impL("multleftneutral") left by {trivial}
    eql("multassoc","Rmultclosed_inv_1_1")
    eql("Rmultclosed_inv_0_1","Rmultclosed_inv_1_1")
    trivial
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
      Seq("setplusclosed" -> hof"R ⊕ R ⊆ R")
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

  def setPlusSubset = Lemma(
    Sequent(
      Seq("plusclosed" -> hof"∀(R:i>o)∀(x:i)∀(y:i) ((R x ∧ R y) → R(x + y))"),
      Seq("setplussubset" -> hof"∀(R:i>o)∀(S:i>o) (R ⊆ S → S ⊕ R ⊆ S)")
    )
  ){
    decompose
    unfold("⊕","⊆") in ("setplussubset_1","setplussubset_0")
    decompose
    allL("setplussubset_0",hov"b:i").forget
    impL("setplussubset_0") left by {trivial}
    allL("plusclosed",hov"S:i>o",hov"a:i",hov"b:i").forget
    impL("plusclosed") left by {
      andR("plusclosed")
      trivial 
      trivial
    }
    eql("setplussubset_1_0_1","plusclosed")
    trivial
  }

  def multleftDistributive = Lemma(
    Sequent(
        Seq("rightdist" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) * z) = (x * z) + (y * z))"),
        Seq("multleftdist" -> hof"∀a∀b∀R ((R a ∧ R b) → (a + b) ** R ⊆ a ** R ⊕ b ** R)")
    )
  ){
    decompose
    unfold("⊆","**","⊕") in "multleftdist_1"
    decompose
    allL("rightdist",hov"R:i>o",hov"a:i",hov"b:i",hov"a_0:i").forget
    impL("rightdist") left by {
      andR left by {
        andR left by {trivial}
        trivial
        }
      trivial
    }
    exR(le"a*a_0",le"b*a_0").forget
    andR left by{
      andR left by{
        exR(hov"a_0:i").forget
        andR
        trivial
        trivial
      }
      exR(hov"a_0:i").forget
      andR
      trivial
      trivial
    }
    eql("multleftdist_1_0_1","rightdist")
    trivial
  }

  def multsetAssoc = Lemma(
    Sequent(
        Seq("extens" -> hof"∀A∀B ((A = B) <-> ∀(z:i) (A z <-> B z))",
            "multassoc" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x * y) * z) = (x * (y * z)))"),
        Seq("multsetassoc" -> hof"∀R∀x∀y ((R x ∧ R y) → x ** (y ** R) = (x * y) ** R)")
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
      unfold("**") in ("multsetassoc_1_0","multsetassoc_1_1")
      decompose
      eql("multsetassoc_1_0_0_1","multsetassoc_1_0_1")
      exR(hov"a_0:i").forget
      andR left by {trivial}
      allL("multassoc",hov"R:i>o",hov"x:i",hov"y:i",hov"a_0:i").forget
      impL("multassoc") left by {
        andR left by {
          andR left by {trivial}
          trivial
        }
        trivial
      }
      eql("multassoc","multsetassoc_1_0_1")
      trivial
    }
    unfold("**") in "multsetassoc_1"
    decompose
    exR("multsetassoc_1_1",le"y * a").forget
    andR 
    exR(hov"a:i").forget
    andR left by {
      trivial
    }
    trivial
    allL("multassoc",hov"R:i>o",hov"x:i",hov"y:i",hov"a:i").forget
    impL("multassoc") left by {
      andR left by {
        andR left by {trivial} 
        trivial
        } 
      trivial
      }
    eql("multassoc","multsetassoc_1_0_1")
    trivial
  }

  def multleftSubset = Lemma(
    Sequent(
        Seq(),
        Seq("multleftsubset" -> hof"∀x∀R∀S (R ⊆ S → x ** R ⊆ x ** S)")
    )
  ){
    decompose
    unfold("**","⊆") in ("multleftsubset_0","multleftsubset_1")
    decompose
    allL("multleftsubset_0",hov"a:i").forget
    exR("multleftsubset_1_1",hov"a:i").forget
    impL("multleftsubset_0") left by {trivial}
    andR left by {trivial}
    trivial
  }
  
  def cancellationPlus = Lemma(
    Sequent(
      Seq(("0_element" -> hof"∀(R:i>o) R 0"),
          ("plusassoc" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) + z) = (x + (y + z)))"),
          ("plusneutral" -> hof"∀(R:i>o)∀(x:i) (R x → x + 0 = x)"),
          ("plusinverse" -> hof"∀(R:i>o)∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))"),
          ("pluscomm" -> hof"∀(R:i>o)∀(x:i)∀(y:i) ((R x ∧ R y) → (x + y = y + x))")),
      Seq("cancellation" -> hof"∀R∀x∀y∀z ((R x ∧ R y ∧ R z ∧ x + y = x + z) → y = z)")
    )
  ){
    decompose
    allL("0_element",hov"R:i>o").forget
    allL("plusneutral",hov"R:i>o",hov"y:i")
    impL("plusneutral_0") left by {trivial}
    allL("plusneutral",hov"R:i>o",hov"z:i")
    impL("plusneutral_1") left by {trivial}
    allL("pluscomm",hov"R:i>o",hov"y:i",fot"0")
    impL("pluscomm_0") left by {
      andR left by{trivial}
      trivial
    }
    eql("pluscomm_0","plusneutral_0")
    allL("pluscomm",hov"R:i>o",hov"z:i",fot"0")
    impL("pluscomm_1") left by {
      andR left by{trivial}
      trivial
    }
    eql("pluscomm_1","plusneutral_1")
    eql("plusneutral_0","cancellation_1")
    eql("plusneutral_1","cancellation_1")
    allL("plusinverse",hov"R:i>o",hov"x:i").forget
    impL("plusinverse") left by {trivial}
    andL
    allL("pluscomm",hov"R:i>o",hov"x:i",le"-x")
    impL("pluscomm_2") left by {
      andR left by {trivial}
      trivial
    }
    eql("pluscomm_2","plusinverse_0")
    eql("plusinverse_0","cancellation_1")
    allL("plusassoc",hov"R:i>o",le"-x",hov"x:i",hov"y:i")
    impL("plusassoc_0") left by {
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    allL("plusassoc",hov"R:i>o",le"-x",hov"x:i",hov"z:i")
    impL("plusassoc_1") left by {
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    eql("plusassoc_0","cancellation_1")
    eql("plusassoc_1","cancellation_1")
    eql("cancellation_0_1","cancellation_1").fromLeftToRight
    trivial
  }

  def absorption0left = Lemma(
    Sequent(
      Seq(("0_element" -> hof"∀(R:i>o) R 0"),
          ("plusassoc" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) + z) = (x + (y + z)))"),
          ("plusneutral" -> hof"∀(R:i>o)∀(x:i) (R x → x + 0 = x)"),
          ("plusinverse" -> hof"∀(R:i>o)∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))"),
          ("pluscomm" -> hof"∀(R:i>o)∀(x:i)∀(y:i) ((R x ∧ R y) → (x + y = y + x))"),
          ("multclosed" -> hof"∀(R:i>o)∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"),
          ("leftdist" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → (x * (y + z)) = (x * y) + (x * z))")),
      Seq("absorption0left" -> hof"∀R∀x (R x → x*0 = 0)")
    )
  ){
    decompose
    cut("cancellation",hof"∀R∀x∀y∀z ((R x ∧ R y ∧ R z ∧ x + y = x + z) → y = z)") left insert (cancellationPlus)
    allL("0_element",hov"R:i>o").forget
    allL("plusneutral",hov"R:i>o",fot"0")
    impL("plusneutral_0") left by {trivial}
    allL("leftdist",hov"R:i>o",hov"x:i",fot"0",fot"0").forget
    impL("leftdist") left by{
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    eql("plusneutral_0","leftdist").fromLeftToRight
    allL("cancellation",hov"R:i>o",le"x*0",fot"0",le"x*0").forget
    allL("multclosed",hov"R:i>o",hov"x:i",fot"0").forget
    impL("multclosed") left by{
      andR left by {trivial}
      trivial
    }
    allL("plusneutral",hov"R:i>o",le"x*0").forget
    impL("plusneutral") left by {trivial}
    eql("plusneutral","leftdist").yielding(hof"x*0+0=x*0+x*0")
    impL("cancellation") left by{
      andR left by {
        andR left by {
          andR left by {trivial}
          trivial
        }
        trivial
      }
      trivial
    }
    eql("cancellation","absorption0left_1").fromRightToLeft
    trivial
  }

  def absorption0right = Lemma(
    Sequent(
      Seq(("0_element" -> hof"∀(R:i>o) R 0"),
          ("plusassoc" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) + z) = (x + (y + z)))"),
          ("plusneutral" -> hof"∀(R:i>o)∀(x:i) (R x → x + 0 = x)"),
          ("plusinverse" -> hof"∀(R:i>o)∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))"),
          ("pluscomm" -> hof"∀(R:i>o)∀(x:i)∀(y:i) ((R x ∧ R y) → (x + y = y + x))"),
          ("multclosed" -> hof"∀(R:i>o)∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"),
          ("leftdist" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → (x * (y + z)) = (x * y) + (x * z))"),
          ("rightdist" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) * z) = (x * z) + (y * z))")),
      Seq("absorption0right" -> hof"∀R∀x (R x → 0*x = 0)")
    )
  ){
    decompose
    cut("cancellation",hof"∀R∀x∀y∀z ((R x ∧ R y ∧ R z ∧ x + y = x + z) → y = z)") left insert (cancellationPlus)
    allL("0_element",hov"R:i>o").forget
    allL("plusneutral",hov"R:i>o",fot"0")
    impL("plusneutral_0") left by {trivial}
    allL("rightdist",hov"R:i>o",fot"0",fot"0",hov"x:i").forget
    impL("rightdist") left by{
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    eql("plusneutral_0","rightdist").fromLeftToRight
    allL("cancellation",hov"R:i>o",le"0*x",fot"0",le"0*x").forget
    allL("multclosed",hov"R:i>o",fot"0",hov"x:i").forget
    impL("multclosed") left by{
      andR left by {trivial}
      trivial
    }
    allL("plusneutral",hov"R:i>o",le"0*x").forget
    impL("plusneutral") left by {trivial}
    eql("plusneutral","rightdist").yielding(hof"0*x+0=0*x+0*x")
    impL("cancellation") left by{
      andR left by {
        andR left by {
          andR left by {trivial}
          trivial
        }
        trivial
      }
      trivial
    }
    eql("cancellation","absorption0right_1").fromRightToLeft
    trivial
  }

  def multMinusleft = Lemma(
    Sequent(
      Seq(("0_element" -> hof"∀(R:i>o) R 0"),
          ("plusassoc" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) + z) = (x + (y + z)))"),
          ("plusneutral" -> hof"∀(R:i>o)∀(x:i) (R x → x + 0 = x)"),
          ("plusinverse" -> hof"∀(R:i>o)∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))"),
          ("pluscomm" -> hof"∀(R:i>o)∀(x:i)∀(y:i) ((R x ∧ R y) → (x + y = y + x))"),
          ("multclosed" -> hof"∀(R:i>o)∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"),
          ("leftdist" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → (x * (y + z)) = (x * y) + (x * z))"),
          ("cancellation" -> hof"∀R∀x∀y∀z ((R x ∧ R y ∧ R z ∧ x + y = x + z) → y = z)")),
      Seq("multminus" -> hof"∀R∀x∀y ((R x ∧ R y) → x * (-y) = -(x*y) )")
    )
  ){
    cut("absorption0left",hof"∀R∀x (R x → x*0 = 0)") left insert (absorption0left)
    // cut("cancellation",hof"∀R∀x∀y∀z ((R x ∧ R y ∧ R z ∧ x + y = x + z) → y = z)") left insert (cancellationPlus)
    forget("0_element","plusassoc","plusneutral","pluscomm")
    decompose
    allL("plusinverse",hov"R:i>o",le"x*y")
    allL("multclosed",hov"R:i>o",hov"x:i",hov"y:i")
    impL("multclosed_0") left by {
      andR left by {trivial}
      trivial
    }
    impL("plusinverse_0") left by {trivial}
    andL
    allL("leftdist",hov"R:i>o",hov"x:i",hov"y:i",le"-y").forget
    allL("plusinverse",hov"R:i>o",hov"y:i")
    impL("plusinverse_1") left by {trivial}
    andL
    impL("leftdist") left by{
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    eql("plusinverse_1_0","leftdist")
    allL("absorption0left",hov"R:i>o",hov"x:i").forget
    impL("absorption0left") left by {trivial}
    eql("absorption0left","leftdist").fromLeftToRight
    eql("plusinverse_0_0","leftdist").fromRightToLeft
    allL("cancellation",hov"R:i>o",le"x*y",le"x*(-y)",le"-(x*y)").forget
    allL("multclosed",hov"R:i>o",hov"x:i",le"-y")
    impL("multclosed_1") left by {
      andR left by {trivial}
      trivial
    }
    impL("cancellation") left by {
      andR left by {
        andR left by {
          andR left by {
            trivial
            }
          trivial
        }
        trivial
      }
      eql("leftdist","cancellation").fromLeftToRight
      trivial
    }
    trivial
  }

  def multMinusright = Lemma(
    Sequent(
      Seq(("0_element" -> hof"∀(R:i>o) R 0"),
          ("plusassoc" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) + z) = (x + (y + z)))"),
          ("plusneutral" -> hof"∀(R:i>o)∀(x:i) (R x → x + 0 = x)"),
          ("plusinverse" -> hof"∀(R:i>o)∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))"),
          ("pluscomm" -> hof"∀(R:i>o)∀(x:i)∀(y:i) ((R x ∧ R y) → (x + y = y + x))"),
          ("multclosed" -> hof"∀(R:i>o)∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"),
          ("leftdist" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → (x * (y + z)) = (x * y) + (x * z))"),
          ("rightdist" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) * z) = (x * z) + (y * z))"),
          ("cancellation" -> hof"∀R∀x∀y∀z ((R x ∧ R y ∧ R z ∧ x + y = x + z) → y = z)")),
      Seq("multminusright" -> hof"∀R∀x∀y ((R x ∧ R y) → (-x) * y = -(x*y) )")
    )
  ){
    cut("absorption0right",hof"∀R∀x (R x → 0*x = 0)") left insert (absorption0right)
    // cut("cancellation",hof"∀R∀x∀y∀z ((R x ∧ R y ∧ R z ∧ x + y = x + z) → y = z)") left insert (cancellationPlus)
    forget("0_element","plusassoc","plusneutral","pluscomm","leftdist")
    decompose
    allL("plusinverse",hov"R:i>o",le"x*y")
    allL("multclosed",hov"R:i>o",hov"x:i",hov"y:i")
    impL("multclosed_0") left by {
      andR left by {trivial}
      trivial
    }
    impL("plusinverse_0") left by {trivial}
    andL
    allL("rightdist",hov"R:i>o",hov"x:i",le"-x",hov"y:i").forget
    allL("plusinverse",hov"R:i>o",hov"x:i")
    impL("plusinverse_1") left by {trivial}
    andL
    impL("rightdist") left by{
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    eql("plusinverse_1_0","rightdist")
    allL("absorption0right",hov"R:i>o",hov"y:i").forget
    impL("absorption0right") left by {trivial}
    eql("absorption0right","rightdist").fromLeftToRight
    eql("plusinverse_0_0","rightdist").fromRightToLeft
    allL("cancellation",hov"R:i>o",le"x*y",le"-(x*y)",le"(-x)*y").forget
    allL("multclosed",hov"R:i>o",le"-x",hov"y:i")
    impL("multclosed_1") left by {
      andR left by {trivial}
      trivial
    }
    impL("cancellation") left by {
      andR left by {
        andR left by {
          andR left by {
            trivial
            }
          trivial
        }
        trivial
      }
      eql("rightdist","cancellation").fromLeftToRight
      trivial
    }
    eql("cancellation","multminusright_1").fromLeftToRight
    trivial
  }

  def setMult1_equal = Lemma(
    Sequent(
      Seq(("extens" -> hof"∀A∀B ((A = B) <-> ∀(z:i) (A z <-> B z))"),
          ("multleftneutral" -> hof"∀(R:i>o)∀(x:i) (R x → (x = 1 * x))")),
      Seq("setmult1" -> hof"∀R R = 1**R")
    )
  ){
    decompose
    allL("extens",hov"R:i>o",le"1**R").forget
    andL
    impL("extens_1") left by {
      forget("setmult1","extens_0")
      decompose
      andR left by {
        impR
        allL("multleftneutral",hov"R:i>o",hov"z:i").forget
        impL("multleftneutral") left by {trivial}
        eql("multleftneutral","extens_1_1")
        unfold("**") in ("extens_1_1")
        exR(hov"z:i").forget
        andR left by {trivial}
        trivial
      }
      impR
      unfold("**") in ("extens_1_0")
      decompose
      allL("multleftneutral",hov"R:i>o",hov"a:i").forget
      impL("multleftneutral") left by {trivial}
      eql("multleftneutral","extens_1_0_1").fromRightToLeft
      eql("extens_1_0_1","extens_1_0_0")
      trivial
    }
    trivial
  }

  def inverse = Lemma(
    Sequent(
        Seq(("extens" -> hof"∀A∀B ((A = B) <-> ∀(z:i) (A z <-> B z))"),
            ("1_element" -> hof"∀(R:i>o) R 1"),
            ("plusclosed" -> hof"∀(R:i>o)∀(x:i)∀(y:i) ((R x ∧ R y) → R(x + y))"),
            ("plusassoc" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) + z) = (x + (y + z)))"),
            ("plusneutral" -> hof"∀(R:i>o)∀(x:i) (R x → x + 0 = x)"),
            ("plusinverse" -> hof"∀(R:i>o)∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))"),
            ("pluscomm" -> hof"∀(R:i>o)∀(x:i)∀(y:i) ((R x ∧ R y) → (x + y = y + x))"),
            ("multclosed" -> hof"∀(R:i>o)∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"),
            ("multassoc" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x * y) * z) = (x * (y * z)))"),
            ("multleftneutral" -> hof"∀(R:i>o)∀(x:i) (R x → (x = 1 * x))"),
            ("multrightneutral" -> hof"∀(R:i>o)∀(x:i) (R x → (x * 1 = x))"),
            ("leftdist" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → (x * (y + z)) = (x * y) + (x * z))"),
            ("rightdist" -> hof"∀(R:i>o)∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) * z) = (x * z) + (y * z))"),
            ("multminusleft" -> hof"∀R∀x∀y ((R x ∧ R y) → x * (-y) = -(x*y) )"),
            ("multminusright" -> hof"∀R∀x∀y ((R x ∧ R y) → (-x) * y = -(x*y) )")),
        Seq("inverse" -> hof"∀(a:i)∀(b:i) (R a ∧ R b -> (∃(x:i) (R x ∧ (1 + (- a*b)) * x = 1 ) -> ∃(y:i) ( R y ∧ (1 + (- b*a)) * y = 1 )))")
    )
  ){
    decompose
    allL("multclosed",hov"R:i>o",hov"a:i",hov"b:i")
    allL("plusinverse",hov"R:i>o",le"a*b")
    allL("plusclosed",hov"R:i>o",fot"1",le"-(a*b)")
    allL("1_element",hov"R:i>o").forget
    decompose
    impL("multclosed_0") left by {
      andR left by {trivial}
      trivial
    }
    impL("plusinverse_0") left by {trivial}
    andL("plusinverse_0")
    forget("plusinverse_0_0")
    impL("plusclosed_0") left by {
      andR left by {trivial}
      trivial
    }
    cut("multclosed_inv",hof"∀x (∃y (R x ∧ R y ∧ x * y = 1) → R ⊆ x ** R)") left insert (multClosed_inv)
    allL("multclosed_inv",le"1+(-(a*b))").forget
    impL("multclosed_inv") left by {
      exR("multclosed_inv",hov"x:i").forget
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    forget("inverse_1_0_1")
    cut("multleftsubset", hof"∀x∀R∀S (R ⊆ S → x ** R ⊆ x ** S)") left insert (multleftSubset)
    allL("multleftsubset",hov"b:i",hov"R:i>o",le"(1+(-(a*b)))**R")
    impL("multleftsubset_0") left by {trivial}
    cut("multsetassoc",hof"∀R∀x∀y ((R x ∧ R y) → x ** (y ** R) = (x * y) ** R)") left insert (multsetAssoc)
    allL("multsetassoc",hov"R:i>o",hov"b:i",le"(1+(-(a*b)))")
    impL("multsetassoc_0") left by {
      andR left by {trivial}
      trivial
    }
    eql("multsetassoc_0","multleftsubset_0")
    forget("multsetassoc_0","multclosed_inv","inverse_1_0_0")
    allL("leftdist",hov"R:i>o",hov"b:i",fot"1",le"-(a*b)").forget
    impL("leftdist") left by {
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    allL("multrightneutral",hov"R:i>o",hov"b:i").forget
    impL("multrightneutral") left by {trivial}
    eql("multrightneutral","leftdist").fromLeftToRight
    forget("multrightneutral")
    // cut("multminusleft",hof"∀R∀x∀y ((R x ∧ R y) → x * (-y) = -(x*y) )") left insert (multminusleft)
    allL("multminusleft",hov"R:i>o",hov"b:i",le"a*b").forget
    impL("multminusleft") left by {
      andR left by {trivial}
      trivial
    }
    eql("multminusleft","leftdist")
    forget("multminusleft")
    allL("multassoc",hov"R:i>o",hov"b:i",hov"a:i",hov"b:i").forget
    impL("multassoc") left by {
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    eql("multassoc","leftdist")
    allL("rightdist",hov"R:i>o",fot"1",le"-(b*a)",hov"b:i")
    allL("multclosed",hov"R:i>o",hov"b:i",hov"a:i")
    impL("multclosed_1") left by {
      andR left by {trivial}
      trivial
    }
    allL("plusinverse",hov"R:i>o",le"b*a")
    impL("plusinverse_1") left by {trivial}
    andL("plusinverse_1")
    impL("rightdist_0") left by {
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    allL("multleftneutral",hov"R:i>o",hov"b:i")
    impL("multleftneutral_0") left by {trivial}
    eql("multleftneutral_0","leftdist").yielding(hof"b*(1+(-(a*b)))=1*b+(-(b*a*b))")
    // cut("multminusright",hof"∀R∀x∀y ((R x ∧ R y) → x * (-y) = -(x*y) )") left insert (multminusright)
    forget("plusinverse","multassoc","multleftneutral_0")
    allL("multminusright",hov"R:i>o",le"b*a",hov"b:i").forget
    impL("multminusright") left by {
      andR left by {trivial}
      trivial
    }
    eql("multminusright","rightdist_0")
    forget("multminusright")
    eql("rightdist_0","leftdist").fromRightToLeft
    forget("rightdist_0")
    eql("leftdist","multleftsubset_0")
    forget("leftdist")
    allL("multsetassoc",hov"R:i>o",le"1+(-(b*a))",hov"b:i")
    allL("plusclosed",hov"R:i>o",fot"1",le"-(b*a)")
    impL("plusclosed_1") left by {
      andR left by {trivial}
      trivial
    }
    impL("multsetassoc_0") left by {
      andR left by {trivial}
      trivial
    }
    cut("setmultclosed",hof"∀R∀x (R x → x ** R ⊆ R)") left insert (setMultClosed)
    forget("multclosed")
    allL("setmultclosed",hov"R:i>o",hov"b:i")
    impL("setmultclosed_0") left by {trivial}
    allL("multleftsubset",le"1+(-(b*a))",le"b**R",hov"R:i>o")
    impL("multleftsubset_1") left by {trivial}
    eql("multsetassoc_0","multleftsubset_1")
    allL("setmultclosed",hov"R:i>o",hov"a:i")
    impL("setmultclosed_1") left by {trivial}
    allL("multleftsubset",hov"b:i",le"a**R",hov"R:i>o").forget
    impL("multleftsubset") left by {trivial}
    allL("multsetassoc",hov"R:i>o",hov"b:i",hov"a:i").forget
    impL("multsetassoc") left by {
      andR left by {trivial}
      trivial
    }
    cut("subtrans",hof"∀A∀B∀C ( ( A ⊆ B ∧ B ⊆ C ) -> ( A ⊆ C ) )") left insert (subTransitivity)
    allL("subtrans",le"b**R",le"((1+(-(b*a)))*b)**R",le"(1+(-(b*a)))**R")
    impL("subtrans_0") left by {
      andR left by {trivial}
      trivial
    }
    allL("subtrans",le"b**(a**R)",le"b**R",le"(1+(-(b*a)))**R")
    impL("subtrans_1") left by {
      andR left by {trivial}
      trivial
    }
    forget("subtrans_0","multleftsubset_1","setmultclosed_0","setmultclosed_1","multsetassoc_0","multleftsubset_0","multleftsubset")
    eql("multsetassoc","subtrans_1")
    forget("multsetassoc")
    cut("multsetdist",hof"∀a∀b∀R ((R a ∧ R b) → (a + b) ** R ⊆ a ** R ⊕ b ** R)") left insert (multleftDistributive)
    allL("multsetdist",le"1+(-(b*a))",le"b*a",hov"R:i>o").forget
    impL("multsetdist") left by {
      andR left by {trivial}
      trivial
    }
    cut("setmult1",hof"∀R R = 1**R") left insert (setMult1_equal)
    allL("setmult1",hov"R:i>o").forget
    forget("extens","multleftneutral")
    allL("plusneutral",hov"R:i>o",fot"1").forget
    impL("plusneutral") left by {trivial}
    eql("plusneutral","setmult1")
    forget("plusneutral")
    allL("pluscomm",hov"R:i>o",le"b*a",le"-(b*a)").forget
    impL("pluscomm") left by {
      andR left by {trivial}
      trivial
    }
    eql("plusinverse_1_0","pluscomm")
    eql("pluscomm","setmult1")
    allL("plusassoc",hov"R:i>o",fot"1",le"-(b*a)",le"b*a").forget
    impL("plusassoc") left by {
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    eql("plusassoc","setmult1")
    forget("pluscomm","plusassoc","plusinverse_1_0","rightdist")
    eql("setmult1","multsetdist").fromRightToLeft
    forget("setmult1")
    cut("setplussubset",hof"∀(R:i>o)∀(S:i>o) (R ⊆ S → S ⊕ R ⊆ S)") left insert (setPlusSubset)
    forget("plusclosed")
    allL("setplussubset",le"(b*a)**R",le"(1+(-(b*a)))**R").forget
    impL("setplussubset") left by {trivial}
    allL("subtrans",hov"R:i>o",le"(1 + (-)(b * a)) ** R ⊕ b * a ** R",le"(1 + (-)(b * a)) ** R").forget
    impL("subtrans") left by {
      andR left by {trivial}
      trivial
    }
    forget("setplussubset","multsetdist","subtrans_1","setmultclosed")
    unfold("⊆") in "subtrans"
    allL("subtrans",fot"1").forget
    impL("subtrans") left by {trivial}
    unfold("**") in "subtrans"
    exL("subtrans",hov"y:i")
    decompose
    exR(hov"y:i").forget
    andR left by {trivial}
    eql("subtrans_1","inverse_1_1").fromRightToLeft
    trivial
  }
}


```


#### Short summary: 

empty definition using pc, found symbol in pc: `<none>`.