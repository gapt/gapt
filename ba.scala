import gapt.expr._
import gapt.formats.babel.{Notation, Precedence}
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.proofs.Sequent
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._
import scala.languageFeature.implicitConversions

import gapt.proofs.lk.rules.CutRule

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
  
  // ctx += hof"EXT = (∀(A:i>o)∀(B:i>o) ((A = B) <-> ∀(z:i) (A z <-> B z)))"
  // ctx += hof"P0 = (R 0)"
  // ctx += hof"PNEUT = (∀(x:i) (R x → x + 0 = x))"
  // ctx += hof"PCLOSED = (∀(x:i)∀(y:i) ((R x ∧ R y) → R(x + y)))"
  // ctx += hof"PASSOC = (∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) + z) = (x + (y + z))))"
  // ctx += hof"PINV = (∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x))))"
  // ctx += hof"PCOMM = (∀(x:i)∀(y:i) ((R x ∧ R y) → (x + y = y + x)))"
  // ctx += hof"MNEUTL = (∀(x:i) (R x → (x = 1 * x)))"
  // ctx += hof"MNEUTR = (∀(x:i) (R x → (x * 1 = x)))"
  // ctx += hof"MCLOSED = (∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y)))"
  // ctx += hof"MASSOC = (∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x * y) * z) = (x * (y * z))))"
  // ctx += hof"DISTL = (∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → (x * (y + z)) = (x * y) + (x * z)))"
  // ctx += hof"DISTR = (∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) * z) = (x * z) + (y * z)))"
  // ctx += hof"RINGAX = (P0 ∧ PNEUT ∧ PCLOSED ∧ PASSOC ∧ PINV ∧ PCOMM ∧ MNEUTL ∧ MNEUTR ∧ MCLOSED ∧ MASSOC ∧ DISTL ∧ DISTR)"
  
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
          "multclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"), 
      Seq("setmultclosed" -> hof"∀x (R x → x ** R ⊆ R)")
    )
  ){
    decompose
    unfold("**","⊆") in "setmultclosed_1"
    decompose
    allL("multclosed",hov"x:i",hov"a:i").forget
    impL left by {
      andR left by {trivial}
      trivial
    }
    eql("setmultclosed_1_0_1","multclosed")
    trivial
  }

  def multClosed_Inv = Lemma(
    Sequent(
      Seq(("multclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"),
          ("multassoc" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x * y) * z) = (x * (y * z)))"),
          ("multleftneutral" -> hof"∀(x:i) (R x → (x = 1 * x))")), 
      Seq("Rmultclosed_inv" -> hof"∀x (∃y (R x ∧ R y ∧ x * y = 1) → R ⊆ x ** R)")
    )
  ){
    unfold("**","⊆") in "Rmultclosed_inv"
    decompose
    exR("Rmultclosed_inv_1_1",le"y*x_0").forget
    allL("multclosed",hov"y:i",hov"x_0:i").forget
    andR left by {
      impL("multclosed") left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    allL("multassoc",hov"x:i",hov"y:i",hov"x_0:i").forget
    impL("multassoc") left by {
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    allL("multleftneutral",hov"x_0:i").forget
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
      Seq(("plusclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x + y))"),
          ("leftdist" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → (x * (y + z)) = (x * y) + (x * z))")),
      Seq("setplussubset" -> hof"∀x∀y (R y → x**R ⊆ y**R → y**R ⊕ x**R ⊆ y**R)")
    )
  ){
    decompose
    unfold("⊕","⊆") in ("setplussubset_1_0","setplussubset_1_1")
    decompose
    allL("setplussubset_1_0",hov"b:i").forget
    impL("setplussubset_1_0") left by {trivial}
    forget("setplussubset_1_1_0_0_1")
    unfold("**") in ("setplussubset_1_1_0_0_0","setplussubset_1_0","setplussubset_1_1_1")
    decompose
    eql("setplussubset_1_0_1","setplussubset_1_1_0_1")
    forget("setplussubset_1_0_1")
    eql("setplussubset_1_1_0_0_0_1","setplussubset_1_1_0_1")
    forget("setplussubset_1_1_0_0_0_1")
    allL("leftdist",hov"y:i",hov"a_0:i",hov"a_1:i").forget
    impL("leftdist") left by {
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    forget("setplussubset_0")
    eql("leftdist","setplussubset_1_1_0_1")
    forget("leftdist")
    allL("plusclosed",hov"a_0:i",hov"a_1:i").forget
    impL("plusclosed") left by {
      andR("plusclosed") left by {trivial}
      trivial
    }
    forget("setplussubset_1_0_0","setplussubset_1_1_0_0_0_0")
    exR("setplussubset_1_1_1",le"a_0 + a_1")
    andR left by {trivial}
    trivial
  }

  def multleftDistributive = Lemma(
    Sequent(
        Seq("rightdist" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) * z) = (x * z) + (y * z))"),
        Seq("multleftdist" -> hof"∀a∀b ((R a ∧ R b) → (a + b) ** R ⊆ a ** R ⊕ b ** R)")
    )
  ){
    decompose
    unfold("⊆","**","⊕") in "multleftdist_1"
    decompose
    allL("rightdist",hov"a:i",hov"b:i",hov"a_0:i").forget
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
            "multassoc" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x * y) * z) = (x * (y * z)))"),
        Seq("multsetassoc" -> hof"∀x∀y ((R x ∧ R y) → x ** (y ** R) = (x * y) ** R)")
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
      allL("multassoc",hov"x:i",hov"y:i",hov"a_0:i").forget
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
    allL("multassoc",hov"x:i",hov"y:i",hov"a:i").forget
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
        Seq("multleftsubset" -> hof"∀x∀A∀B (A ⊆ B → x ** A ⊆ x ** B)")
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
      Seq(("0_element" -> hof"R 0"),
          ("plusassoc" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) + z) = (x + (y + z)))"),
          ("plusneutral" -> hof"∀(x:i) (R x → x + 0 = x)"),
          ("plusinverse" -> hof"∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))"),
          ("pluscomm" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → (x + y = y + x))")),
      Seq("cancellation" -> hof"∀x∀y∀z ((R x ∧ R y ∧ R z ∧ x + y = x + z) → y = z)")
    )
  ){
    decompose
    allL("plusneutral",hov"y:i")
    impL("plusneutral_0") left by {trivial}
    allL("plusneutral",hov"z:i")
    impL("plusneutral_1") left by {trivial}
    allL("pluscomm",hov"y:i",fot"0")
    impL("pluscomm_0") left by {
      andR left by{trivial}
      trivial
    }
    eql("pluscomm_0","plusneutral_0")
    allL("pluscomm",hov"z:i",fot"0")
    impL("pluscomm_1") left by {
      andR left by{trivial}
      trivial
    }
    eql("pluscomm_1","plusneutral_1")
    eql("plusneutral_0","cancellation_1")
    eql("plusneutral_1","cancellation_1")
    allL("plusinverse",hov"x:i").forget
    impL("plusinverse") left by {trivial}
    andL
    allL("pluscomm",hov"x:i",le"-x")
    impL("pluscomm_2") left by {
      andR left by {trivial}
      trivial
    }
    eql("pluscomm_2","plusinverse_0")
    eql("plusinverse_0","cancellation_1")
    allL("plusassoc",le"-x",hov"x:i",hov"y:i")
    impL("plusassoc_0") left by {
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    allL("plusassoc",le"-x",hov"x:i",hov"z:i")
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

  def absorption0Left = Lemma(
    Sequent(
      Seq(("0_element" -> hof"R 0"),
          ("plusassoc" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) + z) = (x + (y + z)))"),
          ("plusneutral" -> hof"∀(x:i) (R x → x + 0 = x)"),
          ("plusinverse" -> hof"∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))"),
          ("pluscomm" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → (x + y = y + x))"),
          ("multclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"),
          ("leftdist" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → (x * (y + z)) = (x * y) + (x * z))"),
          ("cancellation" -> hof"∀x∀y∀z ((R x ∧ R y ∧ R z ∧ x + y = x + z) → y = z)")),
      Seq("absorption0left" -> hof"∀x (R x → x*0 = 0)")
    )
  ){
    decompose
    allL("plusneutral",fot"0")
    impL("plusneutral_0") left by {trivial}
    allL("leftdist",hov"x:i",fot"0",fot"0").forget
    impL("leftdist") left by{
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    eql("plusneutral_0","leftdist").fromLeftToRight
    allL("cancellation",le"x*0",fot"0",le"x*0").forget
    allL("multclosed",hov"x:i",fot"0").forget
    impL("multclosed") left by{
      andR left by {trivial}
      trivial
    }
    allL("plusneutral",le"x*0").forget
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

  def absorption0Right = Lemma(
    Sequent(
      Seq(("0_element" -> hof"R 0"),
          ("plusassoc" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) + z) = (x + (y + z)))"),
          ("plusneutral" -> hof"∀(x:i) (R x → x + 0 = x)"),
          ("plusinverse" -> hof"∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))"),
          ("pluscomm" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → (x + y = y + x))"),
          ("multclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"),
          ("leftdist" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → (x * (y + z)) = (x * y) + (x * z))"),
          ("rightdist" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) * z) = (x * z) + (y * z))"),
          ("cancellation" -> hof"∀x∀y∀z ((R x ∧ R y ∧ R z ∧ x + y = x + z) → y = z)")),
      Seq("absorption0right" -> hof"∀x (R x → 0*x = 0)")
    )
  ){
    decompose
    allL("plusneutral",fot"0")
    impL("plusneutral_0") left by {trivial}
    allL("rightdist",fot"0",fot"0",hov"x:i").forget
    impL("rightdist") left by{
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    eql("plusneutral_0","rightdist").fromLeftToRight
    allL("cancellation",le"0*x",fot"0",le"0*x").forget
    allL("multclosed",fot"0",hov"x:i").forget
    impL("multclosed") left by{
      andR left by {trivial}
      trivial
    }
    allL("plusneutral",le"0*x").forget
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

  def multMinusRight = Lemma(
    Sequent(
      Seq(("plusinverse" -> hof"∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))"),
          ("multclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"),
          ("leftdist" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → (x * (y + z)) = (x * y) + (x * z))"),
          ("cancellation" -> hof"∀x∀y∀z ((R x ∧ R y ∧ R z ∧ x + y = x + z) → y = z)"),
          ("absorption0left" -> hof"∀x (R x → x*0 = 0)")),
      Seq("multminusright" -> hof"∀x∀y ((R x ∧ R y) → x * (-y) = -(x*y) )")
    )
  ){
    decompose
    allL("plusinverse",le"x*y")
    allL("multclosed",hov"x:i",hov"y:i")
    impL("multclosed_0") left by {
      andR left by {trivial}
      trivial
    }
    impL("plusinverse_0") left by {trivial}
    andL
    allL("leftdist",hov"x:i",hov"y:i",le"-y").forget
    allL("plusinverse",hov"y:i")
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
    allL("absorption0left",hov"x:i").forget
    impL("absorption0left") left by {trivial}
    eql("absorption0left","leftdist").fromLeftToRight
    eql("plusinverse_0_0","leftdist").fromRightToLeft
    allL("cancellation",le"x*y",le"x*(-y)",le"-(x*y)").forget
    allL("multclosed",hov"x:i",le"-y")
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

  def multMinusLeft = Lemma(
    Sequent(
      Seq(("plusinverse" -> hof"∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))"),
          ("multclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"),
          ("rightdist" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) * z) = (x * z) + (y * z))"),
          ("cancellation" -> hof"∀x∀y∀z ((R x ∧ R y ∧ R z ∧ x + y = x + z) → y = z)"),
          ("absorption0right" -> hof"∀x (R x → 0 * x = 0)")),
      Seq("multminusleft" -> hof"∀x∀y ((R x ∧ R y) → (-x) * y = -(x * y) )")
    )
  ){
    decompose
    allL("plusinverse",le"x*y")
    allL("multclosed",hov"x:i",hov"y:i")
    impL("multclosed_0") left by {
      andR left by {trivial}
      trivial
    }
    impL("plusinverse_0") left by {trivial}
    andL
    allL("rightdist",hov"x:i",le"-x",hov"y:i").forget
    allL("plusinverse",hov"x:i")
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
    allL("absorption0right",hov"y:i").forget
    impL("absorption0right") left by {trivial}
    eql("absorption0right","rightdist").fromLeftToRight
    eql("plusinverse_0_0","rightdist").fromRightToLeft
    allL("cancellation",le"x*y",le"-(x*y)",le"(-x)*y").forget
    allL("multclosed",le"-x",hov"y:i")
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
    eql("cancellation","multminusleft_1").fromLeftToRight
    trivial
  }

  def setMult1_Equal = Lemma(
    Sequent(
      Seq(("extens" -> hof"∀A∀B ((A = B) <-> ∀(z:i) (A z <-> B z))"),
          ("multleftneutral" -> hof"∀(x:i) (R x → (x = 1 * x))")),
      Seq("setmult1equ" -> hof"R = 1**R")
    )
  ){
    decompose
    allL("extens",hov"R:i>o",le"1**R").forget
    andL
    impL("extens_1") left by {
      forget("setmult1equ","extens_0")
      decompose
      andR left by {
        impR
        allL("multleftneutral",hov"z:i").forget
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
      allL("multleftneutral",hov"a:i").forget
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
            ("0_element" -> hof"R 0"),
            ("1_element" -> hof"R 1"),
            ("plusclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x + y))"),
            ("plusassoc" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) + z) = (x + (y + z)))"),
            ("plusneutral" -> hof"∀(x:i) (R x → x + 0 = x)"),
            ("plusinverse" -> hof"∀(x:i) (R x → (x + (- x) = 0 ∧ R (-x)))"),
            ("pluscomm" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → (x + y = y + x))"),
            ("multclosed" -> hof"∀(x:i)∀(y:i) ((R x ∧ R y) → R(x * y))"),
            ("multassoc" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x * y) * z) = (x * (y * z)))"),
            ("multleftneutral" -> hof"∀(x:i) (R x → (x = 1 * x))"),
            ("multrightneutral" -> hof"∀(x:i) (R x → (x * 1 = x))"),
            ("leftdist" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → (x * (y + z)) = (x * y) + (x * z))"),
            ("rightdist" -> hof"∀(x:i)∀(y:i)∀(z:i) ((R x ∧ R y ∧ R z) → ((x + y) * z) = (x * z) + (y * z))")),
        Seq("inverse" -> hof"∀(a:i)∀(b:i) (R a ∧ R b -> (∃(x:i) (R x ∧ (1 + (- a*b)) * x = 1 ) -> ∃(y:i) ( R y ∧ (1 + (- b*a)) * y = 1 )))")
    )
  ){
    cut("cancellation",hof"∀x∀y∀z ((R x ∧ R y ∧ R z ∧ x + y = x + z) → y = z)") left insert (cancellationPlus)
    cut("absorption0right",hof"∀x (R x → 0 * x = 0)") left insert (absorption0Right)
    cut("absorption0left",hof"∀x (R x → x * 0 = 0)") left insert (absorption0Left)
    decompose
    allL("multclosed",hov"a:i",hov"b:i")
    allL("plusinverse",le"a*b")
    allL("plusclosed",fot"1",le"-(a*b)")
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
    cut("multclosed_inv",hof"∀x (∃y (R x ∧ R y ∧ x * y = 1) → R ⊆ x ** R)") left insert (multClosed_Inv)
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
    cut("multleftsubset", hof"∀x∀A∀B (A ⊆ B → x ** A ⊆ x ** B)") left insert (multleftSubset)
    allL("multleftsubset",hov"b:i",hov"R:i>o",le"(1+(-(a*b)))**R")
    impL("multleftsubset_0") left by {trivial}
    cut("multsetassoc",hof"∀x∀y ((R x ∧ R y) → x ** (y ** R) = (x * y) ** R)") left insert (multsetAssoc)
    allL("multsetassoc",hov"b:i",le"(1+(-(a*b)))")
    impL("multsetassoc_0") left by {
      andR left by {trivial}
      trivial
    }
    eql("multsetassoc_0","multleftsubset_0")
    forget("multsetassoc_0","multclosed_inv","inverse_1_0_0")
    allL("leftdist",hov"b:i",fot"1",le"-(a*b)")
    impL("leftdist_0") left by {
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    allL("multrightneutral",hov"b:i").forget
    impL("multrightneutral") left by {trivial}
    eql("multrightneutral","leftdist_0").fromLeftToRight
    forget("multrightneutral")
    cut("multminusright",hof"∀x∀y ((R x ∧ R y) → x * (-y) = -(x*y) )") left insert (multMinusRight)
    allL("multminusright",hov"b:i",le"a*b").forget
    impL("multminusright") left by {
      andR left by {trivial}
      trivial
    }
    eql("multminusright","leftdist_0")
    forget("multminusright")
    allL("multassoc",hov"b:i",hov"a:i",hov"b:i").forget
    impL("multassoc") left by {
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    eql("multassoc","leftdist_0")
    allL("rightdist",fot"1",le"-(b*a)",hov"b:i")
    allL("multclosed",hov"b:i",hov"a:i")
    impL("multclosed_1") left by {
      andR left by {trivial}
      trivial
    }
    allL("plusinverse",le"b*a")
    impL("plusinverse_1") left by {trivial}
    andL("plusinverse_1")
    impL("rightdist_0") left by {
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    allL("multleftneutral",hov"b:i")
    impL("multleftneutral_0") left by {trivial}
    eql("multleftneutral_0","leftdist_0").yielding(hof"b*(1+(-(a*b)))=1*b+(-(b*a*b))")
    cut("multminusleft",hof"∀x∀y ((R x ∧ R y) → (-x) * y = -(x * y) )") left insert (multMinusLeft)
    forget("plusinverse","multassoc","multleftneutral_0")
    allL("multminusleft",le"b*a",hov"b:i").forget
    impL("multminusleft") left by {
      andR left by {trivial}
      trivial
    }
    eql("multminusleft","rightdist_0")
    forget("multminusleft")
    eql("rightdist_0","leftdist_0").fromRightToLeft
    forget("rightdist_0")
    eql("leftdist_0","multleftsubset_0")
    forget("leftdist_0")
    allL("multsetassoc",le"1+(-(b*a))",hov"b:i")
    allL("plusclosed",fot"1",le"-(b*a)")
    impL("plusclosed_1") left by {
      andR left by {trivial}
      trivial
    }
    impL("multsetassoc_0") left by {
      andR left by {trivial}
      trivial
    }
    cut("setmultclosed",hof"∀x (R x → x ** R ⊆ R)") left insert (setMultClosed)
    forget("multclosed")
    allL("setmultclosed",hov"b:i")
    impL("setmultclosed_0") left by {trivial}
    allL("multleftsubset",le"1+(-(b*a))",le"b**R",hov"R:i>o")
    impL("multleftsubset_1") left by {trivial}
    eql("multsetassoc_0","multleftsubset_1")
    allL("setmultclosed",hov"a:i")
    impL("setmultclosed_1") left by {trivial}
    allL("multleftsubset",hov"b:i",le"a**R",hov"R:i>o").forget
    impL("multleftsubset") left by {trivial}
    allL("multsetassoc",hov"b:i",hov"a:i").forget
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
    forget("subtrans_0","setmultclosed_0","setmultclosed_1","multsetassoc_0","multleftsubset_0","multleftsubset_1","multleftsubset")
    eql("multsetassoc","subtrans_1")
    forget("multsetassoc")
    cut("multsetdist",hof"∀a∀b ((R a ∧ R b) → (a + b) ** R ⊆ a ** R ⊕ b ** R)") left insert (multleftDistributive)
    allL("multsetdist",le"1+(-(b*a))",le"b*a").forget
    impL("multsetdist") left by {
      andR left by {trivial}
      trivial
    }
    cut("setmult1equ",hof"R = 1**R") left insert (setMult1_Equal)
    forget("extens","multleftneutral")
    allL("plusneutral",fot"1").forget
    impL("plusneutral") left by {trivial}
    eql("plusneutral","setmult1equ")
    forget("plusneutral")
    allL("pluscomm",le"b*a",le"-(b*a)").forget
    impL("pluscomm") left by {
      andR left by {trivial}
      trivial
    }
    eql("plusinverse_1_0","pluscomm")
    eql("pluscomm","setmult1equ")
    allL("plusassoc",fot"1",le"-(b*a)",le"b*a").forget
    impL("plusassoc") left by {
      andR left by {
        andR left by {trivial}
        trivial
      }
      trivial
    }
    eql("plusassoc","setmult1equ")
    forget("pluscomm","plusassoc","plusinverse_1_0","rightdist")
    eql("setmult1equ","multsetdist").fromRightToLeft
    forget("setmult1equ")
    cut("setplussubset",hof"∀x∀y (R y → x**R ⊆ y**R → y**R ⊕ x**R ⊆ y**R)") left insert (setPlusSubset)
    forget("plusclosed")
    allL("setplussubset",le"b*a",le"1+(-)(b*a)").forget
    impL("setplussubset") left by {trivial}
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

  def inverse_acnf = {
    val p1 = proof.inverse
    val p2 = eliminateDefinitions(p1)(proof.ctx)
    val p3 = soEqToEquiv(p2)
    val p4 = CutRule(gapt.proofs.lk.transformations.atomicEquality.trivialExtensionality, p3)
    cutNormal(p4)
  }
}