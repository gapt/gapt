package gapt.examples.tip.axar

import ammonite.ops._
import gapt.expr._
import gapt.expr.formula.Formula
import gapt.formats.babel.Notation
import gapt.formats.babel.Precedence
import gapt.formats.tip.export.export.{ export => exportTip }
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.immutable.ImmutableContext
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic.Lemma
import gapt.proofs.gaptic.TacticsProof
import gapt.proofs.gaptic._

object AxarProblems {

  val problems = List(
    noind_1,
    noind_2,
    noind_3,
    noind_4,
    openind_1,
    openind_2,
    openind_3,
    openind_3a,
    openind_3b,
    openind_4,
    openind_5,
    openind_5a,
    openind_6,
    openind_6a,
    openind_6b,
    openind_7,
    openind_8a,
    openind_8,
    openind_9,
    openind_9a,
    openind_10 )

  private val SMT2_LINE_WIDTH = 80

  def axarProblemToSmt2String( problem: Problem ): String =
    exportTip( problem.sequent, problem.language.context, problem.comment )
      .render( SMT2_LINE_WIDTH ) + "\n"

  def exportAxarProblemToSmt2File( prefix: Path, problem: Problem ): Unit = {
    val outputFilePath = prefix / ( problem.name + ".smt2" )
    val output = axarProblemToSmt2String( problem )
    ammonite.ops.write( outputFilePath, output )
  }

  def exportAxarProblems( prefix: Path ): Unit = {
    problems.foreach { exportAxarProblemToSmt2File( prefix, _ ) }
  }
}

case class Language(
    inductiveTypes: Seq[InductiveType],
    constants:      Set[Const],
    notations:      Set[Notation] ) {

  def extend( constant: Const ) = Language(
    inductiveTypes,
    constants + constant,
    notations )

  implicit def context: ImmutableContext = {
    var ctx = Context.default
    inductiveTypes.foreach { ctx += _ }
    constants.foreach { ctx += _ }
    notations.foreach { ctx += _ }
    ctx
  }
}

object PeanoArithmetic {
  val language: Language = {
    val inductiveTypes = Seq(
      InductiveType( "nat", hoc"0:nat", hoc"s:nat>nat" ) )
    val constants = Set(
      hoc"+:nat>nat>nat",
      hoc"*:nat>nat>nat",
      hoc"≤:nat>nat>o" )
    val notations: Set[Notation] = Set(
      Notation.Infix( "+", Precedence.plusMinus ),
      Notation.Infix( "*", Precedence.timesDiv ),
      Notation.Infix( "≤", Precedence.infixRel ) )
    Language( inductiveTypes, constants, notations )
  }
  def numeral( n: Int ): Expr = {
    import language.context
    n match {
      case 0 => le"0"
      case _ => le"s(${numeral( n - 1 )})"
    }
  }
}

object RobinsonArithmetic {
  val name = "Q"
  val language: Language = PeanoArithmetic.language
  val axioms: Seq[Formula] = {
    import language.context
    Seq(
      hof"!x 0 != s(x)",
      hof"!x !y ( s(x) = s(y) -> x = y )",
      hof"!x (x != 0 -> ?y x = s(y))",
      hof"!x x + 0 = x",
      hof"!x !y x + s(y) = s(x + y)",
      hof"!x x * 0 = 0",
      hof"!x !y x * s(y) = x*y + x",
      hof"!x !y ( x ≤ y <-> ?z z + x = y)" )
  }
}
object GaussianArithmetic {
  val language: Language = PeanoArithmetic.language.extend( hoc"g:nat>nat" )
  val axioms: Seq[Formula] = RobinsonArithmetic.axioms ++ {
    import language.context
    Seq(
      hof"g(0) = 0",
      hof"!x g(s(x)) = g(x) + s(x)" )
  }
}

abstract class Problem( val language: Language )
  extends TacticsProof( language.context ) {
  val sequent: Sequent[Formula]
  val comment: Option[String] = None
  val name: String
}

object noind_1 extends Problem( PeanoArithmetic.language ) {

  import PeanoArithmetic.numeral

  val name = "noind_1"

  override val comment = Some(
    s"""
       | Provable without induction.
       |
       |""".stripMargin )

  val goal = hof"${numeral( 2 )} * ${numeral( 3 )} + ${numeral( 5 )} = ${numeral( 11 )}"

  val sequent: Sequent[Formula] =
    RobinsonArithmetic.axioms ++: Sequent() :+ goal

  lazy val proof = Lemma( sequent ) {
    rewrite.many ltr "h_6" in "g"
    rewrite ltr "h_5" in "g"
    rewrite.many ltr "h_4" in "g"
    rewrite.many ltr "h_3" in "g"
    refl
  }
}
object noind_2 extends Problem( PeanoArithmetic.language ) {

  import PeanoArithmetic.numeral

  val name = "noind_2"

  val sequent =
    RobinsonArithmetic.axioms ++:
      Sequent() :+
      hof"${numeral( 10 )} ≤ ${numeral( 2 )} * ${numeral( 3 )} + ${numeral( 5 )}"

  lazy val proof = Lemma(
    sequent ) {
    allL( "h_7", numeral( 10 ), le"${numeral( 2 )} * ${numeral( 3 )} + ${numeral( 5 )}" )
    andL( "h_7_0" )
    forget( "h_7_0_0" )
    impL( "h_7_0_1" )
    // 1
    forget( "g" )
    exR( le"s(0)" )
    forget( "h_7_0_1" )
    rewrite.many ltr "h_6" in "h_7_0_1_0"
    rewrite ltr "h_5" in "h_7_0_1_0"
    rewrite.many ltr "h_4" in "h_7_0_1_0"
    rewrite.many ltr "h_3" in "h_7_0_1_0"
    refl
    // 2
    trivial
  }
}
object noind_3 extends Problem( PeanoArithmetic.language ) {
  import PeanoArithmetic.numeral
  val name = "noind_3"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"?x x*${numeral( 3 )} + ${numeral( 5 )} = ${numeral( 11 )}"
  lazy val proof = Lemma( sequent ) {
    forget( "h_0", "h_1", "h_2", "h_7" )
    exR( le"s(s(0))" )
    forget( "g" )
    rewrite.many ltr "h_6" in "g_0"
    rewrite ltr "h_5" in "g_0"
    rewrite.many ltr "h_4" in "g_0"
    rewrite.many ltr "h_3" in "g_0"
    refl
  }
}

object noind_4 extends Problem( PeanoArithmetic.language ) {
  import PeanoArithmetic.numeral
  val name = "noind_4"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"?x ${numeral( 10 )} ≤ ${numeral( 2 )} * x + ${numeral( 5 )}"
  lazy val proof = Lemma(
    sequent ) {
    forget( "h_0", "h_1", "h_2" )
    exR( le"s(s(s(0)))" )
    forget( "g" )
    allL( "h_7", numeral( 10 ), le"${numeral( 2 )} * ${numeral( 3 )} + ${numeral( 5 )}" )
    forget( "h_7" )
    andL( "h_7_0" )
    forget( "h_7_0_0" )
    impL( "h_7_0_1" )
    // 1
    forget( "g_0" )
    exR( "h_7_0_1", le"s(0)" )
    forget( "h_7_0_1" )
    rewrite.many ltr "h_6" in "h_7_0_1_0"
    rewrite ltr "h_5" in "h_7_0_1_0"
    rewrite.many ltr "h_4" in "h_7_0_1_0"
    rewrite.many ltr "h_3" in "h_7_0_1_0"
    refl
    // 2
    trivial
  }
}

object noind_lemma_1 extends Problem( PeanoArithmetic.language ) {
  val name = "noind lemma_1"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y (x ≤ y -> s(x) ≤ s(y))"
  lazy val proof = Lemma( sequent ) {
    decompose
    allL( "h_7", le"s(x)", le"s(y)" )
    andL( "h_7_0" )
    forget( "h_7_0_0" )
    chain( "h_7_0_1" )
    allL( "h_7", le"x:nat", le"y:nat" )
    andL( "h_7_1" )
    forget( "h_7_1_1" )
    impL( "h_7_1_0" )
    trivial
    exL( "h_7_1_0" )
    exR( le"z:nat" )
    escargot
  }
}
object openind_1 extends Problem( PeanoArithmetic.language ) {
  val name = "openind_1"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y !z x + (y + z) = (x + y) + z"
  lazy val proof = Lemma(
    sequent ) {
    allR( "g" )
    allR( "g" )
    allR( "g" )
    induction( hov"z:nat" )
    // 1
    rewrite.many ltr "h_3" in "g"
    refl
    // 2
    rewrite.many ltr "h_4" in "g"
    rewrite ltr "IHz_0" in "g"
    refl
  }
}

object openind_2 extends Problem( PeanoArithmetic.language ) {
  val name = "openind_2"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y !z (y + x = z + x -> y = z)"
  lazy val proof = Lemma( sequent ) {
    allR( "g" )
    allR( "g" )
    allR( "g" )
    induction( hov"x:nat" )
    // 1
    rewrite.many ltr "h_3" in "g"
    impR
    trivial
    // 2
    impR // assume y + s(x) = z + s(x)
    rewrite.many ltr "h_4" in "g_0" // by def of + we have s(y + x) = s(z + x)
    allL( "h_1", le"y + x_0", le"z + x_0" ) // by injectivity of + we have y + x = z + x
    impL( "h_1_0" )
    // 2.1
    trivial
    // 2.2
    impL( "IHx_0" ) // by the induction hypothesis we obtain y = z
    // 2.1
    trivial
    // 2.2
    trivial
  }
}
object openind_3a extends Problem( PeanoArithmetic.language ) {
  val name = "openind_3a"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x 0 + x = x"
  lazy val proof = Lemma( sequent ) {
    allR
    induction( hov"x:nat" )
    // 1.1
    rewrite ltr "h_3" in "g"
    refl
    // 1.2
    rewrite ltr "h_4" in "g"
    rewrite ltr "IHx_0" in "g"
    refl
  }

}

object openind_3b extends Problem( PeanoArithmetic.language ) {
  val name = "openind_3b"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y s(x) + y = s(x + y)"
  lazy val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"y:nat" )
    // 2.1
    rewrite.many ltr "h_3" in "g"
    refl
    // 2.2
    rewrite.many ltr "h_4" in "g"
    rewrite ltr "IHy_0" in "g"
    refl
  }
}
object openind_3 extends Problem( PeanoArithmetic.language ) {
  val name = "openind_3"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y x + y = y + x"
  lazy val proof = Lemma( sequent ) {
    include( "l_1", openind_3a.proof )
    // 2
    include( "l_2", openind_3b.proof )
    // 3
    allR( "g" )
    allR( "g" )
    induction( hov"x:nat" )
    // 3.1
    rewrite ltr "l_1" in "g"
    rewrite ltr "h_3" in "g"
    refl
    // 3.2
    rewrite ltr "l_2" in "g"
    rewrite ltr "h_4" in "g"
    rewrite ltr "IHx_0" in "g"
    refl
  }
}
object openind_4 extends Problem( PeanoArithmetic.language ) {
  val name = "openind_4"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y !z (x + y = x + z -> y = z)"
  lazy val proof = Lemma( sequent ) {
    include( "l_1", openind_3.proof )
    include( "l_2", openind_2.proof )
    allR( "g" )
    allR( "g" )
    allR( "g" )
    allL( "l_1", le"x:nat", le"y:nat" )
    rewrite ltr "l_1_0" in "g"
    forget( "l_1_0" )
    allL( "l_1", le"x:nat", le"z:nat" )
    rewrite ltr "l_1_0" in "g"
    allL( "l_2", le"x:nat", le"y:nat", le"z:nat" )
    trivial
  }
}
object openind_5a extends Problem( PeanoArithmetic.language ) {
  val name = "openind_5a"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y !z x * (y + z) = x*y + x*z"
  lazy val proof = Lemma( sequent ) {
    allR
    allR
    allR
    induction( hov"z:nat" )
    escargot
    include( "l_1", openind_1.proof )
    escargot
  }
}

object openind_5 extends Problem( PeanoArithmetic.language ) {
  val name = "openind_5"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y !z x * (y * z) = (x * y) * z"
  lazy val proof = Lemma( sequent ) {
    allR
    allR
    allR
    induction( hov"z:nat" )
    // 1
    rewrite.many ltr "h_5" in "g"
    refl
    // 2
    rewrite.many ltr "h_6" in "g"
    include( "l_1", openind_5a.proof )
    escargot
  }
}
object openind_6a extends Problem( PeanoArithmetic.language ) {
  val name = "openind_6a"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x 0 * x = 0"
  lazy val proof = Lemma( sequent ) {
    allR
    induction( hov"x:nat" )
    escargot
    escargot
  }
}
object openind_6b extends Problem( PeanoArithmetic.language ) {
  val name = "openind_6b"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y s(x) * y = x*y + y"
  lazy val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"y:nat" )
    rewrite.many ltr "h_5" in "g"
    rewrite ltr "h_3" in "g"
    refl
    rewrite.many ltr "h_6" in "g"
    rewrite.many ltr "h_4" in "g"
    include( "plus_assoc", openind_1.proof )
    include( "plus_comm", openind_3.proof )
    escargot
  }
}
object openind_6 extends Problem( PeanoArithmetic.language ) {
  val name = "openind_6"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y x * y = y * x"
  lazy val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"x:nat" )
    include( "l_1", openind_6a.proof )
    escargot
    include( "msl", openind_6b.proof )
    escargot
  }
}
object openind_7 extends Problem( PeanoArithmetic.language ) {
  val name = "openind_7"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y (x ≤ y | y ≤ x)"
  lazy val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"x:nat" )
    // 1
    escargot
    // 2
    orL
    allL( "h_7", le"x_0:nat", le"y:nat" )
    andL
    forget( "h_7_0_1" )
    impL
    trivial
    exL
    allL( "h_2", le"z:nat" )
    impL
    negR
    rewrite ltr "h_2_0" in "h_7_0_0"
    include( "l_1", openind_3a.proof )
    rewrite ltr "l_1" in "h_7_0_0"
    orR
    forget( "g_0" )
    allL( "h_7", le"y:nat", le"s(x_0:nat)" )
    andL
    forget( "h_7_1_0" )
    impL
    forget( "g_1" )
    exR( le"s(0)" )
    forget( "h_7_1_1" )
    include( "l_2", openind_3b.proof )
    rewrite ltr "l_2" in "h_7_1_1_0"
    rewrite ltr "l_1" in "h_7_1_1_0"
    rewrite ltr "h_7_0_0" in "h_7_1_1_0"
    refl
    trivial
    exL
    rewrite ltr "h_2_0" in "h_7_0_0"
    include( "l_1", openind_3b.proof )
    rewrite ltr "l_1" in "h_7_0_0"
    forget( "l_1" )
    rewrite rtl "h_4" in "h_7_0_0"
    forget( "l_1" )
    orR
    forget( "g_1" )
    allL( "h_7", le"s(x_0:nat)", le"y:nat" )
    andL
    forget( "h_7_1_0" )
    impL
    forget( "g_0" )
    exR( le"y_0:nat" )
    trivial
    trivial
    orR
    forget( "g_0" )
    allL( "h_7", le"y:nat", le"x_0:nat" )
    andL
    forget( "h_7_0_1" )
    impL
    trivial
    exL
    allL( "h_7", le"y:nat", le"s(x_0:nat)" )
    andL
    forget( "h_7_1_0" )
    impL
    exR( le"s(z:nat)" )
    include( "l_1", openind_3b.proof )
    rewrite ltr "l_1" in "h_7_1_1_0"
    rewrite ltr "h_7_0_0" in "h_7_1_1_0"
    refl
    trivial
  }
}
object openind_8a extends Problem( PeanoArithmetic.language ) {
  val name = "openind_8a"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y (x != 0 | y != 0 -> x + y != 0)"
  lazy val proof = Lemma( sequent ) {
    decompose
    orL( "g_0" )
    // case x != 0
    allL( "h_2", le"x:nat" )
    impL( "h_2_0" )
    trivial
    exL
    rewrite ltr "h_2_0" in "g_1"
    include( "l", openind_3b.proof )
    rewrite ltr "l" in "g_1"
    allL( "h_0", le"y_0 + y" )
    negL( "h_0_0" )
    quasiprop
    // case y != 0
    allL( "h_2", le"y:nat" )
    impL( "h_2_0" )
    trivial
    exL
    rewrite ltr "h_2_0" in "g_1"
    rewrite ltr "h_4" in "g_1"
    allL( "h_0", le"x + y_0" )
    negL( "h_0_0" )
    quasiprop
  }
}
object openind_8 extends Problem( PeanoArithmetic.language ) {
  val name = "openind_8"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"∀x ∀y ∀z ( x != 0 ∧ y * x = z * x  →  y = z )"
  lazy val proof = Lemma( sequent ) {

    cut( "l", hof"!x !y (x ≤ y & x != y -> ?z (z != 0 & z + x = y))" )
    forget( "g" )
    allR
    allR
    impR
    andL
    allL( "h_7", le"x:nat", le"y:nat" )
    andL
    forget( "h_7_0_1" )
    impL
    trivial
    exL
    allL( "h_2", le"z:nat" )
    impL
    negR
    rewrite ltr "h_2_0" in "h_7_0_0"
    include( "l_1", openind_3a.proof )
    rewrite ltr "l_1" in "h_7_0_0"
    negL
    trivial
    exL
    exR( le"z:nat" )
    andR
    negR
    rewrite ltr "l_1_0" in "h_2_0"
    allL( "h_0", le"y_0:nat" )
    negL( "h_0_0" )
    trivial
    trivial

    cut( "f", hof"!x !y !z (x ≤ y & x != y & z != 0 -> x * z ≤ y * z & x * z != y * z)" )
    forget( "g" )
    allR
    allR
    allR
    induction( hov"z:nat" )

    // begin base
    impR
    andL
    andL
    negL( "f_0_1" )
    refl
    // end base

    // begin step

    impR
    andL
    andL

    // begin case distinction on z_0 = 0 | z_0 != 0
    allL( "h_2", le"z_0:nat" )
    impL( "h_2_0" )

    // begin case z_0 = 0
    negR
    rewrite.many ltr "h_2_0" in "f_1"
    rewrite.many ltr "h_6" in "f_1"
    rewrite.many ltr "h_5" in "f_1"
    include( "l_1", openind_3a.proof )
    rewrite.many ltr "l_1" in "f_1"
    prop
    // end case z_0 = 0

    // begin case ?y z_0 = s(y)

    // begin z_0 != 0
    exL( "h_2_0" ) // z_0 = s(y_0)
    cut( "h_2_0_0", hof"z_0 != 0" )
    negR
    rewrite ltr "h_2_0_0" in "h_2_0"
    allL( "h_0", le"y_0:nat" )
    prop
    forget( "h_2_0" )
    //end z_0 != 0

    // begin apply IH
    impL( "IHz_0" )
    andR( "IHz_0" )
    andR( "IHz_0" )
    trivial
    trivial
    trivial
    // end apply IH

    andL( "IHz_0" )

    // begin apply lemma xz_0 < yz_0 -> xz_0 + u = yz_0 for some u != 0
    allL( "l", le"x*z_0", le"y*z_0" )
    impL( "l_0" )
    andR( "l_0" )
    trivial
    trivial
    exL( "l_0", hov"u:nat" )
    andL( "l_0" )
    // end apply lemma xz_0 < yz_0 -> xz_0 + u = yz_0 for some u != 0

    // begin apply lemma x < y -> y = x + v for some v != 0
    allL( "l", le"x:nat", le"y:nat" )
    impL( "l_1" )
    andR( "l_1" )
    trivial
    trivial
    exL( "l_1", hov"v:nat" )
    andL( "l_1" )
    // end apply lemma x < y -> y = x + v for some v != 0

    // begin solve main lemma
    rewrite.many ltr "h_6" in "f_1"
    rewrite.many rtl "l_0_1" in "f_1"
    rewrite.many rtl "l_1_1" in "f_1"
    include( "plus_asso", openind_1.proof )
    include( "plus_comm", openind_3.proof )
    include( "lem", openind_8a.proof )
    andR

    // begin <=
    allL( "h_7", le"x * z_0 + x", le"u + (x * z_0) + (v + x)" )
    andL( "h_7_0" )
    forget( "h_7_0_0" )
    impL( "h_7_0_1" )
    exR( "h_7_0_1", le"(u + v)" )
    forget( "h_7_0_1", "f_1", "h_1", "h_2", "h_3", "h_4", "h_5", "h_6", "h_7", "l_1_0", "l_1_1", "l_0_0", "l_0_1", "IHz_0_0", "IHz_0_1", "h_2_0_0", "f_0_0_0", "f_0_0_1", "f_0_1", "l", "h_0", "lem" )
    escargot
    trivial
    // end <=

    // begin !=
    include( "plus_canc", openind_4.proof )
    allL( "lem", le"u:nat", le"v:nat" )
    forget( "h_7_0_1", "h_1", "h_2", "h_4", "h_5", "h_6", "h_7", "l_1_1", "l_0_1", "IHz_0_0", "IHz_0_1", "h_2_0_0", "f_0_0_0", "f_0_0_1", "f_0_1", "l", "h_0", "lem" )
    allL( "plus_canc", le"x * z_0", le"0", le"u + v" )
    escargot
    // end !=

    // end solve main lemma

    // begin case ?y z_0 = s(y)

    // end step

    // begin apply main lemma
    decompose
    // begin case distinction y <= z | z <= y
    include( "leq_dico", openind_7.proof )
    allL( "leq_dico", le"y:nat", le"z:nat" )
    allL( "h_7", le"y:nat", le"z:nat" )
    forget( "leq_dico", "l", "h_1", "h_5", "h_6", "h_7" )
    orL

    // begin y <= z
    escargot
    // end y <= z

    // begin z <= y
    escargot
    // end z <= y

    // end case distinction y <= z | z <= y

    // end apply main lemma
  }
}
object openind_9a extends Problem( PeanoArithmetic.language ) {
  val name = "openind_9a"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y (x + y = 0 -> x = 0 & y = 0)"
  lazy val proof = Lemma( sequent ) {
    decompose
    andR
    allL( "h_2", le"x:nat" )
    impL( "h_2_0" )
    prop
    exL( "h_2_0" )
    rewrite ltr "h_2_0" in "g_0"
    include( "plus_slef", openind_3b.proof )
    escargot
    escargot
  }

}
object openind_9 extends Problem( PeanoArithmetic.language ) {
  val name = "openind_9"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y ( x ≤ y & y ≤ x -> x = y )"
  lazy val proof = Lemma( sequent ) {
    decompose
    allL( "h_7", le"x:nat", le"y:nat" )
    allL( "h_7", le"y:nat", le"x:nat" )
    andL( "h_7_0" )
    andL( "h_7_1" )
    forget( "h_7_0_1" )
    forget( "h_7_1_1" )
    impL( "h_7_0_0" )
    trivial
    impL( "h_7_1_0" )
    trivial
    forget( "g_0_0", "g_0_1" )
    include( "plus_canc", openind_4.proof )
    include( "plus_asso", openind_1.proof )
    include( "plus_comm", openind_3.proof )
    forget( "h_7" )
    exL( "h_7_0_0", hov"u:nat" )
    exL( "h_7_1_0", hov"v:nat" )
    rewrite rtl "h_7_0_0" in "h_7_1_0"
    allL( "plus_canc", le"x:nat", le"0", le"u + v" )
    escargot
  }
}
object openind_10 extends Problem( GaussianArithmetic.language ) {
  val name = "openind_10"
  val sequent = ( GaussianArithmetic.axioms ) ++: Sequent() :+ hof"!x s(s(0)) * g(x) = x * s(x)"
  lazy val proof = Lemma( sequent ) {
    include( "plus_asso", openind_1.proof )
    include( "plus_comm", openind_3.proof )
    include( "mult_comm", openind_6.proof )
    allR( "g", hov"x:nat" )
    induction( hov"x:nat" )
    escargot
    escargot
  }
}
object openind_11a extends Problem( PeanoArithmetic.language ) {
  val name = ""
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y !z ( y ≤ z & y != z -> x + y ≤ x + z & x + y != x + z )"
  val proof = Lemma( sequent ) {
    allR
    allR
    allR
    induction( hov"x:nat" )

    // begin base case
    include( "plus_lzer", openind_3a.proof )
    forget( "h_0", "h_1", "h_2", "h_3", "h_4", "h_5", "h_6", "h_7" )
    escargot
    // end base case

    // begin step case
    impR
    andL

    // begin apply the IH
    impL
    prop
    andL
    // end apply the IH

    include( "plus_lsuc", openind_3b.proof )
    rewrite.many ltr "plus_lsuc" in "g_1"
    andR

    // begin sx_0 + y <= sx_0 + z
    include( "leq_succ", noind_lemma_1.proof )
    chain( "leq_succ" )
    trivial
    // end sx_0 + y <= sx_0 + z

    // begin s(x_0) + y != s(x_0) + z
    allL( "h_1", le"x_0 + y", le"x_0 + z" )
    impL
    prop
    quasiprop
    // end s(x_0) + y != s(x_0) + z

    // end step case
  }
}
object openind_11 extends Problem( PeanoArithmetic.language ) {
  val name = "openind_11"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y ( x + x = y + y -> x = y )"
  // via induction with multiplication ( 2*x = 2*y -> x = y )
  val proof = Lemma( sequent ) {
    cut( "l", hof"!x x + x = x*s(s(0))" )
    // begin lemma x + x = x*2
    allR( "l" )
    rewrite.many ltr "h_6" in "l"
    rewrite ltr "h_5" in "l"
    include( "plus_lzer", openind_3a.proof )
    rewrite ltr "plus_lzer" in "l"
    refl
    // end lemma
    allR
    allR
    impR
    rewrite.many ltr "l" in "g_0"
    include( "mult_canc", openind_8.proof )
    allL( "mult_canc", le"s(s(0))", le"x:nat", le"y:nat" )
    impL( "mult_canc_0" )
    andR
    // 2 != 0 via h_0
    allL( "h_0", le"s(0)" )
    quasiprop

    trivial

    trivial
  }
  //   via pure s, 0, +, ≤ induction
  val proof2 = Lemma( sequent ) {
    allR
    allR
    impR
    include( "leq_dico", openind_7.proof )
    allL( "leq_dico", le"x:nat", le"y:nat" )
    orL

    // begin x <= y
    allL( "h_7", le"x:nat", le"y:nat" )
    andL( "h_7_0" )
    forget( "h_7_0_1" )
    impL
    trivial
    exL( "h_7_0_0", hov"z:nat" )

    allL( "h_2", le"z:nat" )
    impL( "h_2_0" )

    // begin z_0 = 0
    negR
    rewrite ltr "h_2_0" in "h_7_0_0"
    include( "plus_lzer", openind_3a.proof )
    escargot
    // end z_0 = 0

    // begin z_0 != 0
    cut( "z_ne_zero", hof"z != 0" )
    escargot
    rewrite.many rtl "h_7_0_0" in "g_0"
    include( "plus_comm", openind_3.proof )
    include( "plus_asso", openind_1.proof )
    include( "plus_canc", openind_4.proof )
    escargot
    // end z_0 != 0

    // end x <= y

    // begin y <= x
    allL( "h_7", le"y:nat", le"x:nat" )
    andL( "h_7_0" )
    forget( "h_7_0_1" )
    impL
    trivial
    exL( "h_7_0_0", hov"z:nat" )

    allL( "h_2", le"z:nat" )
    impL( "h_2_0" )

    // begin z_0 = 0
    negR
    rewrite ltr "h_2_0" in "h_7_0_0"
    include( "plus_lzer", openind_3a.proof )
    escargot
    // end z_0 = 0

    // begin z_0 != 0
    cut( "z_ne_zero", hof"z != 0" )
    escargot
    rewrite.many rtl "h_7_0_0" in "g_0"
    include( "plus_comm", openind_3.proof )
    include( "plus_asso", openind_1.proof )
    include( "plus_canc", openind_4.proof )
    forget( "h_2_0", "h_5", "h_6" )
    escargot
    // end z_0 != 0

    // end y <= x
  }

}
object openind_lemma_1 extends Problem( PeanoArithmetic.language ) {
  val name = "openind_lemma_1"
  val sequent = RobinsonArithmetic.axioms ++: Sequent() :+ hof"!x !y ( y != 0 -> x + y != x)"
  val proof = Lemma( sequent ) {
    decompose
    allL( "h_2", le"y:nat" )
    include( "plus_canc", openind_4.proof )
    forget( "h_2" )
    escargot
  }
}
