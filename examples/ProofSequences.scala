package gapt.examples

import gapt.examples.Formulas._
import gapt.expr._
import gapt.expr.fol.Numeral
import gapt.expr.fol.Utils
import gapt.expr.hol.instantiate
import gapt.expr.hol.universalClosure
import gapt.formats.babel.Notation
import gapt.formats.babel.Precedence
import gapt.proofs.Ant
import gapt.proofs.HOLSequent
import gapt.proofs.ProofBuilder
import gapt.proofs.Sequent
import gapt.proofs.Suc
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._
import gapt.proofs.lk._
import gapt.proofs.lk.rules
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.ReflexivityAxiom
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.macros
import gapt.proofs.lk.rules.macros.ContractionMacroRule
import gapt.proofs.lk.rules.macros.ForallLeftBlock
import gapt.proofs.lk.rules.macros.TransRule
import gapt.proofs.lk.rules.macros.WeakeningContractionMacroRule
import gapt.proofs.lk.rules.macros.WeakeningLeftMacroRule

trait ProofSequence {
  def apply( n: Int ): LKProof

  def name = getClass.getSimpleName.replace( "$", "" )
}

/**
 * Constructs cut-free FOL LK proofs of the sequents
 *
 * P(0), ∀x. P(x) → P(s(x)) :- P(s^n^(0))
 *
 * where n is an Integer parameter >= 0.
 */
object LinearExampleProof extends ProofSequence {
  /**
   * @param n An integer >= 0.
   * @return A proof of P(0), ∀x. P(x) → P(s(x)) :- P(s^n^(0))
   */
  def apply( n: Int ): LKProof = {
    require( n >= 0, "n must be nonnegative" )

    val num = Utils.numeral( n )
    val ax = fof"!x (P x -> P (s x))"
    val p0 = foa"P(0)"
    val pn = foa"P($num)"
    Proof( Sequent( Seq( "P0" -> p0, "Ax" -> ax ), Seq( "Pn" -> pn ) ) ) {
      repeat( chain( "Ax" ) )
      prop
    }
  }
}

/**
 * Constructs short FOL LK proofs of the sequents
 *
 * P(0), ∀x. P(x) → P(s(x)) :- P(s^2 ^n^ ^(0))
 *
 * where n is an Integer parameter >= 0.
 */
object LinearCutExampleProof extends ProofSequence {
  private val ax = fof"!x (P x -> P (s x))"
  private def s( n: Int )( x: FOLTerm ): FOLTerm =
    if ( n == 0 ) x else s( n - 1 )( FOLFunction( "s", x ) )
  private def lemma( n: Int ): LKProof =
    Proof( hols"h: !x (P(x) -> P(${s( 1 << ( n - 1 ) )( fov"x" )})) :- !x (P(x) -> P(${s( 1 << n )( fov"x" )}))" ) {
      allR; impR; repeat( chain( "h" ) ); trivial
    }
  private def lemmas( n: Int ): LKProof =
    if ( n == 0 ) LogicalAxiom( ax )
    else if ( n == 1 ) lemma( 1 )
    else CutRule( lemmas( n - 1 ), Suc( 0 ), lemma( n ), Ant( 0 ) )

  /**
   * @param n An integer >= 0.
   * @return A proof of P(0), ∀x. P(x) → P(s(x)) :- P(s^2 ^m^ ^(0))
   */
  def apply( n: Int ): LKProof = {
    require( n >= 0, "n must be nonnegative" )
    Proof( hols"p0: P(0), ax: $ax :- g: P(${s( 1 << n )( foc"0" )})" ) {
      include( "lem", lemmas( n ) )
      chain( "lem" )
      prop
    }
  }
}

/**
 * Functions to construct cut-free FOL LK proofs of the sequents
 *
 * P(0,0), ∀x,y. P(x,y) → P(s(x),y), ∀x,y. P(x,y) → P(x,s(y)) :- P(s^n^(0),s^n^(0))
 *
 * where n is an Integer parameter >= 0.
 *
 * The proofs constructed here go along the diagonal of P, i.e. one x-step, then one y-step, etc.
 */
object SquareDiagonalExampleProof extends ProofSequence {

  /**
   * @param n An integer >= 0.
   * @return A proof of P(0,0), ∀x,y. P(x,y) → P(s(x),y), ∀x,y. P(x,y) → P(x,s(y)) :- P(s^n^(0),s^n^(0))
   */
  def apply( n: Int ): LKProof = {
    require( n >= 0, "n must be nonnegative" )

    val num = Utils.numeral( n )
    val p00 = foa"P(0,0)"
    val pnn = foa"P($num, $num)"
    val axX = fof"!x!y (P(x,y) -> P(s(x), y))"
    val axY = fof"!x!y (P(x,y) -> P(x, s(y)))"

    Proof( Sequent( Seq( "P00" -> p00, "AxX" -> axX, "AxY" -> axY ), Seq( "Pnn" -> pnn ) ) ) {
      repeat( chain( "AxY" ) andThen chain( "AxX" ) )
      prop
    }
  }
}

/**
 * Functions to construct cut-free FOL LK proofs of the sequents
 *
 * P(0,0), ∀x,y. P(x,y) → P(s(x),y), ∀x,y. P(x,y) → P(x,s(y)) :- P(s^n^(0),s^n^(0))
 *
 * where n is an Integer parameter >= 0.
 *
 * The proofs constructed here go along the edges of P, i.e. first all X-steps are performed,
 * then all Y-steps are performed
 */
object SquareEdgesExampleProof extends ProofSequence {

  /**
   * @param n An integer >= 0.
   * @return A proof of P(0,0), ∀x,y. P(x,y) → P(s(x),y), ∀x,y. P(x,y) → P(x,s(y)) :- P(s^n^(0),s^n^(0))
   */
  def apply( n: Int ): LKProof = {
    require( n >= 0, "n must be nonnegative" )

    val num = Utils.numeral( n )
    val p00 = foa"P(0,0)"
    val pnn = foa"P($num, $num)"
    val axX = fof"!x!y (P(x,y) -> P(s(x), y))"
    val axY = fof"!x!y (P(x,y) -> P(x, s(y)))"

    Proof( Sequent( Seq( "P00" -> p00, "AxX" -> axX, "AxY" -> axY ), Seq( "Pnn" -> pnn ) ) ) {
      repeat( chain( "AxY" ) )
      repeat( chain( "AxX" ) )
      prop
    }
  }
}

/**
 * Functions to construct cut-free FOL LK proofs of the sequents
 *
 * P(a,b), ∀x,y. P(x,y) → P(s,,x,,(x),y), ∀x,y. P(x,y) → P(x,s,,y,,(y)) :- P(s,,x,,^n^(a),s,,y,,^n^(b))
 *
 * where n is an Integer parameter >= 0.
 *
 * The proofs constructed here go along the edges of P, i.e. first all X-steps are performed,
 * then all Y-steps are performed,
 * but unlike SquareEdgesExampleProof, different functions are used for the X- and the Y-directions.
 */
object SquareEdges2DimExampleProof extends ProofSequence {

  /**
   * @param n An integer >= 0.
   * @return P(a,b), ∀x,y. P(x,y) → P(s,,x,,(x),y), ∀x,y. P(x,y) → P(x,s,,y,,(y)) :- P(s,,x,,^n^(a),s,,y,,^n^(b))
   */
  def apply( n: Int ): LKProof = {
    require( n >= 0, "n must be nonnegative" )

    val sna = Utils.iterateTerm( FOLConst( "a" ), "s_x", n )
    val snb = Utils.iterateTerm( FOLConst( "b" ), "s_y", n )
    val pab = foa"P(a,b)"
    val pnn = foa"P($sna, $snb)"
    val axX = fof"!x!y (P(x,y) -> P(s_x(x), y))"
    val axY = fof"!x!y (P(x,y) -> P(x, s_y(y)))"

    Proof( Sequent( Seq( "Pab" -> pab, "AxX" -> axX, "AxY" -> axY ), Seq( "Pnn" -> pnn ) ) ) {
      repeat( chain( "AxY" ) )
      repeat( chain( "AxX" ) )
      prop
    }
  }
}

/**
 * Functions to construct the straightforward cut-free FOL LK proofs of the sequents
 *
 * P(s^n^(0),0), ∀x,y. P(s(x),y) → P(x,s(y)) :- P(0,s^n^(0))
 *
 * where n is an Integer parameter >= 0.
 *
 * This sequent is shown to have no cut-free proof which can be compressed by a
 * single cut with a single quantifier in S. Eberhard, S. Hetzl: On the
 * compressibility of finite languages and formal proofs, submitted, 2015.
 */
object SumExampleProof extends ProofSequence {

  /**
   * @param n An integer >= 0.
   * @return A proof of P(s^n^(0),0), ∀x,y. P(s(x),y) → P(x,s(y)) :- P(0,s^n^(0))
   */
  def apply( n: Int ): LKProof = {
    require( n >= 0, "n must be nonnegative" )

    val num = Utils.numeral( n )
    val pn0 = foa"P($num,0)"
    val p0n = foa"P(0,$num)"
    val ax = fof" ∀x ∀y (P(s(x),y) -> P(x, s(y)))"

    Proof( Sequent( Seq( "Pn0" -> pn0, "Ax" -> ax ), Seq( "P0n" -> p0n ) ) ) {
      repeat( chain( "Ax" ) )
      prop
    }
  }
}

trait ExplicitEqualityTactics {

  /**
   * Applies the quantified equation ∀x(e_l=e_r) to the left side of the equation tgt_l=tgt_r,
   * leaving open the subgoal e_r σ = tgt_r.
   */
  def explicitRewriteLeft(
    equation: String, targetEq: String,
    transitivity: String = "trans" ) =
    for {
      goal <- currentGoal
      All.Block( Seq( _, transVar, _ ), _ ) = goal( transitivity )
      All.Block( _, Imp.Block( _, Eq( eqL, eqR ) ) ) = goal( equation )
      Eq( tgtL, tgtR ) = goal( targetEq )
      subst <- syntacticMatching( eqL, tgtL ).
        toTactic( s"cannot match equation $equation to formula $targetEq" )
      _ <- chain( transitivity ).at( targetEq ).subst( transVar -> subst( eqR ) )
      _ <- chain( equation ).at( targetEq )
    } yield ()

  /**
   * Applies the quantified equation ∀x(e_l=e_r) to the right side of the equation tgt_l=tgt_r,
   * leaving open the subgoal tgt_l = e_l σ.
   */
  def explicitRewriteRight(
    equation: String, targetEq: String,
    transitivity: String = "trans" ) =
    for {
      goal <- currentGoal
      All.Block( Seq( _, transVar, _ ), _ ) = goal( transitivity )
      All.Block( _, Imp.Block( _, Eq( eqL, eqR ) ) ) = goal( equation )
      Eq( tgtL, tgtR ) = goal( targetEq )
      subst <- syntacticMatching( eqR, tgtR ).
        toTactic( s"cannot match equation $equation to formula $targetEq" )
      _ <- chain( transitivity ).at( targetEq ).subst( transVar -> subst( eqL ) )
      _ <- focus( 1 )
      _ <- chain( equation ).at( targetEq )
    } yield ()

}

/**
 * Functions to construct cut-free FOL LK proofs of the sequents
 *
 * Refl, Trans, \ALL x. f(x) = x :- f^n^(a) = a
 *
 * where n is an Integer parameter >= 0.
 */
object LinearEqExampleProof extends TacticsProof with ProofSequence with ExplicitEqualityTactics {
  ctx += Sort( "i" )
  ctx += hoc"f: i>i"
  ctx += hoc"a: i"

  // f^k(a)
  private def fk( k: Int ): Expr =
    Stream.iterate( le"a" )( x => le"f $x" )( k )

  def apply( n: Int ) =
    Proof(
      ( "refl" -> hof"∀(x:i) x=x" ) +:
        ( "trans" -> hof"∀(x:i)∀y∀z (x=y ∧ y=z → x=z)" ) +:
        ( "id" -> hof"∀x f(x)=x" ) +: Sequent()
        :+ ( "goal" -> hof"${fk( n )} = a" ) ) {
        repeat( explicitRewriteLeft( "id", "goal" ) )
        chain( "refl" )
      }
}

object SumOfOnesF2ExampleProof extends TacticsProof with ProofSequence with ExplicitEqualityTactics {
  ctx += Sort( "i" )
  ctx += hoc"s: i>i"
  ctx += hoc"0: i"
  ctx += hoc"'+': i>i>i"
  ctx += Notation.Infix( "+", Precedence.plusMinus )
  ctx += hoc"f: i>i"

  def apply( n: Int ) =
    Proof(
      ( "trans" -> hof"∀(x:i)∀y∀z (x=y ∧ y=z → x=z)" ) +:
        ( "congplusleft" -> hof"∀x∀y∀z (y=z → y+x = z+x)" ) +:
        ( "plus1" -> hof"∀x x + s(0) = s(x)" ) +:
        ( "fs" -> hof"∀x f(s(x)) = f(x) + s(0)" ) +:
        ( "f0" -> hof"f 0 = 0" ) +:
        Sequent()
        :+ ( "goal" -> hof"f ${Numeral( n )} = ${Numeral( n )}" ) ) {
        repeat(
          explicitRewriteRight( "plus1", "goal" ) andThen
            explicitRewriteLeft( "fs", "goal" ) andThen
            chain( "congplusleft" ) )
        chain( "f0" )
      }
}

object SumOfOnesFExampleProof extends TacticsProof with ProofSequence with ExplicitEqualityTactics {
  ctx += Sort( "i" )
  ctx += hoc"s: i>i"
  ctx += hoc"0: i"
  ctx += hoc"'+': i>i>i"
  ctx += Notation.Infix( "+", Precedence.plusMinus )
  ctx += hoc"f: i>i"

  def apply( n: Int ) =
    Proof(
      ( "trans" -> hof"∀(x:i)∀y∀z (x=y ∧ y=z → x=z)" ) +:
        ( "congsuc" -> hof"∀x ∀y (x = y → s(x) = s(y))" ) +:
        ( "plus1" -> hof"∀x x + s(0) = s(x)" ) +:
        ( "fs" -> hof"∀x f(s(x)) = f(x) + s(0)" ) +:
        ( "f0" -> hof"f 0 = 0" ) +:
        Sequent()
        :+ ( "goal" -> hof"f ${Numeral( n )} = ${Numeral( n )}" ) ) {
        repeat(
          explicitRewriteLeft( "fs", "goal" ) andThen
            explicitRewriteLeft( "plus1", "goal" ) andThen
            chain( "congsuc" ) )
        chain( "f0" )
      }
}

/**
 * Functions to construct cut-free FOL LK proofs of the sequents
 *
 * Refl, Trans, CongSuc, ABase, ASuc, :- sum( n ) = s^n^(0)
 *
 * where n is an Integer parameter >= 0.
 */
object SumOfOnesExampleProof extends ProofSequence {
  import Utils.{ numeral => num }

  def apply( n: Int ) = {
    val goal = if ( n == 0 ) foa"0 = 0" else foa"${sum( n )} = ${num( n )}"
    val endSequent = Sequent(
      Seq(
        "Refl" -> ReflexivityEq,
        "Trans" -> TransitivityEq,
        "CongSuc" -> CongUnaryEq( "s" ),
        "ABase" -> Peano.AdditionBase,
        "ASuc" -> Peano.AdditionSucc ), Seq(
        "Goal" -> goal ) )

    n match {
      case 0 | 1 =>
        Proof( endSequent ) {
          allL( "Refl", num( n ) )
          prop
        }

      case _ =>
        val subProof = apply( n - 1 )
        Proof( endSequent ) {
          allL( "CongSuc", sum( n - 1 ), num( n - 1 ) )
          impL( "CongSuc_0" )
          insert( subProof )

          allL( "Trans", sum( n ), FOLFunction( "s", sum( n - 1 ) ), num( n ) ) //Trans_0
          impL( "Trans_0" )
          insert( aux_proof( n - 1 ) )

          impL( "Trans_0" )
          repeat( trivial )
        }
    }
  }

  /** constructs proof of: Trans, CongSuc, ASuc, ABase :- sum( k + 1 ) = s( sum( k ) ) */
  private def aux_proof( n: Int ): LKProof = {
    val goal = fof"${sum( n + 1 )} = s(${sum( n )})"
    val endSequent = Sequent(
      Seq(
        "Trans" -> TransitivityEq,
        "CongSuc" -> CongUnaryEq( "s" ),
        "ABase" -> Peano.AdditionBase,
        "ASuc" -> Peano.AdditionSucc ), Seq(
        "Goal" -> goal ) )

    Proof( endSequent ) {
      allL( "ABase", sum( n ) ) //ABase_0
      allL( "ASuc", sum( n ), num( 0 ) ) // ASuc_0
      allL( "CongSuc", fot"${sum( n )} + 0", sum( n ) ) // CongSuc_0
      impL( "CongSuc_0" )
      trivial

      allL( "Trans", sum( n + 1 ), fot"s(${sum( n )} +0)", fot"s(${sum( n )})" ) // Trans_0
      impL( "Trans_0" )
      trivial

      impL( "Trans_0" )
      repeat( trivial )
    }
  }

  // the term (.((1 + 1) + 1 ) + ... + 1 ), k must be at least 1
  private def sum( k: Int ): FOLTerm = {
    if ( k == 1 ) Utils.numeral( 1 )
    else FOLFunction( "+", sum( k - 1 ) :: Utils.numeral( 1 ) :: Nil )
  }
}

/**
 * Auxiliary structure to deal with axioms of the schema:
 * Forall variables cond1 -> cond2 -> ... -> condn -> consequence |- ...
 */
class AllQuantifiedConditionalAxiomHelper(
    variables: List[FOLVar], conditions: List[FOLAtom],
    consequence: FOLFormula ) {
  /**
   * Returns the full axiom
   */
  def getAxiom: FOLFormula = {
    // TODO: refactor apply_conditional_equality, combine duplicate code
    val impl_chain = ( conditions :\ consequence )( ( c, acc ) => Imp( c, acc ) )

    All.Block( variables, impl_chain )
  }

  /**
   * Use axiom with given expressions in proof.
   * Consequence of axiom must appear in current proof.
   * Instantiated conditions will of course remain in the antecedent of the returned proof
   */
  def apply( expressions: List[FOLTerm], p: LKProof ): LKProof = {
    assert( expressions.length == variables.length, "Number of expressions doesn't equal number of variables" )

    // construct implication with instantiated conditions and consequence
    val ( instantiated_conditions, instantiated_consequence ) =
      ( ( conditions -> consequence ) /: variables.indices ) { ( acc, i ) =>
        val substitute = ( x: FOLFormula ) => FOLSubstitution( variables( i ), expressions( i ) )( x )
        ( acc._1.map( substitute ).asInstanceOf[List[FOLAtom]], substitute( acc._2 ) )
      }

    val p1 = apply_conditional_equality( instantiated_conditions, instantiated_consequence, p )

    // iteratively instantiate all-quantified variables with expression
    def instantiate_axiom( expressions: List[FOLTerm], axiom: FOLFormula, p: LKProof ): LKProof = {
      expressions match {
        case Nil => p
        case head :: tail =>
          val new_axiom = instantiate( axiom, head )
          val new_p = instantiate_axiom( tail, new_axiom, p )

          ForallLeftRule( new_p, axiom, head )

      }
    }

    val ax = getAxiom
    val p2 = instantiate_axiom( expressions, ax, p1 )

    ContractionLeftRule( p2, ax )
  }

  private def apply_conditional_equality( equalities: List[FOLAtom], result: FOLFormula, p: LKProof ): LKProof = {
    equalities match {
      case Nil =>
        p // no conditions at all

      case head :: Nil =>
        val ax = LogicalAxiom( head )
        ImpLeftRule( ax, head, p, result )

      case head :: tail =>
        val ax = LogicalAxiom( head )
        val impl_chain = ( tail :\ result )( ( c, acc ) => Imp( c, acc ) )

        val s2 = apply_conditional_equality( tail, result, p )
        ImpLeftRule( ax, head, s2, impl_chain )

    }
  }
}

object UniformAssociativity3ExampleProof extends ProofSequence {

  val s = "s"
  val p = "+"

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val z = FOLVar( "z" )

  val x1 = FOLVar( "x_1" )
  val x2 = FOLVar( "x_2" )
  val y1 = FOLVar( "y_1" )
  val y2 = FOLVar( "y_2" )

  def f1( sym: String, arg: FOLTerm ) = FOLFunction( sym, arg :: Nil )
  def f2( sym: String, arg1: FOLTerm, arg2: FOLTerm ): FOLTerm = FOLFunction( sym, arg1 :: arg2 :: Nil )
  def f2( arg1: FOLTerm, sym: String, arg2: FOLTerm ): FOLTerm = f2( sym, arg1, arg2 )

  // Axioms

  // Trans as from TransRule, possibly unify or generalise
  val Trans = All( x, All( y, All( z, Imp( And( Eq( x, y ), Eq( y, z ) ), Eq( x, z ) ) ) ) )
  val Symm = All( x, Eq( x, x ) )
  val Cs = All( x, All( y, Imp( Eq( x, y ), Eq( FOLFunction( s, x :: Nil ), FOLFunction( s, y :: Nil ) ) ) ) )

  // TODO: port these axioms to new format using AllQuantifiedConditionalAxiomHelper
  def refl_ax(): FOLFormula = All( x, refl_ax( x ) )
  def refl_ax( x: FOLTerm ): FOLFormula = All( y, refl_ax( x, y ) )
  def refl_ax( x: FOLTerm, y: FOLTerm ): FOLFormula = Imp( Eq( x, y ), Eq( y, x ) )

  // x=y -> s(x) = s(y)
  def cs_ax(): FOLFormula = All( x, cs_ax( x ) )
  def cs_ax( x: FOLTerm ): FOLFormula = All( y, cs_ax( x, y ) )
  def cs_ax( x: FOLTerm, y: FOLTerm ): FOLFormula =
    Imp( Eq( x, y ), Eq( FOLFunction( s, x :: Nil ), FOLFunction( s, y :: Nil ) ) )

  // x1 = x2 -> y1 = y2 -> x1 + y1 = x2 + y2
  val cp = new AllQuantifiedConditionalAxiomHelper(
    x1 :: x2 :: y1 :: y2 :: Nil,
    Eq( x1, x2 ) :: Eq( y1, y2 ) :: Nil,
    Eq( FOLFunction( p, x1 :: y1 :: Nil ), FOLFunction( p, x2 :: y2 :: Nil ) ) )

  // Arithmetic axioms
  val Ax1 = All( x, Eq( FOLFunction( p, x :: Utils.numeral( 0 ) :: Nil ), x ) )

  // Forall x, y: s(x+y) = x+s(y)
  def ax2_ax(): FOLFormula = All( x, All( y, ax2_ax( x, y ) ) )
  def ax2_ax( x: FOLTerm ): FOLFormula = All( y, ax2_ax( x, y ) )
  def ax2_ax( x: FOLTerm, y: FOLTerm ): FOLFormula =
    Eq( f1( s, f2( x, p, y ) ), f2( x, p, f1( s, y ) ) )

  def addAllAxioms( proof: LKProof ): LKProof =
    Seq( Trans, cp.getAxiom, Symm, ax2_ax(), cs_ax(), refl_ax(), Ax1 ).foldLeft( proof )( WeakeningLeftRule( _, _ ) )

  def apply( n: Int ): LKProof = {
    assert( n >= 0, "n must be >= 0" )
    val proof = if ( n > 0 ) {
      gen_proof_step( 0, n )
    } else {
      val zero = Utils.numeral( 0 )
      val c1 = f2( f2( zero, p, zero ), p, zero )
      val e1 = f2( zero, p, f2( zero, p, zero ) )
      addAllAxioms( LogicalAxiom( Eq( c1, e1 ) ) )
    }
    induction_start( n, proof )
  }

  /**
   * Close off proof ending in (n + n) + 0 = n + (n + 0) |- ...
   */
  def induction_start( n: Int, p0: LKProof ): LKProof = {
    // show both sides equal to n + n
    val n_num = Utils.numeral( n )
    val zero = Utils.numeral( 0 )
    val c1 = f2( f2( n_num, p, n_num ), p, zero )
    val d1 = f2( n_num, p, n_num )
    val e1 = f2( n_num, p, f2( n_num, p, zero ) )
    val p1 = TransRule( c1, d1, e1, p0 )

    // show (n + n) + 0 = (n + n) directly via ax1
    val p2 = ForallLeftRule( p1, Ax1, d1 )
    val p3 = ContractionLeftRule( p2, Ax1 )

    // show (n + n) = n + (n + 0)
    val p4 = cp( n_num :: n_num :: n_num :: f2( n_num, p, zero ) :: Nil, p3 )

    // show n = n and n = n + 0
    val p5 = ForallLeftRule( p4, Symm, n_num )
    val p6 = ContractionLeftRule( p5, Symm )

    val p7 = reflect( f2( n_num, p, zero ), n_num, p6 )

    val p8 = ForallLeftRule( p7, Ax1, n_num )
    ContractionLeftRule( p8, Ax1 )
  }

  /**
   * *
   * Returns proof Pi (currently including line above and below Pi), with numerals n, i, i+1:
   * (n + n) + i+1 = n + (n + i+1), Ax |- ...
   *  Pi
   * (n + n) + i   = n + (n + i), Ax |- ...
   */
  def gen_proof_step( i: Int, n: Int ): LKProof = {
    val n_num = Utils.numeral( n )
    val i_num = Utils.numeral( i )
    val ip1_num = Utils.numeral( i + 1 )

    val a1 = f2( f2( n_num, p, n_num ), p, ip1_num )
    val a2 = f2( n_num, p, f2( n_num, p, ip1_num ) )
    val b1 = f2( n_num, p, f1( s, f2( p, n_num, i_num ) ) )

    val p0 =
      if ( i + 1 >= n ) {
        val final_expression = Eq( a1, a2 )

        val top = LogicalAxiom( final_expression )
        addAllAxioms( top )
      } else {
        gen_proof_step( i + 1, n )
      }

    val p1 = TransRule( a1, b1, a2, p0 )

    // the left side now contains
    // (n + n) + s(i) = n + s(n + i) as well as
    // n + s(n + i) = n + (n + s(i))

    // use Cp to reduce the latter to s(n + i) = (n + s(i))
    val x1_1 = n_num
    val x2_1 = n_num
    val y1_1 = f1( s, f2( n_num, p, i_num ) )
    val y2_1 = f2( n_num, p, f1( s, i_num ) )
    val p8 = cp( x1_1 :: x2_1 :: y1_1 :: y2_1 :: Nil, p1 )

    // show x1 = x2 by symmetry
    val p9 = ForallLeftRule( p8, Symm, n_num )
    val p10 = ContractionLeftRule( p9, Symm )

    // show y1 = y2 by Ax2 (i.e. s(n + i) = (n + s(i)) )
    val p13 = show_by_ax2( n_num, i_num, p10 )

    // now we only have (n + n) + s(i) = n + s(n + i) left (c=e),
    // reduce right hand side by Ax2 and Trans to s(n + (n + i) (c=d) )
    val c1 = f2( f2( n_num, p, n_num ), p, f1( s, i_num ) )
    val d1 = f1( s, f2( n_num, p, f2( n_num, p, i_num ) ) )
    val e1 = f2( n_num, p, f1( s, f2( n_num, p, i_num ) ) )
    val p14 = TransRule( c1, d1, e1, p13 )

    // show d=e by Ax2
    val p15 = show_by_ax2( n_num, f2( n_num, p, i_num ), p14 )

    // next goal: reduce (n + n) + s(i) = s(n + (n + i) to (n + n) + s(i) = s( (n + n) + i) using the IH, Trans and Cs)
    val c2 = f2( f2( n_num, p, n_num ), p, f1( s, i_num ) )
    val d2 = f1( s, f2( f2( n_num, p, n_num ), p, i_num ) )
    val e2 = d1
    val p16 = TransRule( c2, d2, e2, p15 )

    val p17 = show_by_cs( f2( f2( n_num, p, n_num ), p, i_num ), f2( n_num, p, f2( n_num, p, i_num ) ), p16 )

    // now we have:
    // (n + n) + s(i) = s( (n + n) + i)
    // as well as
    // (n + n) + i = n + (n + i)
    // -> use Ax2

    // use reflection to match definition of ax2 afterwards
    val p18 = reflect( d2, c2, p17 )

    val p19 = show_by_ax2( f2( n_num, p, n_num ), i_num, p18 )
    p19

    // we end up with the IH (n + n) + i = n + (n + i)
  }

  def show_by_ax2( x: FOLTerm, y: FOLTerm, p: LKProof ): LKProof = {
    val p1 = ForallLeftRule( p, ax2_ax( x ), y )
    val p2 = ForallLeftRule( p1, ax2_ax(), x )
    ContractionLeftRule( p2, ax2_ax() )
  }

  def show_by_cs( x: FOLTerm, y: FOLTerm, p: LKProof ): LKProof = {
    val p1 = apply_conditional_equality(
      Eq( x, y ) :: Nil,
      Eq( FOLFunction( s, x :: Nil ), FOLFunction( s, y :: Nil ) ), p )

    val p2 = ForallLeftRule( p1, cs_ax( x ), y )
    val p3 = ForallLeftRule( p2, cs_ax(), x )
    ContractionLeftRule( p3, cs_ax() )
  }

  /**
   * Takes a proof s2 with end-sequent of the form
   * (x=y), ... |- ...
   * and return one with end-sequent of the form
   * (y=x), ... |- ...
   */
  def reflect( x: FOLTerm, y: FOLTerm, p: LKProof ): LKProof = {
    val p1 = apply_conditional_equality( Eq( x, y ) :: Nil, Eq( y, x ), p )

    val p2 = ForallLeftRule( p1, refl_ax( x ), y )
    val p3 = ForallLeftRule( p2, refl_ax(), x )
    ContractionLeftRule( p3, refl_ax() )
  }

  def apply_conditional_equality( equalities: List[FOLFormula], result: FOLFormula, p: LKProof ): LKProof = {
    equalities match {
      case Nil => p
      case head :: Nil => {
        val ax = LogicalAxiom( head )
        ImpLeftRule( ax, head, p, result )
      }
      case head :: tail => {
        val ax = LogicalAxiom( head )
        var impl_chain = result
        for ( elem <- tail.reverse ) {
          impl_chain = Imp( elem, impl_chain )
        }
        val s2 = apply_conditional_equality( tail, result, p )
        ImpLeftRule( ax, head, s2, impl_chain )
      }
    }
  }
}

/**
 * Proof of f(n) = g(n, 1), where f is the head recursive and
 * g the tail recursive formulation of the factorial function
 */
object FactorialFunctionEqualityExampleProof extends ProofSequence {

  val p = "+"
  val m = "*"
  val s = "s"
  val f = "f"
  val g = "g"

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val z = FOLVar( "z" )

  def f1( sym: String, arg: FOLTerm ) = FOLFunction( sym, arg :: Nil )
  def f2( sym: String, arg1: FOLTerm, arg2: FOLTerm ): FOLTerm = FOLFunction( sym, arg1 :: arg2 :: Nil )
  def f2( arg1: FOLTerm, sym: String, arg2: FOLTerm ): FOLTerm = f2( sym, arg1, arg2 )

  val f_ax_1 = Eq( f1( f, Utils.numeral( 0 ) ), f1( s, Utils.numeral( 0 ) ) )
  val f_ax_2 = fof"!x f(s(x)) = s(x) * f(x)"

  val g_ax_1 = new AllQuantifiedConditionalAxiomHelper( y :: Nil, Nil,
    Eq( y, f2( g, Utils.numeral( 0 ), y ) ) )
  val g_ax_2 = fof"!x!y g(s(x), y) = g(x, y * s(x))"

  val g_compat_2 = new AllQuantifiedConditionalAxiomHelper(
    x :: y :: z :: Nil,
    Eq( y, z ) :: Nil, Eq( f2( g, x, y ), f2( g, x, z ) ) )

  val trans_axiom = new AllQuantifiedConditionalAxiomHelper(
    x :: y :: z :: Nil,
    Eq( x, y ) :: Eq( y, z ) :: Nil, Eq( x, z ) )
  val symm_axiom = All( x, Eq( x, x ) )
  val refl_axiom = new AllQuantifiedConditionalAxiomHelper(
    x :: y :: Nil,
    Eq( x, y ) :: Nil, Eq( y, x ) )
  val compat_mul_axiom = new AllQuantifiedConditionalAxiomHelper(
    x :: y :: z :: Nil,
    Eq( x, y ) :: Nil, Eq( f2( z, m, x ), f2( z, m, y ) ) )
  val assoc_mul_axiom = new AllQuantifiedConditionalAxiomHelper( x :: y :: z :: Nil, Nil,
    Eq( f2( x, m, f2( y, m, z ) ), f2( f2( x, m, y ), m, z ) ) )

  val mul_neutral_axiom = new AllQuantifiedConditionalAxiomHelper( x :: Nil, Nil,
    Eq( f2( x, m, Utils.numeral( 1 ) ), x ) )
  // this second axiom saves us from adding commutativity of multiplication
  val mul_neutral_axiom_2 = new AllQuantifiedConditionalAxiomHelper( x :: Nil, Nil,
    Eq( f2( Utils.numeral( 1 ), m, x ), x ) )

  def apply( n: Int ): LKProof = n match {
    case 0 =>
      val targetEquation = Eq( f1( f, Utils.numeral( 0 ) ), f2( g, Utils.numeral( 0 ), Utils.numeral( 1 ) ) )
      val g0 = Eq( Utils.numeral( 1 ), f2( g, Utils.numeral( 0 ), Utils.numeral( 1 ) ) )
      val ax1 = LogicalAxiom( f_ax_1 )
      val ax2 = LogicalAxiom( g0 )
      val ax3 = LogicalAxiom( targetEquation )
      val p1 = ImpLeftRule( ax2, g0, ax3, targetEquation )
      val p2 = ImpLeftRule( ax1, f_ax_1, p1, Imp( g0, targetEquation ) )
      val p3 = ForallLeftBlock( p2, trans_axiom.getAxiom,
        Seq( f1( f, Utils.numeral( 0 ) ), Utils.numeral( 1 ), f2( g, Utils.numeral( 0 ), Utils.numeral( 1 ) ) ) )
      val p4 = ForallLeftRule( p3, g_ax_1.getAxiom, Utils.numeral( 1 ) )
      WeakeningLeftMacroRule(
        p4,
        List( f_ax_2, g_ax_2, symm_axiom, refl_axiom.getAxiom,
          compat_mul_axiom.getAxiom, assoc_mul_axiom.getAxiom, g_compat_2.getAxiom,
          mul_neutral_axiom.getAxiom, mul_neutral_axiom_2.getAxiom ) )
    case _ => induction_steps( n )
  }

  def induction_steps( n: Int ): LKProof = {
    val axiom = LogicalAxiom( Eq( f1( f, Utils.numeral( n ) ), f2( g, Utils.numeral( n ), Utils.numeral( 1 ) ) ) )

    // add axioms
    val all_axioms = List[FOLFormula]( f_ax_1, f_ax_2, g_ax_1.getAxiom, g_ax_2, symm_axiom, refl_axiom.getAxiom,
      trans_axiom.getAxiom, compat_mul_axiom.getAxiom, assoc_mul_axiom.getAxiom, g_compat_2.getAxiom,
      mul_neutral_axiom.getAxiom, mul_neutral_axiom_2.getAxiom )
    val p1 = all_axioms.foldLeft[LKProof]( axiom )( ( proof, elem ) => WeakeningLeftRule( proof, elem ) )

    val n_num = Utils.numeral( n )

    /**
     * Returns (( ([start_value*]n)*(n-1) ) * ... * ) k
     */
    def get_partial_factorial_term( n: Int, k: Int, start_value: Option[FOLTerm] = None ): FOLTerm = {
      if ( n <= k ) {
        if ( n == k ) {
          start_value match {
            case Some( value ) => f2( value, m, Utils.numeral( n ) )
            case None          => Utils.numeral( n )
          }
        } else throw new Exception( "k larger than n in partial factorial" )
      } else {
        f2( m, get_partial_factorial_term( n, k + 1, start_value ), Utils.numeral( k ) )
      }
    }

    def induction_step_rec( p0: LKProof, k: Int ): LKProof = {

      val k_num = Utils.numeral( k )
      val zero = Utils.numeral( 0 )
      val one = Utils.numeral( 1 )

      val part_fac = if ( n == k ) one else get_partial_factorial_term( n, k + 1 )
      val part_fac_next = get_partial_factorial_term( n, k )

      val f_k_term = if ( n == k ) f1( f, k_num ) // f(k)
      else f2( m, part_fac, f1( f, k_num ) ) // part_fac * f(k)

      val g_k_term = f2( g, k_num, part_fac )

      if ( k == 0 ) {
        // we have: n! * f(0) = g(0, ( ... (( (1 * n) * (n-1) ) * (n-2) ) * ... ) * 1 )

        // use f(0) = s(0)
        val p1 = trans_axiom( List( f_k_term, f2( part_fac, m, f1( s, zero ) ), g_k_term ), p0 )
        val p2 = compat_mul_axiom( List( f1( f, zero ), f1( s, zero ), part_fac ), p1 )
        val p3 = ContractionLeftRule( p2, f_ax_1 )

        // use g(0, y) = y
        val p4 = trans_axiom( List( f2( part_fac, m, f1( s, zero ) ), part_fac, g_k_term ), p3 )
        val p5 = g_ax_1( part_fac :: Nil, p4 )

        // the formula actually says n! * 1 = n!, we have to get rid of the 1
        val p6 = trans_axiom( List( f2( part_fac, m, one ), part_fac, part_fac ), p5 )
        val p7 = mul_neutral_axiom( List( part_fac ), p6 )
        val p8 = ForallLeftRule( p7, symm_axiom, part_fac )
        val p9 = ContractionLeftRule( p8, symm_axiom )

        p9
      } else {
        // lhs contains part_fac * f(k) = g(k, part_fac)

        val km1_num = Utils.numeral( k - 1 ) // must not be evaluated for k == 0
        val f_km1_term = f2( m, part_fac_next, f1( f, km1_num ) ) // (part_fac * k) * f(k-1)
        val g_km1_term = f2( g, km1_num, part_fac_next )

        // first step: decompose f: part_fac * k * f(k-1) = g(k, 1*part_fac)
        val p1 = trans_axiom( List( f_k_term, f_km1_term, g_k_term ), p0 )

        val p3 =
          if ( n == k ) {
            // use axiom directly, part_fac is empty
            val p1_0 = ForallLeftRule( p1, f_ax_2, km1_num )
            ContractionLeftRule( p1_0, f_ax_2 )
          } else {
            // the antecedent contains something along the lines of:
            // 4*f(3) = (4*3) * f(2) or
            // (4*3)*f(2) = ((4*3)*2) * f(1)
            // we however need the last part exposed and grouped to be able
            // to use compat & f_ax2 to show it, like in: 4*f(3) = 4* (3*f(2))
            // use Trans to expose it and show it, other part can be shown by associativity
            // step in between (=yTrans):
            // 4 * (3*f(2)) or
            // (4*3) * (2*f(1))
            val yTrans = f2( part_fac, m, f2( k_num, m, f1( f, km1_num ) ) )
            val p1_0 = trans_axiom( f_k_term :: yTrans :: f_km1_term :: Nil, p1 )
            // show by compat, then f_ax_2: part_fac * f(k) = part_fac * (k * f(k-1))
            val f_k = f1( f, k_num )
            val k_f_km1 = f2( k_num, m, f1( f, km1_num ) )
            val p1_1 = compat_mul_axiom( List( f_k, k_f_km1, part_fac ), p1_0 )
            val p1_2 = ForallLeftRule( p1_1, f_ax_2, km1_num )
            val p1_3 = ContractionLeftRule( p1_2, f_ax_2 )
            // show by assoc: part_fac * (k * f(k-1)) = (part_fac * k) * f(k-1)
            val p1_4 = assoc_mul_axiom( List( part_fac, k_num, f1( f, km1_num ) ), p1_3 )
            p1_4
          }

        // now transform k * f(k-1) = g(k, part_fac) to k * f(k-1) = g(k-1, part_fac * k)
        val p4 = trans_axiom( List( f_km1_term, g_km1_term, g_k_term ), p3 )

        // show g(k, part_fac) = g(k-1, part_fac*k) (need to use reflection to get to this form first)
        val p4_2 = refl_axiom( g_k_term :: g_km1_term :: Nil, p4 )

        val p5 =
          if ( n == k ) {
            // g is initially called with a 1 as second argument, but we want to get rid of it
            // to make the final result equal to the one f produces
            // use trans to split into g-axiom part and part where the two expressions only differ by this extra one
            val g_intermed = f2( g, km1_num, f2( one, m, part_fac_next ) )
            val p5_1 = trans_axiom( g_k_term :: g_intermed :: g_km1_term :: Nil, p4_2 )
            // show g(n, 1) = g(n-1, 1*n) by g_ax_2
            val intermed = All( y, Eq( f2( g, k_num, y ), f2( g, km1_num, f2( y, m, k_num ) ) ) )
            val p5_2 = ForallLeftRule( p5_1, intermed, one )
            val p5_3 = ForallLeftRule( p5_2, g_ax_2, km1_num )
            val p5_4 = ContractionLeftRule( p5_3, g_ax_2 )

            // show g(n-1, 1*n) = g(n-1, n) by g_compat_2
            val p5_5 = g_compat_2( List( km1_num, f2( one, m, k_num ), k_num ), p5_4 )
            // show 1 * k = k
            val p5_6 = mul_neutral_axiom_2( List( k_num ), p5_5 )
            p5_6
          } else {
            val intermed = All( y, Eq(
              f2( g, f1( s, km1_num ), y ),
              f2( g, km1_num, f2( m, y, f1( s, km1_num ) ) ) ) )
            val p6 = ForallLeftRule( p4_2, intermed, part_fac )
            val p7 = ForallLeftRule( p6, g_ax_2, km1_num )
            val p8 = ContractionLeftRule( p7, g_ax_2 )
            p8
          }

        induction_step_rec( p5, k - 1 )
      }
    }

    induction_step_rec( p1, n )
  }
}

object FactorialFunctionEqualityExampleProof2 extends ProofSequence {
  import gapt.expr.fol.Utils.{ numeral => num }

  val zero = FOLConst( "0" )
  val one = s( zero )
  val alpha = FOLVar( "α" )
  val beta = FOLVar( "β" )
  val nu = FOLVar( "ν" )
  val gamma = FOLVar( "γ" )

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val z = FOLVar( "z" )
  val w = FOLVar( "w" )

  def s( x: FOLTerm ) = FOLFunction( "s", List( x ) )
  def m( x: FOLTerm, y: FOLTerm ) = FOLFunction( "*", x, y )
  def f( x: FOLTerm ) = FOLFunction( "f", List( x ) )
  def g( x: FOLTerm, y: FOLTerm ) = FOLFunction( "g", x, y )

  def f0 = Eq( f( zero ), s( zero ) )
  def fST( x: FOLTerm ) = Eq( f( s( x ) ), m( s( x ), f( x ) ) )
  def g0( x: FOLTerm ) = Eq( g( x, zero ), x )
  def gST( x: FOLTerm, y: FOLTerm ) = Eq( g( x, s( y ) ), g( m( x, s( y ) ), y ) )
  def uR( x: FOLTerm ) = Eq( m( x, s( zero ) ), x )
  def uL( x: FOLTerm ) = Eq( m( s( zero ), x ), x )
  def ASSO( x: FOLTerm, y: FOLTerm, z: FOLTerm ) = Eq( m( m( x, y ), z ), m( x, m( y, z ) ) )
  def target( x: FOLTerm ) = Eq( f( x ), g( s( zero ), x ) )

  def apply( n: Int ): LKProof = {
    /**
     * Computes 1 * n * (n- 1) * … * k, associated to the left.
     *
     */
    def product( k: Int ) =
      ( one /: ( k until n + 1 ).reverse ) { ( acc: FOLTerm, i: Int ) =>
        m( acc, num( i ) )
      }

    /*val axiom = ReflexivityAxiom( product( 1 ) )

    val p1 = ParamodulationRightRule( LogicalAxiom( uR( product( 1 ) ) ),
     uR( product( 1 ) ), axiom, Eq( product( 1 ), product( 1 ) ), Eq( m( product( 1 ), one ), product( 1 ) ) )
    val p2 = ParamodulationRightRule( LogicalAxiom( f0 ), f0, p1, Eq( m( product( 1 ), one ), product( 1 ) ),
     Eq( m( product( 1 ), f( zero ) ), product( 1 ) ) )
    val p3 = ParamodulationRightRule( LogicalAxiom( g0( product( 1 ) ) ),
     g0( product( 1 ) ), p2, Eq( m( product( 1 ), f( zero ) ), product( 1 ) ),
      Eq( m( product( 1 ), f( zero ) ), g( product( 1 ), zero ) ) )
    val p4 = ForallLeftRule( p3, All( x, uR( x ) ), product( 1 ) )
    val p5 = ForallLeftRule( p4, All( x, g0( x ) ), product( 1 ) )

    val p6 = ( 0 until n ).foldLeft[LKProof]( p5 ) { ( acc: LKProof, i: Int ) =>
      val tmp1 = ParamodulationRightRule( LogicalAxiom( ASSO( product( i + 2 ), num( i + 1 ), f( num( i ) ) ) ),
       ASSO( product( i + 2 ), num( i + 1 ), f( num( i ) ) ), acc,
       Eq( m( product( i + 1 ), f( num( i ) ) ), g( product( i + 1 ), num( i ) ) ),
       Eq( m( product( i + 2 ), m( num( i + 1 ), f( num( i ) ) ) ), g( product( i + 1 ), num( i ) ) ) )
      val tmp2 = ForallLeftBlock( tmp1, univclosure( ASSO( x, y, z ) ),
       List( product( i + 2 ), num( i + 1 ), f( num( i ) ) ) )
      val tmp3 = ParamodulationRightRule( LogicalAxiom( fST( num( i ) ) ), fST( num( i ) ),
       tmp2, Eq( m( product( i + 2 ), m( num( i + 1 ), f( num( i ) ) ) ), g( product( i + 1 ), num( i ) ) ),
        Eq( m( product( i + 2 ), f( num( i + 1 ) ) ), g( product( i + 1 ), num( i ) ) ) )
      val tmp4 = ParamodulationRightRule( LogicalAxiom( gST( product( i + 2 ), num( i ) ) ),
       gST( product( i + 2 ), num( i ) ), tmp3, Eq( m( product( i + 2 ), f( num( i + 1 ) ) ),
        g( product( i + 1 ), num( i ) ) ), Eq( m( product( i + 2 ), f( num( i + 1 ) ) ),
        g( product( i + 2 ), num( i + 1 ) ) ) )
      val tmp5 = ForallLeftRule( tmp4, univclosure( fST( x ) ), num( i ) )
      val tmp6 = ForallLeftBlock( tmp5, univclosure( gST( x, y ) ), List( product( i + 2 ), num( i ) ) )
      ContractionMacroRule( tmp6 )
    }

    val p7 = ParamodulationRightRule( LogicalAxiom( uL( f( num( n ) ) ) ),
     uL( f( num( n ) ) ), p6, Eq( m( one, f( num( n ) ) ), g( one, num( n ) ) ), target( num( n ) ) )
    WeakeningContractionMacroRule( ForallLeftRule( p7, All( x, uL( x ) ), f( num( n ) ) ), endSequent( n ) )
*/
    val p1 = ( ProofBuilder
      c ReflexivityAxiom( product( 1 ) )
      u ( WeakeningLeftMacroRule( _, Seq( uR( product( 1 ) ), f0, g0( product( 1 ) ) ) ) )
      u ( EqualityRightRule( _, uR( product( 1 ) ), Eq( product( 1 ), product( 1 ) ),
        Eq( m( product( 1 ), one ), product( 1 ) ) ) )
        u ( EqualityRightRule( _, f0, Eq( m( product( 1 ), one ), product( 1 ) ),
          Eq( m( product( 1 ), f( zero ) ), product( 1 ) ) ) )
          u ( EqualityRightRule( _, g0( product( 1 ) ),
            Eq( m( product( 1 ), f( zero ) ), product( 1 ) ),
            Eq( m( product( 1 ), f( zero ) ), g( product( 1 ), zero ) ) ) )
            u ( ForallLeftRule( _, All( x, uR( x ) ), product( 1 ) ) )
            u ( ForallLeftRule( _, All( x, g0( x ) ), product( 1 ) ) ) qed )

    val p2 = ( 0 until n ).foldLeft[LKProof]( p1 ) { ( acc: LKProof, i: Int ) =>
      ( ProofBuilder
        c acc
        u ( WeakeningLeftMacroRule( _, Seq(
          ASSO( product( i + 2 ), num( i + 1 ), f( num( i ) ) ),
          fST( num( i ) ),
          gST( product( i + 2 ), num( i ) ) ) ) )
        u ( EqualityRightRule( _, ASSO( product( i + 2 ), num( i + 1 ), f( num( i ) ) ),
          Eq( m( product( i + 1 ), f( num( i ) ) ), g( product( i + 1 ), num( i ) ) ),
          Eq( m( product( i + 2 ), m( num( i + 1 ), f( num( i ) ) ) ), g( product( i + 1 ), num( i ) ) ) ) )
          u ( macros.ForallLeftBlock( _, universalClosure( ASSO( x, y, z ) ),
            List( product( i + 2 ), num( i + 1 ), f( num( i ) ) ) ) )
            u ( EqualityRightRule( _, fST( num( i ) ),
              Eq( m( product( i + 2 ), m( num( i + 1 ), f( num( i ) ) ) ), g( product( i + 1 ), num( i ) ) ),
              Eq( m( product( i + 2 ), f( num( i + 1 ) ) ), g( product( i + 1 ), num( i ) ) ) ) )
              u ( EqualityRightRule( _, gST( product( i + 2 ), num( i ) ),
                Eq( m( product( i + 2 ), f( num( i + 1 ) ) ), g( product( i + 1 ), num( i ) ) ),
                Eq( m( product( i + 2 ), f( num( i + 1 ) ) ), g( product( i + 2 ), num( i + 1 ) ) ) ) )
                u ( ForallLeftRule( _, universalClosure( fST( x ) ), num( i ) ) )
                u ( rules.macros.ForallLeftBlock( _, universalClosure( gST( x, y ) ), List( product( i + 2 ), num( i ) ) ) )
                u ( ContractionMacroRule( _ ) ) qed )
    }

    ( ProofBuilder
      c p2
      u ( WeakeningLeftRule( _, uL( f( num( n ) ) ) ) )
      u ( EqualityRightRule( _, uL( f( num( n ) ) ),
        Eq( m( one, f( num( n ) ) ), g( one, num( n ) ) ),
        target( num( n ) ) ) )
        u ( ForallLeftRule( _, All( x, uL( x ) ), f( num( n ) ) ) )
        u ( WeakeningContractionMacroRule( _, endSequent( n ) ) ) qed )
  }

  def endSequent( n: Int ): HOLSequent = HOLSequent(
    List(
      f0,
      fST( x ),
      g0( x ),
      gST( x, y ),
      uR( x ),
      uL( x ),
      ASSO( x, y, z ) ) map universalClosure.apply,
    List(
      target( num( n ) ) ) )
}

