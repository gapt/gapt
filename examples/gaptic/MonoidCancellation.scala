package at.logic.gapt.examples
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.universalClosure
import at.logic.gapt.formats.babel.{ Notation, Precedence }
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKProof

/**
 * Monoid cancellation benchmark from
 * Gregory Malecha and Jesper Bengtson: Extensible and Efficient Automation Through Reflective Tactics, ESOP 2016.
 */
object MonoidCancellation extends TacticsProof {
  ctx += Context.Sort( "m" )
  ctx += hoc"'*': m>m>m"
  ctx += Notation.Infix( "*", Precedence.timesDiv )
  ctx += hoc"1: m"

  ctx += "mul_assoc" -> hcl":- (x*y)*z = x*(y*z)"
  ctx += "mul_comm" -> hcl":- x*y = y*x"
  ctx += "one_mul" -> hcl":- 1*x = x"

  val setup: Tactic[Unit] = {
    def mkAux( formula: Formula ) =
      Proof( Sequent() :+ ( "goal" -> universalClosure( formula ) ) ) {
        decompose
        foTheory
      }

    val plus_unit_p = mkAux( hof"a = b -> 1 * a = b" )
    val plus_assoc_p1 = mkAux( hof"a * (b * c) = d -> (a * b) * c = d" )
    val plus_assoc_p2 = mkAux( hof"b * (a * c) = d -> (a * b) * c = d" )
    val plus_comm_p = mkAux( hof"a * b = c -> b * a = c" )

    val plus_unit_c = mkAux( hof"a = b -> a = 1 * b" )
    val plus_assoc_c1 = mkAux( hof"d = a * (b * c) -> (a * b) * c = d" )
    val plus_assoc_c2 = mkAux( hof"d = b * (a * c) -> (a * b) * c = d" )
    val plus_comm_c = mkAux( hof"c = a * b -> c = b * a" )

    val plus_cancel = mkAux( hof"a = c -> b = d -> a * b = c * d" )

    Tactic {
      include( "plus_unit_p", plus_unit_p ) andThen
        include( "plus_assoc_p1", plus_assoc_p1 ) andThen
        include( "plus_assoc_p2", plus_assoc_p2 ) andThen
        include( "plus_comm_p", plus_comm_p ) andThen
        include( "plus_unit_c", plus_unit_c ) andThen
        include( "plus_assoc_c1", plus_assoc_c1 ) andThen
        include( "plus_assoc_c2", plus_assoc_c2 ) andThen
        include( "plus_comm_c", plus_comm_c ) andThen
        include( "plus_cancel", plus_cancel ) andThen
        skip
    }
  }

  lazy val iterRight: Tactic[Unit] = Tactic {
    chain( "plus_unit_c" ) orElse
      chain( "plus_assoc_c1" ).andThen( iterRight ) orElse
      chain( "plus_assoc_c2" ).andThen( iterRight ) orElse
      chain( "plus_cancel" ).andThen( refl )
  }

  lazy val iterLeft: Tactic[Unit] = Tactic {
    chain( "plus_unit_p" ) orElse
      chain( "plus_assoc_p1" ).andThen( iterRight ) orElse
      chain( "plus_assoc_p2" ).andThen( iterRight ) orElse
      iterRight orElse chain( "plus_comm_p" ).andThen( iterRight )
  }

  lazy val cancel: Tactic[Unit] = Tactic {
    iterLeft orElse chain( "plus_comm_c" ).andThen( iterLeft )
  }

  val solve: Tactic[Unit] = Tactic {
    setup andThen
      repeat( refl orElse cancel )
  }

  Proof( hols":- a*(b*c) = (b*a)*c" ) { solve }

  def benchmarkFormula( n: Int ): Formula = {
    def buildL( n: Int ): Expr = {
      val x = Var( s"x$n", TBase( "m" ) )
      if ( n == 0 ) x else le"$x * ${buildL( n - 1 )}"
    }
    def buildR( n: Int ): Expr = {
      val x = Var( s"x$n", TBase( "m" ) )
      if ( n == 0 ) x else le"${buildL( n - 1 )} * $x"
    }
    hof"${buildL( n )} = ${buildR( n )}"
  }

  def proveBenchmark( n: Int ): LKProof =
    Proof( hols":- ${benchmarkFormula( n )}" ) { solve }

  def runBenchmark( n: Int ): Unit =
    ctx.check( proveBenchmark( n ) )

}