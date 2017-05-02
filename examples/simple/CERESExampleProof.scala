package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lk._

object CERESExpansionExampleProof {
  val c = FOLConst( "c" )
  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val z = FOLVar( "z" )

  def f( x: FOLTerm ) = FOLFunction( "f", List( x ) )
  def g( x: FOLTerm ) = FOLFunction( "g", List( x ) )
  def P( x: FOLTerm ) = FOLFunction( "P", List( x ) )

  def ax1 = Eq( f( f( z ) ), g( z ) )
  def seq = Sequent( Seq(), Seq( ax1 ) )

  val proof = {

    val p5 = ImpLeftRule( LogicalAxiom( fof"P(c)" ), fof"P(c)", ImpLeftRule( LogicalAxiom( fof"P(g(c))" ), fof"P(g(c))", LogicalAxiom( fof"P(g(g(c)))" ), fof"P(g(g(c)))" ), fof"P(g(c))" )

    val p8 = ContractionLeftRule( ForallLeftRule( ForallLeftRule( p5, fof"!x (P(x)->P(g(x)))", c ), fof"!x (P(x)->P(g(x)))", g( c ) ), fof"!x (P(x)->P(g(x)))" )

    val p11 = ParamodulationRightRule( TheoryAxiom( seq ), ax1, LogicalAxiom( fof"P(f(f(z)))" ), fof"P(f(f(z)))", fof"P(g(z))" )

    val p15 = ImpLeftRule( LogicalAxiom( fof"P(z)" ), fof"P(z)", ImpLeftRule( LogicalAxiom( fof"P(f(z))" ), fof"P(f(z))", p11, fof"P(f(f(z)))" ), fof"P(f(z))" )

    val p18 = ContractionLeftRule( ForallLeftRule( ForallLeftRule( p15, fof"!x (P(x)->P(f(x)))", z ), fof"!x (P(x)->P(f(x)))", f( z ) ), fof"!x (P(x)->P(f(x)))" )

    val p19 = ImpRightRule( p18, fof"P(z)", fof"P(g(z))" )

    CutRule( ForallRightRule( p19, fof"!x (P(x)->P(g(x)))", z ), fof"!x (P(x)->P(g(x)))", p8, fof"!x (P(x)->P(g(x)))" )

  }
}
