package at.logic.gapt.examples

import at.logic.gapt.proofs.nd._
import at.logic.gapt.expr._

// Should give an exception.
object logicalAxiom1 extends Script {
  val a1 = LogicalAxiom( hof"P(x)" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type " ); println( m1.ty )
}

object logicalAxiom2 extends Script {
  val a1 = LogicalAxiom( hof"0 = s(0) & 0 + 0 = 0" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type " ); println( m1.ty )
}

object logicalAxiom3 extends Script {
  val a1 = LogicalAxiom( hof"!x ?y ( x * 0 = y -> y = s(0))" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type " ); println( m1.ty )
}

object logicalAxiom4 extends Script {
  val a1 = LogicalAxiom( hof"x = y" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type " ); println( m1.ty )
}

object theoryAxiom1 extends Script {
  val a1 = TheoryAxiom( hof"!z (s(z) = 0 -> ⊥)" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type " ); println( m1.ty )
}

object theoryAxiom2 extends Script {
  val a1 = TheoryAxiom( hof"!y (y*0 = 0)" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type " ); println( m1.ty )
}

// Should give an exception.
object theoryAxiom3 extends Script {
  val a1 = TheoryAxiom( hof"!y (y*0 = y)" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type " ); println( m1.ty )
}

object equalityIntro1 extends Script {
  val a1 = EqualityIntroRule( fot"s(s(s(0)))" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type " ); println( m1.ty )
}

object equalityIntro2 extends Script {
  val a1 = EqualityIntroRule( fot"s(s(s(x + (y * z))))" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type " ); println( m1.ty )
}

object weakeningRule1 extends Script {
  val a1 = EqualityIntroRule( hof"s(s(y))" )
  val a2 = WeakeningRule( a1, hof"!x( x = x + (0 * s(z)))" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type " ); println( m1.ty )
  val m2 = MRealizability.mrealize( a2 )
  print( m2 ); print( " of type " ); println( m2.ty )
}

object weakeningRule2 extends Script {
  val a1 = LogicalAxiom( hof"s(x) = s(s(y))" )
  val a2 = WeakeningRule( a1, hof"!x( x = x + (0 * s(z)))" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type " ); println( m1.ty )
  val m2 = MRealizability.mrealize( a2 )
  print( m2 ); print( " of type " ); println( m2.ty )
}

object weakeningRule3 extends Script {
  val a1 = LogicalAxiom( hof"x = y" )
  val a2 = WeakeningRule( a1, hof"!x( x = z)" )
  val a3 = WeakeningRule( a2, hof"?x (x = y)" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type " ); println( m1.ty )
  val m2 = MRealizability.mrealize( a2 )
  print( m2 ); print( " of type " ); println( m2.ty )
  val m3 = MRealizability.mrealize( a3 )
  print( m3 ); print( " of type " ); println( m3.ty )
}

object contractionRule1 extends Script {
  val a1 = LogicalAxiom( hof"x = 0" )
  val a2 = WeakeningRule( a1, hof"x = z" )
  val a3 = WeakeningRule( a2, hof"x = y" )
  val a4 = WeakeningRule( a3, hof"x = y" )
  val a5 = ContractionRule( a4, hof"x=y" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type " ); println( m1.ty )
  val m2 = MRealizability.mrealize( a2 )
  print( m2 ); print( " of type " ); println( m2.ty )
  val m3 = MRealizability.mrealize( a3 )
  print( m3 ); print( " of type " ); println( m3.ty )
  val m4 = MRealizability.mrealize( a4 )
  print( m4 ); print( " of type " ); println( m4.ty )
  val m5 = MRealizability.mrealize( a5 )
  print( m5 ); print( " of type " ); println( m5.ty )
}

object andElim1Rule1 extends Script {
}

object andElim2Rule1 extends Script {
}

object andIntroRule1 extends Script {
}

object impElimRule1 extends Script {
}

object impIntroRule extends Script {
}

object bottomElimRule extends Script {
}

// Should give an exception.
object excludedMiddle extends Script {
}