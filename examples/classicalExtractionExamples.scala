package gapt.examples

import com.sun.org.apache.bcel.internal.generic.AllocationInstruction
import extraction.CodeGenerator
import gapt.proofs.nd._
import gapt.expr.{ TBase, _ }
import gapt.proofs.{ Ant, Checkable, Context, Sequent, Suc }
import gapt.proofs.Context.{ InductiveType, PrimRecFun }
import gapt.proofs.lk._
import org.sat4j.pb.tools.DisjunctionRHS

object example1 extends Script {

  var ctx = Context()

  implicit var systemT = ClassicalExtraction.systemT( ctx )
  println( systemT )

}

/*
object classicalExtractionTest {
  def apply( proof: NDProof )( implicit ctx: Context ): Unit = {
    val m1 = ClassicalExtraction.mrealize( proof, false )
    //val m1n = ClassicalExtraction.mrealize( proof )
    print( proof ); print( m1 ); print( " of type " ); println( m1._2.ty ); //print( "normalized: " ); print( m1n )
    println(); println()
  }
}
*/

object classicalExtractionTest {
  def apply( proof: NDProof )( implicit ctx: Context ): Unit = {
    val m1 = ClassicalExtraction.extractCases( proof )
    //val m1n = ClassicalExtraction.mrealize( proof )
    //print( proof ); print( m1 ); print( " of type " ); print( m1.ty ); println()
    println( "free vars: " + freeVariables( m1 ) )
    println(); println()
    println( CodeGenerator.apply( m1, ClassicalExtraction.systemT( ctx ) ) )
  }
}

object example2 extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = EqualityIntroRule( le"0" )
  val a2 = OrIntro1Rule( a1, hof"s(0) = 0" )
  classicalExtractionTest( a2 )

  val a3 = OrIntro2Rule( a1, hof"s(0) = 0" )
  classicalExtractionTest( a3 )
}

object example3 extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val b1 = gapt.proofs.nd.LogicalAxiom( hof"x = 0" )
  val b2 = OrIntro2Rule( b1, hof"x = 0" )
  val b6 = OrElimRule( b2, b1, b1 )
  classicalExtractionTest( b6 )
}

object example4 extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val b1 = gapt.proofs.nd.LogicalAxiom( hof"-(x = 0)" )
  val b2 = gapt.proofs.nd.LogicalAxiom( hof"x = 0" )
  val b3 = NegElimRule( b1, b2 )
  val b6 = BottomElimRule( b3, hof"x = 0" )
  classicalExtractionTest( b6 )
}

object example5 extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val b1 = gapt.proofs.nd.LogicalAxiom( hof"-(x = 0)" )
  val b2 = gapt.proofs.nd.LogicalAxiom( hof"x = 0" )
  val b3 = NegElimRule( b1, b2 )
  val b4 = NegIntroRule( b3, Ant( 1 ) )
  val b5 = NegElimRule( b4, b2 )
  val b6 = BottomElimRule( b5, hof"x = 0" )
  classicalExtractionTest( b3 )
  classicalExtractionTest( b4 )
  classicalExtractionTest( b5 )
  classicalExtractionTest( b6 )
}

object example6 extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = gapt.proofs.nd.LogicalAxiom( hof"-(x = 0)" )
  val a2 = gapt.proofs.nd.LogicalAxiom( hof"x = 0" )
  val a3 = NegElimRule( a1, a2 )
  val a4 = BottomElimRule( a3, hof"x = 0" )
  val a5 = ExcludedMiddleRule( a2, Ant( 0 ), a4, Ant( 0 ) )
  classicalExtractionTest( a5 )
}

object example7 extends Script {

  implicit var ctx = Context()
  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = gapt.proofs.nd.LogicalAxiom( hof"-(x = 0)" )
  val a2 = gapt.proofs.nd.LogicalAxiom( hof"x = 0" )
  val a3 = NegElimRule( a1, a2 )
  val a4 = BottomElimRule( a3, hof"-(x = 0)" )
  val a5 = ExcludedMiddleRule( a4, Ant( 1 ), a1, Ant( 0 ) )
  classicalExtractionTest( a5 )
}

object example8 extends Script {

  implicit var ctx = Context()
  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += hoc"P: nat > o"

  val l = gapt.proofs.nd.ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"!x P x" ) ).
    u( ForallElimRule( _, le"n: nat" ) ).
    u( ExistsIntroRule( _, hof"?x P x" ) ).
    u( OrIntro1Rule( _, hof"?x -(P x)" ) ).
    qed
  classicalExtractionTest( l )

  val r = gapt.proofs.nd.ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"?x -(P x)" ) ).
    u( OrIntro2Rule( _, hof"?x P x" ) ).
    qed
  classicalExtractionTest( r )
}

object example9 extends Script {

  implicit var ctx = Context()
  ctx += InductiveType(
    ty"i",
    hoc"0 : i",
    hoc"s : i > i" )
  ctx += hoc"P: i > o"

  val p = gapt.proofs.nd.ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"?x P x" ) ).
    u( OrIntro1Rule( _, hof"-(?x P x)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"-(?x P x)" ) ).
    u( OrIntro2Rule( _, hof"?x P x" ) ).
    b( ExcludedMiddleRule( _, Ant( 0 ), _, Ant( 0 ) ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"?x P x" ) ).
    u( OrIntro1Rule( _, hof"-(?x P x)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"-(?x P x)" ) ).
    u( OrIntro2Rule( _, hof"?x P x" ) ).
    t( OrElimRule( _, _, _ ) ).
    qed
  println( p )
  classicalExtractionTest( p )
}

object example10 extends Script {
  implicit var ctx = Context()
  ctx += TBase( "i" )
  ctx += hoc"P: i > o"

  val p = gapt.proofs.nd.ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"!x P x" ) ).
    u( ForallElimRule( _, hov"v: i" ) ).
    u( ForallIntroRule( _, hof"!y P y", hov"v: i" ) ).
    qed
  classicalExtractionTest( p )
}

object example11 extends Script {
  implicit var ctx = Context()
  val s1 = gapt.proofs.lk.LogicalAxiom( hof"A" )
  val s2 = NegRightRule( s1, hof"A" )
  val s3 = NegLeftRule( s2, hof"-A" )
  val s4 = ImpRightRule( s3, hof"-(-A) -> A" )

  val nd = LKToND( s4 )
  println( nd )
  classicalExtractionTest( nd )
}

object example12 extends Script {

  implicit var ctx = Context()

  val p = gapt.proofs.nd.ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"A" ) ).
    u( OrIntro1Rule( _, hof"-A" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"-A" ) ).
    u( OrIntro2Rule( _, hof"A" ) ).
    b( ExcludedMiddleRule( _, Ant( 0 ), _, Ant( 0 ) ) ).
    qed
  classicalExtractionTest( p )
}

object example13 extends Script {
  implicit var ctx = Context()
  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

}

/*
object extracted extends Script {
  def app[A, B]( f: A => B )( arg: A ): B = f( arg )
  def s( x: Int ) = x + 1
  def mul( x: Int )( y: Int ) = x * y
  def leq( x: Int )( y: Int ) = x <= y

  def pow2( x: Int ) = x * x
  def pi2[A, B]( p: ( A, B ) ) = p._2
  sealed trait Sum[A, B]
  final case class Inr[A, B]( v: B ) extends Sum[A, B]
  def inr[A, B]( v: B ): Sum[A, B] = new Inr( v )

  def matchSum[A, B, C]( p1: Sum[A, B] )( p2: A => C )( p3: B => C ) = {
    p1 match {
      case Inl( a ) => p2( a )
      case Inr( b ) => p3( b )
    }
  }

  def eq[X]( x: X )( y: X ) = x == y
  def lt( x: Int )( y: Int ) = x < y
  final case class Inl[A, B]( v: A ) extends Sum[A, B]
  def inl[A, B]( v: A ): Sum[A, B] = new Inl( v )
  def f( x: Int )( y: Int ) = x < ( y + 1 ) * ( y + 1 ) && y * y <= x

  def natRec[A]( p1: A )( p2: ( Int => A => A ) )( p3: Int ): A = {
    if ( p3 == 0 ) {
      p1
    } else {
      p2( p3 - 1 )( natRec( p1 )( p2 )( p3 - 1 ) )
    }
  }
  class NewException[A]( m: A ) extends Exception
  def exception[A]( p: A ) = { new NewException( p ) }

  def bar2[X, A, B]( p1: X => Boolean )( p2: A => Int )( p3: B => Int ): Int = {
    ???
  }

  def pi1[A, B]( p: ( A, B ) ) = p._1
  def bar[A, B, C]( p1: Boolean )( p2: A => C )( p3: B => C ): C = { ??? }

  def pair[A, B]( p0: A )( p1: B ) = ( p0, p1 )
  def efq( p: Throwable ) = { throw p }
  /*

val prog: Int => Int = {
  v_2: Int =>
    app( {
      v_0: ( Int => Int ) =>
        app( {
          v: Int => v
        } )( app( v_0 )( v_2 ) )
    } )( {
      x: Int =>
        app( app( app( natRec )( 0 ) )( {
          v_0: Int =>
            {
              v_10: Int =>
                app( app( app( bar2 )( {
                  y: Int => app( app( f )( app( s )( v_0 ) ) )( y )
                } ) )( {
                  v_11: Int => v_11
                } ) )( {
                  v_13: ( Int => Exception ) => v_10
                } )
            }
        } ) )( x )
    } )
}
*/

  val prog: Int => Int = {
    x: Int =>
      println( s"x: $x" )
      app( app( app( natRec[Int] )( 0 ) )( {
        v_0: Int =>
          {
            v_10: Int =>
              val f2: Int =
                app( app( app( bar2 )( {
                  y: Int => app( app( f )( app( s )( v_0 ) ) )( y )
                } ) )( {
                  v_11: Int => v_11
                } ) )( {
                  v_13: ( Int => Exception ) => v_10
                } )
              f2
          }
      } ) )( x )
  }
  println( s"res: ${prog( 0 )}" )
  println( s"res: ${prog( s( s( s( s( 0 ) ) ) ) )}" )
}
*/

object extracted extends Script {
  def s( x: Int ) = x + 1
  def mul( x: Int )( y: Int ) = x * y
  def leq( x: Int )( y: Int ) = x <= y

  def pow2( x: Int ) = x * x
  def pi2[A, B]( p: ( A, B ) ) = p._2
  sealed trait Sum[A, B]
  final case class Inr[A, B]( v: B ) extends Sum[A, B]
  def inr[A, B]( v: B ): Sum[A, B] = new Inr( v )

  def matchSum[A, B, C]( p1: Sum[A, B] )( p2: A => C )( p3: B => C ) = {
    p1 match {
      case Inl( a ) => p2( a )
      case Inr( b ) => p3( b )
    }
  }

  def eq[X]( x: X )( y: X ) = x == y
  def lt( x: Int )( y: Int ) = x < y
  final case class Inl[A, B]( v: A ) extends Sum[A, B]
  def inl[A, B]( v: A ): Sum[A, B] = new Inl( v )
  def f( x: Int )( y: Int ) = x < ( y + 1 ) * ( y + 1 ) && y * y <= x

  def natRec[A]( p1: A )( p2: ( Int => A => A ) )( p3: Int ): A = {
    if ( p3 == 0 ) {
      p1
    } else {
      p2( p3 - 1 )( natRec( p1 )( p2 )( p3 - 1 ) )
    }
  }
  class NewException[A]( m: A ) extends Exception
  def exception[A]( p: A ) = { new NewException( p ) }

  def subst[A, B]( x: A )( y: B ): Unit = ()
  def bar2[X, A, B, C]( p1: X => Boolean )( p2: A => C )( p3: B => C ): C = { ??? }

  def pi1[A, B]( p: ( A, B ) ) = p._1
  def bar[A, B, C]( p2: A => C )( p3: B => C ): C = { ??? }

  def pair[A, B]( p0: A )( p1: B ) = ( p0, p1 )
  def efq( p: Throwable ) = { throw p }

  val prog: ( Int => Unit ) => ( Int => Unit ) => ( Int => Unit ) => ( Int => Int => Unit => Unit ) => ( Int => Int => Sum[Sum[Unit, Unit], Unit] ) => ( Int => Int => Int => ( Unit, Unit ) => Unit ) => ( Int => Int => ( ( Unit, Unit ), Unit ) => ( Unit, Unit ) ) => ( Int => Int => ( Unit => ( Unit, Unit ), ( Unit, Unit ) => Unit ) ) => ( Int => Int => ( Unit => Sum[Unit, Unit], Sum[Unit, Unit] => Unit ) ) => ( Int => Unit ) => Int => ( Int, Unit ) =
    {
      v_86: ( Int => Unit ) =>
        {
          v_84: ( Int => Unit ) =>
            {
              v_78: ( Int => Unit ) =>
                {
                  v_77: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                    {
                      v_75: ( Int => ( Int => Sum[Sum[Unit, Unit], Unit] ) ) =>
                        {
                          v_73: ( Int => ( Int => ( Int => ( ( Unit, Unit ) => Unit ) ) ) ) =>
                            {
                              v_63: ( Int => ( Int => ( ( ( Unit, Unit ), Unit ) => ( Unit, Unit ) ) ) ) =>
                                {
                                  v_66: ( Int => ( Int => ( ( Unit => ( Unit, Unit ) ), ( ( Unit, Unit ) => Unit ) ) ) ) =>
                                    {
                                      v_69: ( Int => ( Int => ( ( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit ) ) ) ) =>
                                        {
                                          v_70: ( Int => Unit ) =>
                                            {
                                              v_2: Int =>
                                                ( {
                                                  v_5: Unit =>
                                                    ( {
                                                      v_7: Unit =>
                                                        ( {
                                                          v_85: ( Int => ( ( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit ) ) ) =>
                                                            ( {
                                                              v_82: ( ( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit ) ) =>
                                                                ( {
                                                                  v_6: Unit =>
                                                                    ( {
                                                                      v_83: ( Int => ( ( Unit => ( Unit, Unit ) ), ( ( Unit, Unit ) => Unit ) ) ) =>
                                                                        ( {
                                                                          v_80: ( ( Unit => ( Unit, Unit ) ), ( ( Unit, Unit ) => Unit ) ) =>
                                                                            ( {
                                                                              v_9: ( Sum[Unit, Unit] => Unit ) =>
                                                                                ( {
                                                                                  v_81: ( Unit => Sum[Unit, Unit] ) =>
                                                                                    ( {
                                                                                      v_2: ( ( Unit, Unit ) => Unit ) =>
                                                                                        ( {
                                                                                          v_79: ( Unit => ( Unit, Unit ) ) =>
                                                                                            ( {
                                                                                              v_0: ( Int => ( Int, Unit ) ) =>
                                                                                                ( {
                                                                                                  v: ( Int, Unit ) => v
                                                                                                } )( ( v_0 )( v_2 ) )
                                                                                            } )( {
                                                                                              x: Int =>
                                                                                                ( ( ( natRec[( Int, Unit )] )( ( ( pair[Int, Unit] )( 0 ) )( ( {
                                                                                                  v_1: Unit => v_1
                                                                                                } )( ( v_2 )( ( ( pair[Unit, Unit] )( ( {
                                                                                                  v_4: Unit =>
                                                                                                    ( {
                                                                                                      v_3: Unit => v_3
                                                                                                    } )( ( ( subst )( v_4 ) )( v_5 ) )
                                                                                                } )( ( ( subst )( v_6 ) )( v_7 ) ) ) )( ( {
                                                                                                  v_8: Unit =>
                                                                                                    ( {
                                                                                                      v_4: Unit => ( ( subst )( v_4 ) )( v_8 )
                                                                                                    } )( ( ( subst )( v_6 ) )( v_7 ) )
                                                                                                } )( ( v_9 )( ( inl[Unit, Unit] )() ) ) ) ) ) ) ) )( {
                                                                                                  v_0: Int =>
                                                                                                    {
                                                                                                      v_10: ( Int, Unit ) =>
                                                                                                        ( {
                                                                                                          v_21: Unit =>
                                                                                                            ( {
                                                                                                              v_76: ( Int => ( Unit => Unit ) ) =>
                                                                                                                ( {
                                                                                                                  v_23: ( Unit => Unit ) =>
                                                                                                                    ( {
                                                                                                                      v_74: ( Int => Sum[Sum[Unit, Unit], Unit] ) =>
                                                                                                                        ( {
                                                                                                                          v_42: Sum[Sum[Unit, Unit], Unit] =>
                                                                                                                            ( {
                                                                                                                              v_72: ( Int => ( Int => ( ( Unit, Unit ) => Unit ) ) ) =>
                                                                                                                                ( {
                                                                                                                                  v_71: ( Int => ( ( Unit, Unit ) => Unit ) ) =>
                                                                                                                                    ( {
                                                                                                                                      v_19: ( ( Unit, Unit ) => Unit ) =>
                                                                                                                                        ( {
                                                                                                                                          v_17: Unit =>
                                                                                                                                            ( {
                                                                                                                                              v_20: Unit =>
                                                                                                                                                ( {
                                                                                                                                                  v_67: ( Int => ( ( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit ) ) ) =>
                                                                                                                                                    ( {
                                                                                                                                                      v_68: ( Int => ( ( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit ) ) ) =>
                                                                                                                                                        ( {
                                                                                                                                                          v_61: ( ( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit ) ) =>
                                                                                                                                                            ( {
                                                                                                                                                              v_59: ( ( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit ) ) =>
                                                                                                                                                                ( {
                                                                                                                                                                  v_64: ( Int => ( ( Unit => ( Unit, Unit ) ), ( ( Unit, Unit ) => Unit ) ) ) =>
                                                                                                                                                                    ( {
                                                                                                                                                                      v_65: ( Int => ( ( Unit => ( Unit, Unit ) ), ( ( Unit, Unit ) => Unit ) ) ) =>
                                                                                                                                                                        ( {
                                                                                                                                                                          v_57: ( ( Unit => ( Unit, Unit ) ), ( ( Unit, Unit ) => Unit ) ) =>
                                                                                                                                                                            ( {
                                                                                                                                                                              v_55: ( ( Unit => ( Unit, Unit ) ), ( ( Unit, Unit ) => Unit ) ) =>
                                                                                                                                                                                ( {
                                                                                                                                                                                  v_53: ( ( Unit => ( Unit, Unit ) ), ( ( Unit, Unit ) => Unit ) ) =>
                                                                                                                                                                                    ( {
                                                                                                                                                                                      v_62: ( Int => ( ( ( Unit, Unit ), Unit ) => ( Unit, Unit ) ) ) =>
                                                                                                                                                                                        ( {
                                                                                                                                                                                          v_41: ( ( ( Unit, Unit ), Unit ) => ( Unit, Unit ) ) =>
                                                                                                                                                                                            ( ( ( bar2 )( {
                                                                                                                                                                                              y: Int => ( ( f )( ( s )( v_0 ) ) )( y )
                                                                                                                                                                                            } ) )( {
                                                                                                                                                                                              v_11: ( Int, Unit ) => v_11
                                                                                                                                                                                            } ) )( {
                                                                                                                                                                                              v_13: ( ( Int, Unit ) => Exception ) =>
                                                                                                                                                                                                ( ( pair[Int, Unit] )( ( pi1[Int, Unit] )( v_10 ) ) )( ( ( bar )( {
                                                                                                                                                                                                  v_12: Unit => v_12
                                                                                                                                                                                                } ) )( {
                                                                                                                                                                                                  v_30: ( Unit => Exception ) =>
                                                                                                                                                                                                    ( efq )( ( v_13 )( ( ( pair[Int, Unit] )( ( s )( ( pi1[Int, Unit] )( v_10 ) ) ) )( ( {
                                                                                                                                                                                                      v_37: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                                                        ( {
                                                                                                                                                                                                          v_60: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                                                                                                                            ( {
                                                                                                                                                                                                              v_50: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                  v_58: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                      v_56: ( ( Unit, Unit ) => Unit ) =>
                                                                                                                                                                                                                        ( {
                                                                                                                                                                                                                          v_27: ( Unit => ( Unit, Unit ) ) =>
                                                                                                                                                                                                                            ( {
                                                                                                                                                                                                                              v_31: ( ( Unit, Unit ) => Unit ) =>
                                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                                  v_54: ( Unit => ( Unit, Unit ) ) =>
                                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                                      v_15: ( ( Unit, Unit ) => Unit ) =>
                                                                                                                                                                                                                                        ( {
                                                                                                                                                                                                                                          v_52: ( Unit => ( Unit, Unit ) ) =>
                                                                                                                                                                                                                                            ( {
                                                                                                                                                                                                                                              v_14: Unit => v_14
                                                                                                                                                                                                                                            } )( ( v_15 )( ( ( pair[Unit, Unit] )( ( {
                                                                                                                                                                                                                                              v_26: ( Unit, Unit ) =>
                                                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                                                  v_25: Unit =>
                                                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                                                      v_24: Unit =>
                                                                                                                                                                                                                                                        ( {
                                                                                                                                                                                                                                                          v_18: Unit =>
                                                                                                                                                                                                                                                            ( {
                                                                                                                                                                                                                                                              v_16: Unit => v_16
                                                                                                                                                                                                                                                            } )( ( ( subst )( v_17 ) )( v_18 ) )
                                                                                                                                                                                                                                                        } )( ( v_19 )( ( ( pair[Unit, Unit] )( ( ( subst )( v_20 ) )( ( ( subst )( v_17 ) )( v_21 ) ) ) )( ( {
                                                                                                                                                                                                                                                          v_22: Unit => v_22
                                                                                                                                                                                                                                                        } )( ( v_23 )( ( ( subst )( v_20 ) )( v_24 ) ) ) ) ) )
                                                                                                                                                                                                                                                    } )( ( pi1[Unit, Unit] )( v_26 ) )
                                                                                                                                                                                                                                                } )( ( pi2[Unit, Unit] )( v_26 ) )
                                                                                                                                                                                                                                            } )( ( v_27 )( ( pi2[Int, Unit] )( v_10 ) ) ) ) )( ( ( bar )( {
                                                                                                                                                                                                                                              v_29: Unit => v_29
                                                                                                                                                                                                                                            } ) )( {
                                                                                                                                                                                                                                              v_33: ( Unit => Exception ) =>
                                                                                                                                                                                                                                                ( efq )( ( v_30 )( ( {
                                                                                                                                                                                                                                                  v_12: Unit => v_12
                                                                                                                                                                                                                                                } )( ( v_31 )( ( ( bar )( {
                                                                                                                                                                                                                                                  v_32: ( Unit, Unit ) => v_32
                                                                                                                                                                                                                                                } ) )( {
                                                                                                                                                                                                                                                  v_34: ( ( Unit, Unit ) => Exception ) =>
                                                                                                                                                                                                                                                    ( efq )( ( v_33 )( ( ( bar )( {
                                                                                                                                                                                                                                                      v_29: Unit => v_29
                                                                                                                                                                                                                                                    } ) )( {
                                                                                                                                                                                                                                                      v_33: ( Unit => Exception ) =>
                                                                                                                                                                                                                                                        ( ( bar )( {
                                                                                                                                                                                                                                                          v_29: Unit => v_29
                                                                                                                                                                                                                                                        } ) )( {
                                                                                                                                                                                                                                                          v_33: ( Unit => Exception ) =>
                                                                                                                                                                                                                                                            ( efq )( ( v_34 )( ( ( pair[Unit, Unit] )( ( {
                                                                                                                                                                                                                                                              v_26: ( Unit, Unit ) =>
                                                                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                                                                  v_25: Unit =>
                                                                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                                                                      v_24: Unit =>
                                                                                                                                                                                                                                                                        ( {
                                                                                                                                                                                                                                                                          v_48: Unit =>
                                                                                                                                                                                                                                                                            ( ( bar )( {
                                                                                                                                                                                                                                                                              v_35: Unit => v_35
                                                                                                                                                                                                                                                                            } ) )( {
                                                                                                                                                                                                                                                                              v_39: ( Unit => Exception ) =>
                                                                                                                                                                                                                                                                                ( efq )( ( v_33 )( ( ( bar )( {
                                                                                                                                                                                                                                                                                  v_29: Unit => v_29
                                                                                                                                                                                                                                                                                } ) )( {
                                                                                                                                                                                                                                                                                  v_33: ( Unit => Exception ) =>
                                                                                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                                                                                      v_36: Unit =>
                                                                                                                                                                                                                                                                                        ( {
                                                                                                                                                                                                                                                                                          v_29: Unit => v_29
                                                                                                                                                                                                                                                                                        } )( ( ( subst )( v_20 ) )( v_36 ) )
                                                                                                                                                                                                                                                                                    } )( ( v_37 )( ( inr[Unit, Unit] )( ( ( bar )( {
                                                                                                                                                                                                                                                                                      v_38: Unit => v_38
                                                                                                                                                                                                                                                                                    } ) )( {
                                                                                                                                                                                                                                                                                      v_44: ( Unit => Exception ) =>
                                                                                                                                                                                                                                                                                        ( efq )( ( v_39 )( ( {
                                                                                                                                                                                                                                                                                          v_32: ( Unit, Unit ) =>
                                                                                                                                                                                                                                                                                            ( {
                                                                                                                                                                                                                                                                                              v_40: Unit =>
                                                                                                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                                                                                                  v_35: Unit => v_35
                                                                                                                                                                                                                                                                                                } )( ( pi1[Unit, Unit] )( v_32 ) )
                                                                                                                                                                                                                                                                                            } )( ( pi2[Unit, Unit] )( v_32 ) )
                                                                                                                                                                                                                                                                                        } )( ( v_41 )( ( ( pair[( Unit, Unit ), Unit] )( ( ( pair[Unit, Unit] )( ( ( ( matchSum )( v_42 ) )( {
                                                                                                                                                                                                                                                                                          v_43: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                                                                            ( ( ( matchSum )( v_43 ) )( {
                                                                                                                                                                                                                                                                                              v_38: Unit => ( efq )( ( v_44 )( v_38 ) )
                                                                                                                                                                                                                                                                                            } ) )( {
                                                                                                                                                                                                                                                                                              v_45: Unit =>
                                                                                                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                                                                                                  v_35: Unit => v_35
                                                                                                                                                                                                                                                                                                } )( ( ( subst )( v_20 ) )( v_45 ) )
                                                                                                                                                                                                                                                                                            } )
                                                                                                                                                                                                                                                                                        } ) )( {
                                                                                                                                                                                                                                                                                          v_49: Unit =>
                                                                                                                                                                                                                                                                                            ( efq )( ( v_33 )( ( {
                                                                                                                                                                                                                                                                                              v_46: Unit =>
                                                                                                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                                                                                                  v_47: Unit => ( ( subst )( v_46 ) )( v_47 )
                                                                                                                                                                                                                                                                                                } )( ( ( subst )( v_46 ) )( v_48 ) )
                                                                                                                                                                                                                                                                                            } )( ( ( subst )( v_49 ) )( v_20 ) ) ) )
                                                                                                                                                                                                                                                                                        } ) ) )( v_24 ) ) )( v_25 ) ) ) ) )
                                                                                                                                                                                                                                                                                    } ) ) ) )
                                                                                                                                                                                                                                                                                } ) ) )
                                                                                                                                                                                                                                                                            } )
                                                                                                                                                                                                                                                                        } )( ( v_50 )( ( inl[Unit, Unit] )() ) )
                                                                                                                                                                                                                                                                    } )( ( pi1[Unit, Unit] )( v_26 ) )
                                                                                                                                                                                                                                                                } )( ( pi2[Unit, Unit] )( v_26 ) )
                                                                                                                                                                                                                                                            } )( ( v_27 )( ( pi2[Int, Unit] )( v_10 ) ) ) ) )( ( {
                                                                                                                                                                                                                                                              v_26: ( Unit, Unit ) =>
                                                                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                                                                  v_25: Unit =>
                                                                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                                                                      v_24: Unit =>
                                                                                                                                                                                                                                                                        ( {
                                                                                                                                                                                                                                                                          v_48: Unit =>
                                                                                                                                                                                                                                                                            ( ( bar )( {
                                                                                                                                                                                                                                                                              v_40: Unit => v_40
                                                                                                                                                                                                                                                                            } ) )( {
                                                                                                                                                                                                                                                                              v_51: ( Unit => Exception ) =>
                                                                                                                                                                                                                                                                                ( efq )( ( v_33 )( ( ( bar )( {
                                                                                                                                                                                                                                                                                  v_29: Unit => v_29
                                                                                                                                                                                                                                                                                } ) )( {
                                                                                                                                                                                                                                                                                  v_33: ( Unit => Exception ) =>
                                                                                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                                                                                      v_36: Unit =>
                                                                                                                                                                                                                                                                                        ( {
                                                                                                                                                                                                                                                                                          v_29: Unit => v_29
                                                                                                                                                                                                                                                                                        } )( ( ( subst )( v_20 ) )( v_36 ) )
                                                                                                                                                                                                                                                                                    } )( ( v_37 )( ( inr[Unit, Unit] )( ( ( bar )( {
                                                                                                                                                                                                                                                                                      v_38: Unit => v_38
                                                                                                                                                                                                                                                                                    } ) )( {
                                                                                                                                                                                                                                                                                      v_44: ( Unit => Exception ) =>
                                                                                                                                                                                                                                                                                        ( efq )( ( v_51 )( ( {
                                                                                                                                                                                                                                                                                          v_32: ( Unit, Unit ) =>
                                                                                                                                                                                                                                                                                            ( {
                                                                                                                                                                                                                                                                                              v_40: Unit =>
                                                                                                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                                                                                                  v_35: Unit => v_40
                                                                                                                                                                                                                                                                                                } )( ( pi1[Unit, Unit] )( v_32 ) )
                                                                                                                                                                                                                                                                                            } )( ( pi2[Unit, Unit] )( v_32 ) )
                                                                                                                                                                                                                                                                                        } )( ( v_41 )( ( ( pair[( Unit, Unit ), Unit] )( ( ( pair[Unit, Unit] )( ( ( ( matchSum )( v_42 ) )( {
                                                                                                                                                                                                                                                                                          v_43: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                                                                            ( ( ( matchSum )( v_43 ) )( {
                                                                                                                                                                                                                                                                                              v_38: Unit => ( efq )( ( v_44 )( v_38 ) )
                                                                                                                                                                                                                                                                                            } ) )( {
                                                                                                                                                                                                                                                                                              v_45: Unit =>
                                                                                                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                                                                                                  v_35: Unit => v_35
                                                                                                                                                                                                                                                                                                } )( ( ( subst )( v_20 ) )( v_45 ) )
                                                                                                                                                                                                                                                                                            } )
                                                                                                                                                                                                                                                                                        } ) )( {
                                                                                                                                                                                                                                                                                          v_49: Unit =>
                                                                                                                                                                                                                                                                                            ( efq )( ( v_33 )( ( {
                                                                                                                                                                                                                                                                                              v_46: Unit =>
                                                                                                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                                                                                                  v_47: Unit => ( ( subst )( v_46 ) )( v_47 )
                                                                                                                                                                                                                                                                                                } )( ( ( subst )( v_46 ) )( v_48 ) )
                                                                                                                                                                                                                                                                                            } )( ( ( subst )( v_49 ) )( v_20 ) ) ) )
                                                                                                                                                                                                                                                                                        } ) ) )( v_24 ) ) )( v_25 ) ) ) ) )
                                                                                                                                                                                                                                                                                    } ) ) ) )
                                                                                                                                                                                                                                                                                } ) ) )
                                                                                                                                                                                                                                                                            } )
                                                                                                                                                                                                                                                                        } )( ( v_50 )( ( inl[Unit, Unit] )() ) )
                                                                                                                                                                                                                                                                    } )( ( pi1[Unit, Unit] )( v_26 ) )
                                                                                                                                                                                                                                                                } )( ( pi2[Unit, Unit] )( v_26 ) )
                                                                                                                                                                                                                                                            } )( ( v_27 )( ( pi2[Int, Unit] )( v_10 ) ) ) ) ) )
                                                                                                                                                                                                                                                        } )
                                                                                                                                                                                                                                                    } ) ) )
                                                                                                                                                                                                                                                } ) ) ) ) )
                                                                                                                                                                                                                                            } ) ) ) )
                                                                                                                                                                                                                                        } )( ( pi1[( Unit => ( Unit, Unit ) ), ( ( Unit, Unit ) => Unit )] )( v_53 ) )
                                                                                                                                                                                                                                    } )( ( pi2[( Unit => ( Unit, Unit ) ), ( ( Unit, Unit ) => Unit )] )( v_53 ) )
                                                                                                                                                                                                                                } )( ( pi1[( Unit => ( Unit, Unit ) ), ( ( Unit, Unit ) => Unit )] )( v_55 ) )
                                                                                                                                                                                                                            } )( ( pi2[( Unit => ( Unit, Unit ) ), ( ( Unit, Unit ) => Unit )] )( v_55 ) )
                                                                                                                                                                                                                        } )( ( pi1[( Unit => ( Unit, Unit ) ), ( ( Unit, Unit ) => Unit )] )( v_57 ) )
                                                                                                                                                                                                                    } )( ( pi2[( Unit => ( Unit, Unit ) ), ( ( Unit, Unit ) => Unit )] )( v_57 ) )
                                                                                                                                                                                                                } )( ( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] )( v_59 ) )
                                                                                                                                                                                                            } )( ( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] )( v_59 ) )
                                                                                                                                                                                                        } )( ( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] )( v_61 ) )
                                                                                                                                                                                                    } )( ( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] )( v_61 ) ) ) ) )
                                                                                                                                                                                                } ) )
                                                                                                                                                                                            } )
                                                                                                                                                                                        } )( ( v_62 )( v_0 ) )
                                                                                                                                                                                    } )( ( v_63 )( ( pi1[Int, Unit] )( v_10 ) ) )
                                                                                                                                                                                } )( ( v_64 )( ( s )( ( pi1[Int, Unit] )( v_10 ) ) ) )
                                                                                                                                                                            } )( ( v_64 )( ( pi1[Int, Unit] )( v_10 ) ) )
                                                                                                                                                                        } )( ( v_65 )( ( pi1[Int, Unit] )( v_10 ) ) )
                                                                                                                                                                    } )( ( v_66 )( v_0 ) )
                                                                                                                                                                } )( ( v_66 )( ( s )( v_0 ) ) )
                                                                                                                                                            } )( ( v_67 )( ( s )( v_0 ) ) )
                                                                                                                                                        } )( ( v_68 )( ( s )( v_0 ) ) )
                                                                                                                                                    } )( ( v_69 )( ( ( mul )( ( s )( ( pi1[Int, Unit] )( v_10 ) ) ) )( ( s )( ( pi1[Int, Unit] )( v_10 ) ) ) ) )
                                                                                                                                                } )( ( v_69 )( ( s )( v_0 ) ) )
                                                                                                                                            } )( ( v_70 )( ( s )( ( pi1[Int, Unit] )( v_10 ) ) ) )
                                                                                                                                        } )( ( v_70 )( ( s )( ( s )( ( pi1[Int, Unit] )( v_10 ) ) ) ) )
                                                                                                                                    } )( ( v_71 )( ( ( mul )( ( s )( ( s )( ( pi1[Int, Unit] )( v_10 ) ) ) ) )( ( s )( ( s )( ( pi1[Int, Unit] )( v_10 ) ) ) ) ) )
                                                                                                                                } )( ( v_72 )( ( s )( ( ( mul )( ( s )( ( pi1[Int, Unit] )( v_10 ) ) ) )( ( s )( ( pi1[Int, Unit] )( v_10 ) ) ) ) ) )
                                                                                                                            } )( ( v_73 )( ( s )( v_0 ) ) )
                                                                                                                        } )( ( v_74 )( ( ( mul )( ( s )( ( pi1[Int, Unit] )( v_10 ) ) ) )( ( s )( ( pi1[Int, Unit] )( v_10 ) ) ) ) )
                                                                                                                    } )( ( v_75 )( ( s )( v_0 ) ) )
                                                                                                                } )( ( v_76 )( ( ( mul )( ( s )( ( pi1[Int, Unit] )( v_10 ) ) ) )( ( s )( ( pi1[Int, Unit] )( v_10 ) ) ) ) )
                                                                                                            } )( ( v_77 )( v_0 ) )
                                                                                                        } )( ( v_78 )( ( pi1[Int, Unit] )( v_10 ) ) )
                                                                                                    }
                                                                                                } ) )( x )
                                                                                            } )
                                                                                        } )( ( pi1[( Unit => ( Unit, Unit ) ), ( ( Unit, Unit ) => Unit )] )( v_80 ) )
                                                                                    } )( ( pi2[( Unit => ( Unit, Unit ) ), ( ( Unit, Unit ) => Unit )] )( v_80 ) )
                                                                                } )( ( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] )( v_82 ) )
                                                                            } )( ( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] )( v_82 ) )
                                                                        } )( ( v_83 )( 0 ) )
                                                                    } )( ( v_66 )( 0 ) )
                                                                } )( ( v_84 )( 0 ) )
                                                            } )( ( v_85 )( 0 ) )
                                                        } )( ( v_69 )( 0 ) )
                                                    } )( ( v_70 )( 0 ) )
                                                } )( ( v_86 )( 0 ) )
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
  //(Int => Unit) => Int => (Int, Unit) =

  val arg1 = { x: Int => () }
  val arg2 = { x: Int => () }
  val arg3 = { x: Int => () }
  val arg4 = { x: Int => { y: Int => { z: Unit => () } } }
  val arg5 = { x: Int => { y: Int => inr[Sum[Unit, Unit], Unit]( () ) } }
  val arg6 = { x: Int => { y: Int => { z: Int => { foo: ( Unit, Unit ) => () } } } }
  val arg7 = { x: Int => { y: Int => { z: Int => { foo: ( ( Unit, Unit ), Unit ) => ( (), () ) } } } }
  val arg8 = { x: Int => { y: Int => ( { z: Unit => ( (), () ) }, { foo: ( Unit, Unit ) => () } ) } }
  val arg9 = { x: Int => { y: Int => ( { z: Unit => inr[Unit, Unit]( () ) }, { foo: Sum[Unit, Unit] => () } ) } }
  val arg10 = { x: Int => () }
  val p2 = prog( arg1 )( arg2 )( arg3 )( arg4 )( arg5 ) //(arg6)
  val p3 = p2( arg6 )
  val p4 = p3( arg7 )
  val p5 = p4( arg8 )
  val p6 = p5( arg9 )
  val p7 = p6( arg10 )
  println( s"res: ${pi1( p7( 4 ) )}" )
}
