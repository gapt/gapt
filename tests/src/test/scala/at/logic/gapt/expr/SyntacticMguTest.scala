package at.logic.gapt.expr

import org.specs2.mutable._

class SyntacticMguTest extends Specification {

  "not unify bound variables" in {
    val x = FOLVar( "x" )
    val y = FOLVar( "y" )
    val f = FOLFunctionConst( "f", 2 )
    val g = FOLFunctionConst( "g", 1 )

    syntacticMGU(
      Abs( x, Abs( y, f( x, y ) ) ),
      Abs( x, Abs( y, f( y, x ) ) )
    ) must beNone
    syntacticMGU(
      Abs( x, Abs( y, g( x ) ) ),
      Abs( x, Abs( y, y ) )
    ) must beNone
  }

  "handle variables that are both bound and free" in {
    val Seq( x, y, z ) = Seq( "x", "y", "z" ) map { FOLVar( _ ) }
    val f = Const( "f", Ti -> ( ( Ti -> Ti ) -> Ti ) )
    val g = FOLFunctionConst( "g", 1 )
    val c = FOLConst( "c" )

    syntacticMGU(
      f( x, Abs( y, x ) ),
      f( g( y ), Abs( z, g( c ) ) )
    ) must beSome
  }

}
