package at.logic.gapt.proofs.ceres

import at.logic.gapt.formats.llkNew._
import at.logic.gapt.formats.tptp.{ TPTPFOLExporter, TptpProofParser }
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lk.LKProof
import org.specs2.matcher.MatchResult
import org.specs2.mutable._

import scala.collection.Set
import scala.io.Source

/**
 * Created by marty on 11/24/15.
 */
class StructTest extends Specification {
  "Struct extraction" should {
    "work for the permutation proof" in {
      val proof: LKProof = LLKProofParser.parseString( Source fromInputStream getClass.getClassLoader.getResourceAsStream( "perm.llk" ) mkString ).proof( "TheProof" )
      val struct = extractStruct( proof )
      val cs = CharacteristicClauseSet( struct )
      println( coloredStructString( struct ) )
      val typedec = "var x,y,z : i; const f : i>i>i; const a,b,c : i; "
      val strings = List(
        "f(y, f(z, x)) = f(f(y, z), x)",
        "f(f(y, z), x) = f(x, f(y, z))",
        "f(x, f(y, z)) = f(x, f(y, z))",
        "f(b, f(c, a)) = f(c, f(a, b))",
        "f(a, f(b, c)) = f(b, f(c, a))"
      )
      val List( f1, f2, f3, f4, f5 ) = strings.map( x => parseLLKFormula( typedec + x ) )
      val cs_check = Set(
        HOLSequent( Nil, f1 :: Nil ),
        HOLSequent( Nil, f2 :: Nil ),
        HOLSequent( Nil, f3 :: Nil ),
        HOLSequent( f4 :: f5 :: Nil, Nil )
      )

      def compare( c1: Set[HOLSequent], c2: Set[HOLSequent] ): Set[( HOLSequent, Boolean )] = {
        c1.map( x => {
          val r = c2.exists( y => ( x multiSetEquals y ) )
          //          println( s"Testing $x : $r" )
          ( x, r )
        } )
      }

      println( TPTPFOLExporter.tptp_problem( cs.toList ) )

      compare( cs.asInstanceOf[Set[HOLSequent]], cs_check ).toList must beLike( { case List( ( _, true ), ( _, true ), ( _, true ), ( _, true ) ) => ok( "" ) } )
      compare( cs_check, cs.asInstanceOf[Set[HOLSequent]] ).toList must beLike( { case List( ( _, true ), ( _, true ), ( _, true ), ( _, true ) ) => ok( "" ) } )
      ok( "everything done" )
    }
  }

}
