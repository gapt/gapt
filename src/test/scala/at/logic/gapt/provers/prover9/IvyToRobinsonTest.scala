package at.logic.gapt.formats.ivy

import org.specs2.matcher.MatchResult
import org.specs2.specification.core.Fragments

import at.logic.gapt.utils.testing.ClasspathFileCopier
import conversion.IvyToRobinson
import org.specs2.mutable._
import at.logic.gapt.formats.lisp
import lisp.{ SExpressionParser }

/**
 * Test for the Ivy interface.
 */
class IvyToRobinsonTest extends Specification with ClasspathFileCopier {

  def parse( file: String ): MatchResult[Any] = {
    val result = SExpressionParser( tempCopyOfClasspathFile( file ) )
    result must not beEmpty
    val proof = result.head
    proof match {
      case lisp.List( _ ) =>
        val pinput = IvyParser.parse( proof, IvyParser.is_ivy_variable )
        val rinput = IvyToRobinson( pinput )
        ok
      case _ =>
        ko( s"The proof in $file must have some inferences" )
    }
  }

  "The Ivy Parser" should {
    val filesToTest = Seq( "factor.ivy", "factor2.ivy", "manyliterals.ivy", "simple2.ivy", "prime1-0sk.ivy", "GRA014+1.ivy", "GEO037-2.ivy", "issue221.ivy" )
    Fragments.foreach( filesToTest )( file => ( s"parse the test file $file" ! parse( file ) ) ^ br )
  }

}

