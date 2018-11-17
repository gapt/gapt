package gapt.formats.ivy

import gapt.formats.ClasspathInputFile
import org.specs2.matcher.MatchResult
import org.specs2.specification.core.Fragments
import conversion.IvyToResolution
import org.specs2.mutable._
import gapt.formats.lisp.{ LList, SExpressionParser }

/**
 * Test for the Ivy interface.
 */
class IvyToResolutionTest extends Specification {

  def parse( file: String ): MatchResult[Any] = {
    val result = SExpressionParser.parse( ClasspathInputFile( file ) )
    result must not beEmpty
    val proof = result.head
    proof match {
      case LList( _* ) =>
        val pinput = IvyParser.parse( proof )
        val rinput = IvyToResolution( pinput )
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

