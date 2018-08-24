package gapt.formats.tptp

import gapt.formats.ClasspathInputFile
import org.specs2.mutable.Specification

class TptpParserTest extends Specification {

  def loadTPTP( fileName: String ) =
    resolveIncludes(
      TptpFile( Seq( IncludeDirective( fileName, None ) ) ),
      fileName => TptpParser.parse( ClasspathInputFile( fileName ) ) )

  "gra014p1" in {
    loadTPTP( "GRA014+1.p" )
    ok
  }

  "tautological clauses" in {
    tptpProblemToResolution( loadTPTP( "HWV116-1_excerpt.p" ) )
    ok
  }

}
