package at.logic.gapt.formats.tptp

import at.logic.gapt.formats.ClasspathInputFile
import org.specs2.mutable.Specification

class TptpParserTest extends Specification {

  def loadTPTP( fileName: String ) =
    resolveIncludes(
      TptpFile( Seq( IncludeDirective( fileName, None ) ) ),
      fileName => TptpParser.parse( ClasspathInputFile( fileName ) )
    )

  "gra014p1" in {
    loadTPTP( "GRA014+1.p" )
    ok
  }

}
