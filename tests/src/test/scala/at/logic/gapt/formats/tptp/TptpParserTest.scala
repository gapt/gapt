package at.logic.gapt.formats.tptp

import org.specs2.mutable.Specification

class TptpParserTest extends Specification {

  def loadTPTP( fileName: String ) =
    resolveIncludes(
      TptpFile( Seq( IncludeDirective( fileName, None ) ) ),
      fileName => TptpParser.parseString( io.Source.fromInputStream(
        getClass.getClassLoader.getResourceAsStream( fileName )
      ).mkString, fileName )
    )

  "gra014p1" in {
    loadTPTP( "GRA014+1.p" )
    ok
  }

}
