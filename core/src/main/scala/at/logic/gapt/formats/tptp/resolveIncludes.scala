package at.logic.gapt.formats.tptp

object resolveIncludes {
  def apply( tptpFile: TptpFile, resolver: String => TptpFile ): TptpFile =
    TptpFile( tptpFile.inputs flatMap {
      case IncludeDirective( fileName, formulaSelection ) =>
        apply( resolver( fileName ), resolver ).inputs
      case input => Seq( input )
    } )

}
