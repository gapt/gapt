import scalariform.formatter.preferences._

addCommandAlias("format", "; scalariformFormat ; test:scalariformFormat")

defaultScalariformSettings

ScalariformKeys.preferences := FormattingPreferences()
.setPreference(AlignParameters, true)
.setPreference(AlignSingleLineCaseStatements, true)
.setPreference(DoubleIndentClassDeclaration, true)
.setPreference(SpaceInsideParentheses, true)
