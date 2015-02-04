import scalariform.formatter.preferences._

defaultScalariformSettings

ScalariformKeys.preferences := FormattingPreferences()
.setPreference(AlignParameters, true)
.setPreference(AlignSingleLineCaseStatements, true)
.setPreference(DoubleIndentClassDeclaration, true)
.setPreference(SpaceInsideParentheses, true)
