package gapt.expr.formula.constants

import gapt.expr.ty.To

object AndC extends MonomorphicLogicalC("∧", To ->: To ->: To)
