package gapt.formats.tip

import gapt.expr.ty.TBase
import gapt.formats.tip.parser.TipSmtDatatype
import gapt.proofs.context.update.InductiveType

package object compiler {
  def tipSmtDatatypeToInductiveType(datatype: TipSmtDatatype): InductiveType = {
    val constructorDefinitions = datatype.constructors.map {
      c =>
        c.name -> c.fields.map {
          f =>
            Some(f.name) -> TBase(f.typ.typename)
        }
    }
    InductiveType(datatype.name, Nil, constructorDefinitions: _*)
  }
}
