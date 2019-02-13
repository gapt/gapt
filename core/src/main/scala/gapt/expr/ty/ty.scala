
package gapt.expr.ty

import gapt.formats.babel.BabelExporter

sealed abstract class Ty {
  def ->:( that: Ty ) = TArr( that, this )

  override def toString =
    new BabelExporter( unicode = true, sig = implicitly ).export( this )
}

case class TArr( in: Ty, out: Ty ) extends Ty

case class TBase( name: String, params: List[Ty] ) extends Ty

object TBase {

  /**
   * Creates a new base type.
   *
   * @param name The base type's name.
   * @param params The base type's type arguments.
   * @return A base type of the form (`name` `params`(0) ... `params`(n)),
   * where n is the length of `params`.
   */
  def apply( name: String, params: Ty* ): TBase = TBase( name, params.toList )
}

case class TVar( name: String ) extends Ty