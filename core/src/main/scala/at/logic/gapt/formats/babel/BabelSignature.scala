package at.logic.gapt.formats.babel

import ast._
import at.logic.gapt.expr.Ty
import at.logic.gapt.proofs.Context
import at.logic.gapt.{ expr => real }

/**
 * A signature for the Babel parser.  This class decides whether a free identifier is a variable or a constant.
 */
abstract class BabelSignature {
  /**
   * Decides whether the symbol with the given identifier should be a variable or constant, and what its type should be.
   *
   * @param s The name of the symbol.
   * @return Either IsVar(type) or IsConst(type).
   */
  def apply( s: String ): VarConst

  /**
   * Returns true iff the symbol with the given identifier is a variable.
   *
   * @param s The name of the symbol.
   * @return
   */
  def isVar( s: String ): Boolean = apply( s ).isVar
}

/**
 * Contains various methods for generating signatures.
 *
 */
object BabelSignature {
  /**
   * The signature that the Babel parser will use if no other signature is in scope. In this signature, identifiers denote
   * variables iff they start with [u-zU-Z]. The types of all identifiers are arbitrary.
   */
  implicit val defaultSignature = new BabelSignature {
    val varPattern = "[u-zU-Z].*".r

    override def apply( s: String ): VarConst =
      Context.default.constant( s ) match {
        case Some( c ) => IsConst( Some( c.exptype ) )
        case None =>
          s match {
            case varPattern() => IsVar( None )
            case _            => IsConst( None )
          }
      }
  }
}

/**
 * A signature based on a map: The identifiers for which the map is defined are constants, the rest are variables.
 *
 * @param map A map from strings to types.
 */
case class MapBabelSignature( map: Map[String, Ty] ) extends BabelSignature {
  override def apply( x: String ): VarConst =
    if ( map contains x )
      IsConst( Some( map( x ) ) )
    else
      IsVar( None )
}
object MapBabelSignature {
  def apply( consts: Iterable[real.Const] ): MapBabelSignature =
    MapBabelSignature( consts.view map { c => c.name -> c.exptype } toMap )
}

/**
 * Class with two possible cases, one for variables and one for constants.
 */
sealed trait VarConst {
  def ty: Option[Ty]
  def isVar: Boolean
}

case class IsVar( ty: Option[Ty] ) extends VarConst {
  def isVar = true
}

case class IsConst( ty: Option[Ty] ) extends VarConst {
  def isVar = false
}