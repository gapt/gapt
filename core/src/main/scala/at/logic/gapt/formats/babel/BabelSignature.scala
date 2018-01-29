package at.logic.gapt.formats.babel

import at.logic.gapt.expr.preExpr._
import at.logic.gapt.expr.{ Const, Ty, preExpr }
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
  def signatureLookup( s: String ): BabelSignature.VarConst
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

    def signatureLookup( s: String ): VarConst =
      Context.default.constant( s ) match {
        case Some( c ) => IsConst( c )
        case None =>
          s match {
            case varPattern() => IsVar
            case _            => IsUnknownConst
          }
      }
  }

  sealed abstract class VarConst( val isVar: Boolean )
  /** Variable without known type. */
  case object IsVar extends VarConst( true )
  /** Constant without known type. */
  case object IsUnknownConst extends VarConst( false )
  /** Constant with known type. */
  case class IsConst( c: Const ) extends VarConst( false )
}

/**
 * A signature based on a map: The identifiers for which the map is defined are constants, the rest are variables.
 *
 * @param map A map from strings to types.
 */
case class MapBabelSignature( map: Map[String, Const] ) extends BabelSignature {
  def signatureLookup( x: String ): BabelSignature.VarConst =
    if ( map contains x )
      BabelSignature.IsConst( map( x ) )
    else
      BabelSignature.IsVar
}
object MapBabelSignature {
  def apply( consts: Iterable[real.Const] ): MapBabelSignature =
    MapBabelSignature( Map() ++ consts.view.map { c => c.name -> c } )
}
