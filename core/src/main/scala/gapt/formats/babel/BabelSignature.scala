package gapt.formats.babel

import gapt.expr.Const
import gapt.expr.formula.constants.LogicalC
import gapt.proofs.context.Context
import gapt.proofs.context.State
import gapt.proofs.context.facet.Facet
import gapt.proofs.context.update.Update
import gapt.{ expr => real }

/**
 * A signature for the Babel parser.  This class decides whether a free identifier is a variable or a constant.
 */
trait BabelSignature {
  /**
   * Decides whether the symbol with the given identifier should be a variable or constant, and what its type should be.
   *
   * @param s The name of the symbol.
   * @return Either IsVar(type) or IsConst(type).
   */
  def signatureLookup( s: String ): BabelSignature.VarConst

  def notationsForToken( token: Notation.Token ): Option[Notation]
  def notationsForConst( const: Notation.ConstName ): List[Notation]

  def defaultTypeToI: Boolean
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
  implicit object defaultSignature extends BabelSignature {
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

    val notations = Context.default.get[Notations] ++
      Seq( "<=", ">=", "<", ">" ).map( c => Notation.Infix( c, Precedence.infixRel ) ) ++
      Seq( "+" ).map( c => Notation.Infix( c, Precedence.plusMinus ) ) ++
      Seq( "*", "/" ).map( c => Notation.Infix( c, Precedence.timesDiv ) )

    def notationsForToken( token: Notation.Token ): Option[Notation] = notations.byToken.get( token )
    def notationsForConst( const: Notation.ConstName ): List[Notation] = notations.byConst( const )

    def defaultTypeToI: Boolean = true
  }

  sealed abstract class VarConst( val isVar: Boolean )
  /** Variable without known type. */
  case object IsVar extends VarConst( true )
  /** Constant without known type. */
  case object IsUnknownConst extends VarConst( false )
  /** Constant with known type. */
  case class IsConst( c: Const ) extends VarConst( false )
}

sealed trait Notation extends Update {
  def precedence: Int
  def token: Notation.Token
  def const: Notation.ConstName

  override def apply( ctx: Context ): State =
    ctx.state.update[Notations]( _ + this )
}
object Notation {
  case class Alias( token: Token, const: ConstName ) extends Notation { def precedence = Integer.MAX_VALUE }
  case class Prefix( token: Token, const: ConstName, precedence: Int ) extends Notation
  case class Infix( token: Token, const: ConstName, precedence: Int, leftAssociative: Boolean ) extends Notation
  object Infix {
    def apply( token: Token, const: ConstName, precedence: Int ): Infix = Infix( token, const, precedence, leftAssociative = true )
    def apply( token: String, precedence: Int, leftAssociative: Boolean ): Infix =
      Infix( Token( token ), RealConst( token ), precedence, leftAssociative )
    def apply( token: String, precedence: Int ): Infix =
      Infix( Token( token ), RealConst( token ), precedence )
  }
  case class Postfix( token: Token, const: ConstName, precedence: Int ) extends Notation
  case class Quantifier( token: Token, const: ConstName, precedence: Int ) extends Notation

  case class Token( token: String ) extends AnyVal
  object Token {
    implicit def fromString( token: String ): Token = Token( token )
  }
  sealed trait ConstName
  object ConstName {
    implicit def fromLogicalC( logicalC: LogicalC ): RealConst =
      RealConst( logicalC.name )
  }
  case class RealConst( name: String ) extends ConstName
  case object IffName extends ConstName
  case object NeqName extends ConstName

  val fakeIffConst = IffName
  val fakeNeqConst = NeqName
  def isFakeConst( const: ConstName ): Boolean = !const.isInstanceOf[RealConst]
}

case class Notations( byToken: Map[Notation.Token, Notation], byConst: Map[Notation.ConstName, List[Notation]] ) {
  def ++( notations: Iterable[Notation] ): Notations =
    notations.foldLeft( this )( _ + _ )

  def +( notation: Notation ): Notations =
    copy(
      byToken = byToken.updated( notation.token, notation ),
      byConst = byConst.updated( notation.const, notation :: byConst( notation.const ) ) )
}
object Notations {
  implicit val notationsFacet: Facet[Notations] =
    Facet( Notations( Map(), Map().withDefaultValue( Nil ) ) )
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

  def notationsForToken( token: Notation.Token ): Option[Notation] = None
  def notationsForConst( const: Notation.ConstName ): List[Notation] = Nil
  def defaultTypeToI: Boolean = true
}
object MapBabelSignature {
  def apply( consts: Iterable[real.Const] ): MapBabelSignature =
    MapBabelSignature( Map() ++ consts.view.map { c => c.name -> c } )
}
