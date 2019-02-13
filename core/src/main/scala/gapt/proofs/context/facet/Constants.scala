package gapt.proofs.context.facet

import gapt.expr.Const
import gapt.expr.subst.Substitution
import gapt.expr.ty.TVar
import gapt.expr.ty.Ty

/** Constant symbols, including defined constants, constructors, etc. */
case class Constants( constants: Map[String, Const] ) {
  def +( const: Const ): Constants = {
    require(
      !constants.contains( const.name ),
      s"Constant $const is already defined as ${constants( const.name )}." )
    copy( constants + ( const.name -> const ) )
  }

  def ++( consts: Traversable[Const] ): Constants =
    consts.foldLeft( this )( _ + _ )

  def lookup( name: String, params: List[Ty] ): Option[Const] =
    constants.get( name ).flatMap {
      case c @ Const( _, _, Nil ) if params.isEmpty => Some( c )
      case Const( _, ty, declPs ) if declPs.size == params.size =>
        val subst = Substitution( Nil, declPs.asInstanceOf[List[TVar]] zip params )
        Some( Const( name, subst( ty ), params ) )
      case _ => None
    }

  override def toString = constants.values.toSeq.sortBy( _.name ).
    map( c => s"${c.name}${if ( c.params.isEmpty ) "" else c.params.mkString( "{", " ", "}" )}: ${c.ty}" ).mkString( "\n" )
}

object Constants {
  implicit val constsFacet: Facet[Constants] = Facet( Constants( Map() ) )
}
