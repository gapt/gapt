package at.logic.gapt.formats.babel

import ast._

/**
 * Created by sebastian on 22.02.16.
 */
abstract class Signature {
  def apply( s: String ): VarConst
}

object Signature {
  def apply( set: Set[( String, ast.Type )] ): MapSignature = MapSignature( set.toMap )

  def apply( set: Set[String] )( implicit d: DummyImplicit ): MapSignature = {
    val set_ : Set[( String, ast.Type )] = for ( s <- set ) yield ( s, freshTypeVar() )
    apply( set_ )
  }

  def apply( sym: ( String, ast.Type ), syms: ( String, ast.Type )* ): MapSignature = MapSignature( ( sym +: syms ).toMap )

  def apply( sym: String, syms: String* ): MapSignature = apply( sym -> freshTypeVar(), syms map ( s => s -> freshTypeVar() ): _* )

  implicit val defaultSignature = new Signature {
    val varPattern = "[u-zU-Z].*".r

    override def apply( s: String ): VarConst = {
      if ( varPattern.pattern.matcher( s ).matches() )
        IsVar( freshTypeVar() )
      else
        IsConst( freshTypeVar() )
    }
  }
}

case class MapSignature( map: Map[String, ast.Type] ) extends Signature {
  override def apply( x: String ): VarConst =
    if ( map contains x )
      IsConst( map( x ) )
    else
      IsVar( ast.freshTypeVar() )

}

sealed trait VarConst {
  def t: ast.Type

  def isVar: Boolean
}

case class IsVar( t: ast.Type ) extends VarConst {
  def isVar = true
}

case class IsConst( t: ast.Type ) extends VarConst {
  def isVar = false
}