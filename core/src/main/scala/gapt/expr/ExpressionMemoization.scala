package gapt.expr

import scala.collection.mutable

/**
 * Provide Lambda Expression Constructors that memoize terms, allowing to compress terms.
 */
object ExpressionMemoization {
  /**
   * Create a new memoization instance
   */
  def apply() = new ExpressionMemoization
}

/**
 * Provide Lambda Expression Constructors that memoize terms, allowing to compress terms.
 */
class ExpressionMemoization {

  import gapt.expr

  private val consts = mutable.HashMap[Int, mutable.Set[expr.Const]]()
  private val vars = mutable.HashMap[Int, mutable.Set[expr.Var]]()
  private val abs = mutable.HashMap[Int, mutable.Set[expr.Abs]]()
  private val apps = mutable.HashMap[Int, mutable.Set[expr.App]]()

  def clearStorage() = {
    consts.clear()
    vars.clear()
    abs.clear()
    apps.clear()
  }

  object Const {
    def apply( name: String, ty: Ty, params: List[Ty] = Nil ) =
      consts.synchronized {
        val c = expr.Const( name, ty, params )
        val hash = name.hashCode ^ ty.hashCode
        consts.get( hash ) match {
          case Some( set ) =>
            set find ( u => c == u ) match {
              case Some( x ) => x
              case None =>
                //println( s"consts ${consts.size} / $ccount" )
                set += c
                c
            }
          case None =>
            consts( hash ) = mutable.Set( c )
            c
        }
      }
  }

  object Var {
    def apply( name: String, ty: Ty ) =
      vars.synchronized {
        val c = expr.Var( name, ty )
        val hash = name.hashCode ^ ty.hashCode
        vars.get( hash ) match {
          case Some( set ) =>
            set find ( u => c == u ) match {
              case Some( x ) => x
              case None =>
                //println( s"vars ${vars.size} / $vcount" )
                set += c
                c
            }
          case None =>
            vars( hash ) = mutable.Set( c )
            c
        }
      }
  }

  object App {
    def apply( s: expr.Expr, t: expr.Expr ) =
      apps.synchronized {
        val c = expr.App( s, t )
        val hash = s.hashCode ^ t.hashCode
        apps.get( hash ) match {
          case Some( set ) =>
            set find ( u => c == u ) match {
              case Some( x ) => x
              case None =>
                //println( s"apps ${apps.size} / $appcount" )
                set += c
                c
            }
          case None =>
            apps( hash ) = mutable.Set( c )
            c
        }
      }
  }

  object Eq {
    def apply( s: expr.Expr, t: expr.Expr ) = {
      require( s.ty == t.ty )
      App( App( EqC( s.ty ), s ), t )
    }
  }

  object Abs {
    def apply( s: expr.Var, t: expr.Expr ) =
      abs.synchronized {
        val c = expr.Abs( s, t )
        val hash = s.hashCode ^ t.hashCode
        abs.get( hash ) match {
          case Some( set ) =>
            set find ( u => c == u ) match {
              case Some( x ) => x
              case None =>
                set += c
                c
            }
          case None =>
            abs( hash ) = mutable.Set( c )
            c
        }
      }
  }

  object Expr {
    def apply( e: expr.Expr ): Expr = e match {
      case expr.Var( name, ty )           => Var( name, ty )
      case expr.Const( name, ty, params ) => Const( name, ty, params )
      case expr.App( s, t )               => App( s, t )
      case expr.Abs( v, t )               => Abs( v, t )
    }
  }

}
