/*
 * The definition of Indexed proposition is taken from:
 * A Schemata Calculus for Propositional Logic by Vincent Aravantinos, Ricardo Caferra, and Nicolas Peltier
 *
 */

package at.logic.gapt.expr.schema

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.expr.schema.logicSymbols._

object Tindex extends TBase( "ω" )

/******************** SPECIAL INTEGERS ************************************/

object IntVar {
  def apply( name: String ) = Var( StringSymbol( name ), Tindex )
  def unapply( t: IntegerTerm ) = t match {
    case Var( name, Tindex ) => Some( name )
    case _                   => None
  }
}

object IntConst {
  def apply( sym: SymbolA ): IntConst = Const( sym, Tindex )
  def unapply( t: IntegerTerm ) = t match {
    case c @ Const( name, Tindex ) => Some( c.asInstanceOf[Const].sym )
    case _                         => None
  }
}

object IntZero extends MonomorphicLogicalC( "0", Tindex )

/**************************************************************************/

object IndexedPredicate {
  def apply( name: String, indexTerms: List[SchemaExpression] ): SchemaFormula = {
    val pred = Const( name, FunctionType( To, indexTerms.head.exptype :: Nil ) )
    App( pred, indexTerms.head :: Nil ).asInstanceOf[SchemaFormula]
  }
  def apply( sym: SymbolA, indexTerms: List[SchemaExpression] ): SchemaFormula = {
    val pred = Const( sym, FunctionType( To, indexTerms.head.exptype :: Nil ) )
    App( pred, indexTerms.head :: Nil ).asInstanceOf[SchemaFormula]
  }
  def apply( name: String, indexTerm: IntegerTerm ): SchemaFormula = apply( name, indexTerm :: Nil )

  def unapply( expression: SchemaExpression ): Option[( Const, List[SchemaExpression] )] = expression match {
    case HOLAtom( head: Const, args ) if args.forall( t => t.exptype == Tindex ) =>
      Some( ( head, args ) )
    case _ => None
  }

}

case class IndexedVarSymbol( name: String, val index: SchemaExpression ) extends SymbolA {
  override def toString = name + "(" + index + ")"
}

object indexedFOVar {
  def apply( name: String, i: SchemaExpression ) = Var( IndexedVarSymbol( name, i ), Ti )
  def unapply( s: SchemaExpression ) = s match {
    case Var( _, Ti ) => s.asInstanceOf[Var].sym match {
      case IndexedVarSymbol( name, index ) => Some( name, index )
      case _                               => None
    }
    case _ => None
  }
}

object indexedOmegaVar {
  def apply( name: String, i: SchemaExpression ) = Var( IndexedVarSymbol( name, i ), Tindex )
  def unapply( s: SchemaExpression ) = s match {
    case Var( _, Tindex ) => s.asInstanceOf[Var].sym match {
      case IndexedVarSymbol( name, index ) => Some( name, index )
      case _                               => None
    }
    case _ => None
  }
}

object foVar {
  def apply( name: String ) = FOLVar( name )
  def unapply( t: FOLVar ) = FOLVar.unapply( t )
}

//indexed second-order variable of type: ind->i
object fo2Var {
  def apply( name: String ) = Var( name, Tindex -> Ti )
  def unapply( s: SchemaExpression ) = s match {
    case Var( name, Tindex -> Ti ) => Some( name )
    case _                         => None
  }
}

//first-order constant
object foConst {
  def apply( name: String ) = FOLConst( name )
  def unapply( t: FOLConst ) = FOLConst.unapply( t )
}

//first-order variable of type ω
object fowVar {
  def apply( name: String ) = Var( name, Tindex )
  def unapply( t: SchemaExpression ) = t match {
    case Var( name, Tindex ) => Some( name, Tindex )
    case _                   => None
  }
}

object SchemaFunction {
  /*
  def apply(head: Var, args: List[SchemaExpression]): SchemaExpression = apply_(head, args)
  def apply(head: Const, args: List[SchemaExpression]): SchemaExpression = apply_(head, args)
  */

  // I added the following method to replace the ones above to avoid case distinctions
  // in user code. Maybe better: Add a trait "AtomHead" or something, and add it to
  // both Const and Var. Then, use SchemaExpression with AtomHead instead
  // of SchemaExpression below.
  //
  // The above methods are not so good since the unapply method returns SchemaExpressions,
  // which cannot directly be fed to the above apply methods without casting/case distinction.
  //
  def apply( head: SchemaExpression, args: List[SchemaExpression] ): SchemaExpression = {
    require( head.isInstanceOf[Var] || head.isInstanceOf[Const] )
    apply_( head, args )
  }

  private def apply_( head: SchemaExpression, args: List[SchemaExpression] ): SchemaExpression = args match {
    case Nil     => head
    case t :: tl => apply_( App( head, t ), tl )
  }

  def unapply( expression: SchemaExpression ) = expression match {
    case App( c: Const, _ ) if isLogicalConstant( c )           => None
    case App( App( c: Const, _ ), _ ) if isLogicalConstant( c ) => None
    case App( _, _ ) if ( expression.exptype != To ) =>
      val t = unapply_( expression )
      Some( ( t._1, t._2, expression.exptype ) )
    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_( e: SchemaExpression ): ( SchemaExpression, List[SchemaExpression] ) = e match {
    case v: Var   => ( v, Nil )
    case c: Const => ( c, Nil )
    case App( e1, e2 ) =>
      val t = unapply_( e1 )
      ( t._1, t._2 :+ e2 )
  }
}

/*************** OPERATORS *****************/

object BigAndC extends MonomorphicLogicalC( BigAndSymbol.toString, ( Tindex -> To ) -> ( Tindex -> ( Tindex -> To ) ) )
object BigOrC extends MonomorphicLogicalC( BigOrSymbol.toString, ( ( Tindex -> To ) -> ( Tindex -> ( Tindex -> To ) ) ) )
object BiggerThanC extends MonomorphicLogicalC( BiggerThanSymbol.toString, ( Tindex -> ( Tindex -> To ) ) )
object LessThanC extends MonomorphicLogicalC( LessThanSymbol.toString, ( Tindex -> ( Tindex -> To ) ) )
object LeqC extends MonomorphicLogicalC( LeqSymbol.toString, ( Tindex -> ( Tindex -> To ) ) )
object SuccC extends MonomorphicLogicalC( "s", ( Tindex -> Tindex ) )

object BigAnd {
  def apply( i: IntVar, iter: SchemaFormula, init: IntegerTerm, end: IntegerTerm ): SchemaFormula =
    apply( Abs( i, iter ), init, end )

  def apply( iter: Abs, init: IntegerTerm, end: IntegerTerm ): SchemaFormula =
    App( BigAndC(), iter :: init :: end :: Nil ).asInstanceOf[SchemaFormula]

  def unapply( expression: SchemaExpression ) = expression match {
    case App( App( App( BigAndC(), Abs( v, formula ) ), init: IntegerTerm ), end: IntegerTerm ) =>
      Some( v, formula.asInstanceOf[SchemaFormula], init, end )
    case _ => None
  }
}

object BigOr {
  def apply( i: IntVar, iter: SchemaFormula, init: IntegerTerm, end: IntegerTerm ): SchemaFormula =
    apply( Abs( i, iter ), init, end )

  def apply( iter: Abs, init: IntegerTerm, end: IntegerTerm ): SchemaFormula =
    App( BigOrC(), iter :: init :: end :: Nil ).asInstanceOf[SchemaFormula]

  def unapply( expression: SchemaExpression ) = expression match {
    case App( App( App( BigOrC(), Abs( v, formula ) ), init: IntegerTerm ), end: IntegerTerm ) =>
      Some( v, formula.asInstanceOf[SchemaFormula], init, end )
    case _ => None
  }
}

object BiggerThan {
  def apply( l: IntegerTerm, r: IntegerTerm ) = App( App( BiggerThanC(), l ), r )
  def unapply( e: SchemaExpression ) = e match {
    case App( App( BiggerThanC(), l ), r ) => Some( ( l, r ) )
    case _                                 => None
  }
}

object Succ {
  def apply( t: IntegerTerm ): IntegerTerm = App( SuccC(), t ).asInstanceOf[IntegerTerm]
  //  def apply( t: SchemaExpression ): SchemaExpression = App( SuccC, t )
  def unapply( p: SchemaExpression ) = p match {
    case App( SuccC(), t: IntegerTerm ) => Some( t )
    case _                              => None
  }
}

object Pred {
  def apply( t: IntegerTerm ): IntegerTerm = t match {
    case Succ( t1 ) => t1
    case _          => throw new Exception( "ERROR in Predecessor" )
  }
}

//object representing a schematic atom: P(i:ω, args)
object SchemaAtom {
  /*
  def apply(head: Var, args: List[SchemaExpression]): SchemaFormula = apply_(head, args).asInstanceOf[SchemaFormula]

  def apply(head: Const, args: List[SchemaExpression]): SchemaFormula = apply_(head, args).asInstanceOf[SchemaFormula]
  */

  // I added the following method to replace the ones above to avoid case distinctions
  // in user code. Maybe better: Add a trait "AtomHead" or something, and add it to
  // both Const and Var. Then, use SchemaExpression with AtomHead instead
  // of SchemaExpression below.
  //
  // The above methods are not so good since the unapply method returns SchemaExpressions,
  // which cannot directly be fed to the above apply methods without casting/case distinction.
  //
  def apply( head: SchemaExpression, args: List[SchemaExpression] ): SchemaFormula = {
    require( head.isInstanceOf[Var] || head.isInstanceOf[Const] )
    apply_( head, args ).asInstanceOf[SchemaFormula]
  }

  private def apply_( head: SchemaExpression, args: List[SchemaExpression] ): SchemaExpression = args match {
    case Nil     => head
    case t :: tl => apply_( App( head, t ), tl )
  }

  def unapply( expression: SchemaExpression ) = expression match {
    case App( c: Const, _ ) if isLogicalConstant( c ) => None
    case App( App( c: Const, _ ), _ ) if isLogicalConstant( c ) => None
    case App( _, _ ) if ( expression.exptype == To ) => Some( unapply_( expression ) )
    case Const( _, _ ) if ( expression.exptype == To ) => Some( ( expression, Nil ) )
    case Var( _, _ ) if ( expression.exptype == To ) => Some( ( expression, Nil ) )
    case _ => None
  }

  // Recursive unapply to get the head and args
  private def unapply_( e: SchemaExpression ): ( SchemaExpression, List[SchemaExpression] ) = e match {
    case v: Var   => ( v, Nil )
    case c: Const => ( c, Nil )
    case App( e1, e2 ) =>
      val t = unapply_( e1 )
      ( t._1, t._2 :+ e2 )

  }
}

object lessThan {
  def apply( left: SchemaExpression, right: SchemaExpression ) = {
    require( left.exptype == right.exptype )
    App( App( LessThanC(), left ), right ).asInstanceOf[SchemaFormula]
  }

  def unapply( expression: SchemaExpression ) = expression match {
    case App( App( LessThanC(), left ), right ) => Some( left, right )
    case _                                      => None
  }
}

object leq {
  def apply( left: SchemaExpression, right: SchemaExpression ) = {
    require( left.exptype == right.exptype )
    App( App( LeqC(), left ), right ).asInstanceOf[SchemaFormula]
  }

  def unapply( expression: SchemaExpression ) = expression match {
    case App( App( LeqC(), left ), right ) => Some( left, right )
    case _                                 => None
  }
}

object aTerm {
  def apply( name: Const, ind: IntegerTerm ): IntegerTerm = {
    App( name, ind ).asInstanceOf[IntegerTerm]
  }
}

// Create a var or const????
object foTerm {
  def apply( name: String, args: List[SchemaExpression] ): SchemaExpression = {
    val v = Var( name, args.head.exptype -> Ti )
    App( v, args.head )
  }

  def apply( v: SchemaExpression, args: List[SchemaExpression] ): SchemaExpression = {
    App( v, args.head )
  }

  def unapply( s: SchemaExpression ) = s match {
    case a: App if a.arg.exptype == Ti && a.function.exptype == Ti -> Ti => Some( a.function.asInstanceOf[SchemaExpression], a.arg.asInstanceOf[SchemaExpression] )
    case _ => None
  }
}

// TODO: this seems to be hardcoded for a a single parameter
// plus 0 or 1 arguments. Generalize to simplify the code!
object sTerm {
  //the i should be of type Tindex !
  def apply( f: String, i: SchemaExpression, l: List[SchemaExpression] ): SchemaExpression = {
    require( i.exptype == Tindex )
    if ( l.isEmpty ) {
      val func = Const( f, Tindex -> Ti )
      return App( func, i )
    } else {
      val func = Const( f, Tindex -> ( Ti -> Ti ) )
      return App( App( func, i ), l.head )
    }
  }

  def apply( f: Const, i: SchemaExpression, l: List[SchemaExpression] ): SchemaExpression = {
    require( i.exptype == Tindex )
    if ( l.isEmpty ) App( f, i )
    else App( App( f, i ), l.head )
  }

  def unapply( s: SchemaExpression ) = s match {
    case App( App( func: Const, i ), arg ) if i.exptype == Tindex => Some( ( func, i, arg :: Nil ) )
    case App( func: Const, i ) if i.exptype == Tindex => Some( ( func, i, Nil ) )
    case _ => None
  }
}

//indexed s-term of type ω->ω
object sIndTerm {
  //the i should be of type Tindex !
  def apply( f: String, i: IntegerTerm ): SchemaExpression = {
    val func = Const( f, Tindex -> Tindex )
    return App( func, i )
  }

  def unapply( s: SchemaExpression ) = s match {
    case App( func: Const, i ) if i.exptype == Tindex => Some( ( func, i ) )
    case _ => None
  }
}

//This version of the function is used specifically to find the highest level subterms
//within atoms and satoms. Terms within terms are not located within the set.
object SchemaSubTerms {
  def apply( f: LambdaExpression ): Seq[LambdaExpression] = f match {
    case Var( _, _ )           => List( f )
    case SchemaAtom( _, args ) => args.map( a => apply( a.asInstanceOf[SchemaExpression] ) ).flatten
    case SchemaFunction( _, args, _ ) => {
      List( f ).toSeq
    }

    case And( x, y ) => apply( x.asInstanceOf[SchemaExpression] ) ++ apply( y.asInstanceOf[LambdaExpression] )
    case Or( x, y )  => apply( x.asInstanceOf[SchemaExpression] ) ++ apply( y.asInstanceOf[LambdaExpression] )
    case Imp( x, y ) => apply( x.asInstanceOf[SchemaExpression] ) ++ apply( y.asInstanceOf[LambdaExpression] )
    case Neg( x )    => apply( x.asInstanceOf[SchemaExpression] )
    case Ex( v, x )  => apply( x.asInstanceOf[SchemaExpression] )
    case All( v, x ) => apply( x.asInstanceOf[SchemaExpression] )
    case Abs( _, x ) => apply( x.asInstanceOf[SchemaExpression] )
    case App( x, y ) => List( f ).toSeq
  }
}

//object representing a schematic atom: P(i:ω, args)
object sAtom {
  def apply( sym: SymbolA, args: List[SchemaExpression] ): SchemaFormula = {
    val pred: Var = Var( sym, FunctionType( To, args.map( a => a.exptype ) ) )
    apply( pred, args )
  }

  def unapply( s: SchemaExpression ) = s match {
    case App( func: Const, i ) if i.exptype == Tindex => Some( ( func, i ) )
    case _ => None
  }

  def apply( head: Var, args: List[SchemaExpression] ): SchemaFormula = {
    App( head, args ).asInstanceOf[SchemaFormula]
  }

}

//database for trs
object dbTRS extends Iterable[( Const, ( ( SchemaExpression, SchemaExpression ), ( SchemaExpression, SchemaExpression ) ) )] {
  val map = new scala.collection.mutable.HashMap[Const, ( ( SchemaExpression, SchemaExpression ), ( SchemaExpression, SchemaExpression ) )]

  def get( name: Const ) = map( name )

  def getOption( name: Const ) = map.get( name )

  def clear = map.clear

  def add( name: Const, base: ( SchemaExpression, SchemaExpression ), step: ( SchemaExpression, SchemaExpression ) ): Unit = {
    map.put( name, ( base, step ) )

  }

  def iterator = map.iterator
}

object SimsC extends MonomorphicLogicalC( simSymbol.toString, Ti -> ( Ti -> To ) )

class sTermRewriteSys( val func: Const, val base: SchemaExpression, val rec: SchemaExpression )

object sTermRewriteSys {
  def apply( f: Const, base: SchemaExpression, step: SchemaExpression ) = new sTermRewriteSys( f, base, step )
}

object sims {
  def apply( left: SchemaExpression, right: SchemaExpression ) = {
    require( left.exptype == right.exptype )
    App( App( SimsC(), left ), right ).asInstanceOf[SchemaFormula]
  }

  def unapply( expression: SchemaExpression ) = expression match {
    case App( App( SimsC(), left ), right ) => Some( left.asInstanceOf[SchemaExpression], right.asInstanceOf[SchemaExpression] )
    case _                                  => None
  }
}

object sTermDB extends Iterable[( Const, sTermRewriteSys )] with TraversableOnce[( Const, sTermRewriteSys )] {
  val terms = new scala.collection.mutable.HashMap[Const, sTermRewriteSys]

  def clear = terms.clear

  def get( func: Const ) = terms( func )

  def put( sterm: sTermRewriteSys ) = terms.put( sterm.func, sterm )

  def iterator = terms.iterator
}
