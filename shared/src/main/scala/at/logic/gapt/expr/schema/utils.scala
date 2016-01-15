/*
 * Functions that operate on Schema-expressions
 *
 */

package at.logic.gapt.expr.schema

import at.logic.gapt.expr._

object isAtom {
  def apply( f: SchemaFormula ): Boolean = f match {
    case SchemaAtom( _, _ )       => true
    case IndexedPredicate( _, _ ) => true
    case _                        => false
  }
}
object isSAtom {
  def apply( f: SchemaFormula ): Boolean = f match {
    case sAtom( _, _ ) => true
    case _             => false
  }
}

object unfoldSFormula {
  def apply( f: SchemaFormula ): SchemaFormula = f match {
    case SchemaAtom( name: Var, args )   => SchemaAtom( name, args.map( t => unfoldSTerm( t ) ) )
    case SchemaAtom( name: Const, args ) => SchemaAtom( name, args.map( t => unfoldSTerm( t ) ) )
    case Imp( f1, f2 )                   => Imp( unfoldSFormula( f1 ), unfoldSFormula( f2 ) )
    case Ex( v, f )                      => Ex( v, unfoldSFormula( f ) )
    case All( v, f )                     => All( v, unfoldSFormula( f ) )
    case _                               => f
  }
}

object unfoldSTerm {
  //TODO : needs improvement for the step case
  def apply( e: SchemaExpression ): SchemaExpression = {
    val k = IntVar( "k" )
    val x = foVar( "x" )
    e match {
      case sTerm( func, i, arg ) if dbTRS.map.contains( func ) => {
        if ( i == IntZero() ) {
          val base = dbTRS.map.get( func ).get._1._2
          val new_map = Map[Var, SchemaExpression]() + Tuple2( x, arg.head )
          val subst = SchemaSubstitution( new_map )
          subst( base )
        } else if ( i == k ) e
        else i match {
          case Succ( _ ) => dbTRS.map.get( func ).get._2._2 match {
            case foTerm( name, arg1 ) => foTerm( name, unfoldSTerm( sTerm( func, Pred( i.asInstanceOf[IntegerTerm] ), arg ) ) :: Nil )
          }
          case _ =>
            val j = unfoldSINDTerm( i )
            unfoldSTerm( sTerm( func, j, arg ) )
        }
      }
      case sTerm( func, i, arg ) => e
      case foTerm( holvar, arg ) => foTerm( holvar, unfoldSTerm( arg ) :: Nil )
      case _                     => e
    }
  }
}

object unfoldSINDTerm {
  def apply( e: SchemaExpression ): SchemaExpression = {
    val k = IntVar( "k" )
    e match {
      case sIndTerm( func, i ) if dbTRS.map.contains( func ) => {
        if ( i == IntZero() ) dbTRS.map.get( func ).get._1._2
        else if ( i == k ) e
        else {
          val step = dbTRS.map.get( func ).get._2._2
          val new_map = Map[Var, SchemaExpression]() + Tuple2( k, Pred( i.asInstanceOf[IntegerTerm] ) )
          val subst = SchemaSubstitution( new_map )
          subst( step )
        }
      }
      case _ => e
    }
  }
}

object toIntegerTerm {
  def apply( i: Int ): SchemaExpression = {
    if ( i == 0 )
      IntZero()
    else
      Succ( toIntegerTerm( i - 1 ) )
  }
}

