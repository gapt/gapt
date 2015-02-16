package at.logic.language.fol.algorithms

import at.logic.language.fol._
import at.logic.proofs.lk.base.FSequent

/**
 * Created by sebastian on 2/9/15.
 */
object FOLUnificationAlgorithm extends UnificationAlgorithm {

  def unify( seq1: FSequent, seq2: FSequent ): List[Substitution] = {
    require( ( seq1._1 ++ seq1._2 ++ seq2._1 ++ seq2._2 ).forall( _.isInstanceOf[FOLFormula] ) )

    val formseq1 = FOLOr( ( seq1._1.map( x => FOLNeg( x.asInstanceOf[FOLFormula] ) ) ++ seq1._2.map( x => x.asInstanceOf[FOLFormula] ) ).toList )
    val formseq2 = FOLOr( ( seq2._1.map( x => FOLNeg( x.asInstanceOf[FOLFormula] ) ) ++ seq2._2.map( x => x.asInstanceOf[FOLFormula] ) ).toList )

    unify( formseq1, formseq2 )
  }

  def unify( term1: FOLExpression, term2: FOLExpression ): List[Substitution] =
    unifySetOfTuples( Tuple2( term1.asInstanceOf[FOLExpression], term2.asInstanceOf[FOLExpression] ) :: Nil, Nil ) match {
      case Some( ( Nil, ls ) ) => List( Substitution( ls.map( x => ( x._1.asInstanceOf[FOLVar], x._2 ) ) ) )
      case _                   => Nil
    }

  def applySubToListOfPairs( l: List[Tuple2[FOLExpression, FOLExpression]], s: Substitution ): List[Tuple2[FOLExpression, FOLExpression]] = {
    return l.map( a => ( s.apply( a._1 ), s.apply( a._2 ) ) )
  }

  def isSolvedVarIn( x: FOLVar, l: List[Tuple2[FOLExpression, FOLExpression]] ): Boolean = {
    for ( term <- ( ( l.map( ( a ) => a._1 ) ) ::: ( l.map( ( a ) => a._2 ) ) ) )
      if ( getVars( term ).contains( x ) )
        false
    true
  }

  def getVars( f: FOLExpression ): List[FOLVar] = f match {
    case ( FOLConst( c ) )      => Nil
    case FOLVar( x )            => f.asInstanceOf[FOLVar] :: Nil
    case FOLFunction( _, args ) => args.flatMap( a => getVars( a ) )
    case FOLAtom( _, args )     => args.flatMap( a => getVars( a ) )
    case FOLNeg( f )            => getVars( f )
    case FOLAnd( l, r )         => getVars( l ) ++ getVars( r )
    case FOLOr( l, r )          => getVars( l ) ++ getVars( r )
    case FOLImp( l, r )         => getVars( l ) ++ getVars( r )
  }

  def unifySetOfTuples( s1: List[( FOLExpression, FOLExpression )], s2: List[( FOLExpression, FOLExpression )] ): Option[( List[( FOLExpression, FOLExpression )], List[( FOLExpression, FOLExpression )] )] =
    ( s1, s2 ) match {
      case ( ( ( a1, a2 ) :: s ), s2 ) if a1 == a2 => unifySetOfTuples( s, s2 )

      case ( ( FOLConst( name1 ), FOLConst( name2 ) ) :: s, s2 ) if name1 != name2 => None

      case ( ( ( FOLFunction( f1, args1 ), FOLFunction( f2, args2 ) ) :: s ), s2 ) if args1.length == args2.length && f1 == f2 => unifySetOfTuples( args1.zip( args2 ) ::: s, s2 )

      case ( ( ( FOLAtom( f1, args1 ), FOLAtom( f2, args2 ) ) :: s ), s2 ) if args1.length == args2.length && f1 == f2 => unifySetOfTuples( args1.zip( args2 ) ::: s, s2 )

      case ( ( ( FOLNeg( f1 ), FOLNeg( f2 ) ) :: s ), s2 ) => unifySetOfTuples( ( f1, f2 ) :: s, s2 )

      case ( ( ( x: FOLVar, v ) :: s ), s2 ) if !getVars( v ).contains( x ) => {
        val sub = Substitution( x, v )
        unifySetOfTuples( applySubToListOfPairs( s, sub ), ( x, v ) :: applySubToListOfPairs( s2, sub ) )
      }

      case ( ( ( v, x: FOLVar ) :: s ), s2 ) if !getVars( v ).contains( x ) => {
        val sub = Substitution( x, v )
        unifySetOfTuples( applySubToListOfPairs( s, sub ), ( x, v ) :: applySubToListOfPairs( s2, sub ) )
      }

      case ( Nil, s2 ) => Some( ( Nil, s2 ) )

      case ( ( FOLAnd( l1, r1 ), FOLAnd( l2, r2 ) ) :: s, set2 ) => unifySetOfTuples( ( l1, l2 ) :: ( r1, r2 ) :: s, set2 )

      case ( ( FOLOr( l1, r1 ), FOLOr( l2, r2 ) ) :: s, set2 ) => unifySetOfTuples( ( l1, l2 ) :: ( r1, r2 ) :: s, set2 )

      case ( ( FOLImp( l1, r1 ), FOLImp( l2, r2 ) ) :: s, set2 ) => unifySetOfTuples( ( l1, l2 ) :: ( r1, r2 ) :: s, set2 )

      case _ => None
    }
}
