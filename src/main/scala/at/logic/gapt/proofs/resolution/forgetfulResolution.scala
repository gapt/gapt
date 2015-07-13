package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.CNFp

object ForgetfulResolve {
  def apply( clauses: List[FOLClause] ): List[List[FOLClause]] =
    clauses.map { c => apply_( clauses.dropWhile( _ != c ), c ) }.filterNot( _.isEmpty )

  def apply( f: FOLFormula ): List[FOLFormula] = apply( CNFp.toClauseList( f ) ).map( FOLClause.CNFtoFormula )

  def apply_( clauses: List[FOLClause], c: FOLClause ): List[FOLClause] = {
    ( List[FOLClause]() /: clauses )( ( acc, ci ) =>
      if ( resolvable( ci, c ) )
        resolve( ci, c ) +: acc
      else
        acc )
  }

  // TODO: I've taken the following two functions directly from MinimizeSolution. Perhaps they already exist in the resolution code?

  // Checks if complementary literals exist, and if
  // the clauses are not identical.
  private def resolvable( l: FOLClause, r: FOLClause ) =
    l != r && ( l.positive.exists( f => r.negative.contains( f ) ) || l.negative.exists( f => r.positive.contains( f ) ) )

  // Assumes that resolvable(l, r). Does propositional resolution.
  // TODO: incorporate contraction.
  private def resolve( l: FOLClause, r: FOLClause ): FOLClause =
    {
      val cl = l.positive.find( f => r.negative.contains( f ) )
      if ( cl != None )
        //new FOLClause( l.negative ++ (r.negative - cl.get) , (l.positive - cl.get) ++ r.positive )
        // Using diff to remove only one copy of cl.get (the - operator is deprecated)
        new FOLClause( l.negative ++ ( r.negative.diff( List( cl.get ) ) ), ( l.positive.diff( List( cl.get ) ) ) ++ r.positive )
      else {
        val cr = l.negative.find( f => r.positive.contains( f ) ).get
        //new FOLClause( (l.negative - cr) ++ r.negative, l.positive ++ (r.positive - cr) )
        // Using diff to remove only one copy of cr (the - operator is deprecated)
        new FOLClause( ( l.negative.diff( List( cr ) ) ) ++ r.negative, l.positive ++ ( r.positive.diff( List( cr ) ) ) )
      }
    }

}

object ForgetfulParamodulate {

  def apply( f: FOLFormula ): List[FOLFormula] = apply( CNFp.toClauseList( f ) ).map( FOLClause.CNFtoFormula )

  def apply( clauses: List[FOLClause] ): List[List[FOLClause]] =
    {
      clauses.foldLeft( List[List[FOLClause]]() )( ( list, c1 ) =>
        list ::: clauses.dropWhile( _ != c1 ).foldLeft( List[List[FOLClause]]() )( ( list2, c2 ) =>
          if ( c1 != c2 ) { // do not paramodulate a clause into itself
            val paras = Paramodulants( c1, c2 )
            paras.map( p => ( clauses.filterNot( c => c == c1 || c == c2 ) :+ p ) ).toList ++ list2
          } else
            list2 ) )
    }
}

object Paramodulants {

  def apply( c1: FOLClause, c2: FOLClause ): Set[FOLClause] =
    myParamodulants( c1, c2 ) ++ myParamodulants( c2, c1 )

  // Computes ground paramodulants including the trivial one
  def apply( s: FOLTerm, t: FOLTerm, r: FOLTerm ): Set[FOLTerm] = r match {
    case _ if r == s => Set( t ) ++ Set( r )
    case FOLFunction( f, args ) => {
      val margs = args.map( a => Paramodulants( s, t, a ) )
      getArgs( margs ).map( args => FOLFunction( f, args ) )
    }
    case _ => Set( r )
  }

  // Computes ground paramodulants without the trivial one
  def apply( s: FOLTerm, t: FOLTerm, f: FOLFormula ): Set[FOLFormula] = {
    val res = f match {
      case FOLAtom( x, args ) => {
        val margs = args.map( a => Paramodulants( s, t, a ) )
        getArgs( margs ).map( args => FOLAtom( x, args ) ) - f
      }
    }
    res
  }

  // Computes ground paramodulants
  private def myParamodulants( left: FOLClause, right: FOLClause ): Set[FOLClause] =
    left.positive.foldLeft( Set[FOLClause]() )( ( res, eq ) =>
      res ++ ( eq match {
        case Eq( s, t ) => right.negative.flatMap( aux => ( Paramodulants( s, t, aux ) ++ Paramodulants( t, s, aux ) ).map( para =>
          getParaLeft( eq, aux, para, left, right ) ) ) ++
          right.positive.flatMap( aux => ( Paramodulants( s, t, aux ) ++ Paramodulants( t, s, aux ) ).map( para =>
            getParaRight( eq, aux, para, left, right ) ) ).toSet
        case _ => Set()
      } ) )

  private def getArgs( margs: List[Set[FOLTerm]] ) = {
    val res = margs.foldLeft( Set( List[FOLTerm]() ) )( ( args, res ) => args.flatMap( a => res.map( r => a :+ r ) ) )
    res
  }

  private def getParaLeft( eq: FOLFormula, aux: FOLFormula, main: FOLFormula, left: FOLClause, right: FOLClause ) =
    new Clause( left.negative ++ right.negative.filterNot( f => f == aux ) :+ main, left.positive.filterNot( f => f == eq ) ++ right.positive )

  private def getParaRight( eq: FOLFormula, aux: FOLFormula, main: FOLFormula, left: FOLClause, right: FOLClause ) =
    new Clause( left.negative ++ right.negative, left.positive.filterNot( f => f == eq ) ++ right.positive.filterNot( f => f == aux ) :+ main )

}

// TODO: I honestly have no idea what the relationship of this algorithm to the other one (ForgetfulResolve) is supposed to be.
object forgetfulResolve {
  /**
   * Given a formula and a pair of indices (i,j), resolves the two clauses which contain i & j.
   * The original two clauses are deleted and the new, merged clauses is added to the formula.
   *
   * The order of the clauses is NOT preserved!
   *
   * @param cls The formula in numbered clause form: each atom is tuple of the atom itself and its index.
   * @param pair The two atom indices indicating the atoms to be resolved.
   * @return The original formula, with the two resolved clauses deleted and the new, resolved clause added.
   */
  def apply( cls: List[Clause[( FOLFormula, Int )]], pair: ( Int, Int ) ): List[Clause[( FOLFormula, Int )]] = {

    /**
     * If either component of pair is present in clause, (clause',True)
     * is returned, where clause' is clause, with the occurring atoms deleted.
     * Otherwise, (clause,False) is returned.
     */
    def resolveClause( clause: Clause[( FOLFormula, Int )], pair: ( Int, Int ) ) = {
      val neg = clause.negative.filter( a => a._2 != pair._1 && a._2 != pair._2 )
      val pos = clause.positive.filter( a => a._2 != pair._1 && a._2 != pair._2 )

      ( new Clause( neg, pos ), neg.length != clause.negative.length || pos.length != clause.positive.length )
    }

    val emptyClause = new Clause[( FOLFormula, Int )]( Nil, Nil )

    def mergeClauses( clauses: List[Clause[( FOLFormula, Int )]] ): Clause[( FOLFormula, Int )] = {
      clauses.foldLeft( emptyClause )( ( c1, c2 ) => new Clause( c1.negative ++ c2.negative, c1.positive ++ c2.positive ) )
    }

    val startVal = ( List[Clause[( FOLFormula, Int )]](), List[Clause[( FOLFormula, Int )]]() )

    //Goes through all clauses with fold, trying to delete the atoms given by pair.
    val ( f, rest ) = cls.foldLeft( startVal )( ( x: ( List[Clause[( FOLFormula, Int )]], List[Clause[( FOLFormula, Int )]] ), clause: Clause[( FOLFormula, Int )] ) => {
      val ( formula, mergingClause ) = x
      val ( clause2, resolved ) = resolveClause( clause, pair )

      //The first clause was resolved => add it to the temporary mergingClause instead of formula.
      if ( resolved && mergingClause.length == 0 ) {
        ( formula, clause2 :: Nil )
      } //The 2nd clause was resolved => merge the two clauses and add the result to formula.
      else if ( resolved ) {
        ( mergeClauses( clause2 :: mergingClause ) :: formula, Nil )
      } //No clause was resolved => add the clause as is to the formula and continue.
      else {
        ( clause :: formula, mergingClause )
      }
    } )

    //If both atoms were part of the same clause, rest is non-empty. In this case, add rest's 1 clause again.
    if ( rest.length > 0 ) {
      ( rest.head ) :: f
    } else {
      f
    }
  }
}
