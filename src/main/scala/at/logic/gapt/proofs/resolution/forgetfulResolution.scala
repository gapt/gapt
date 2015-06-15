package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.CNFp

class MyFClause[A]( val neg: List[A], val pos: List[A] ) {
  override def equals( o: Any ) = o match {
    case c: MyFClause[A] => neg == c.neg && pos == c.pos
    case _               => false
  }
  override def hashCode() = 41 * neg.hashCode() + pos.hashCode()

  override def toString = "Clause( " + neg.toString + " ; " + pos.toString + " )"
}

object MyFClause {
  def toMyFClause( c: FClause ): MyFClause[FOLFormula] = {
    val neg = c.neg.toList.map( x => x.asInstanceOf[FOLFormula] )
    val pos = c.pos.toList.map( x => x.asInstanceOf[FOLFormula] )
    new MyFClause[FOLFormula]( neg, pos )
  }

  /**
   * Converts a CNF back into a FOL formula.
   */
  def CNFtoFormula( cls: List[MyFClause[FOLFormula]] ): FOLFormula =
    {
      val nonEmptyClauses = cls.filter( c => c.neg.length > 0 || c.pos.length > 0 ).toList

      if ( nonEmptyClauses.length == 0 ) { Top() }
      else { And( nonEmptyClauses.map( c => Or( c.pos ++ c.neg.map( l => Neg( l ) ) ) ) ) }
    }

  /**
   * Converts a numbered CNF back into a FOL formula.
   */
  def NumberedCNFtoFormula( cls: List[MyFClause[( FOLFormula, Int )]] ): FOLFormula = {
    val nonEmptyClauses = cls.filter( c => c.neg.length > 0 || c.pos.length > 0 ).toList

    if ( nonEmptyClauses.length == 0 ) { Top() }
    else { And( nonEmptyClauses.map( c => Or( c.pos.map( l => l._1 ) ++ c.neg.map( l => Neg( l._1 ) ) ) ) ) }
  }
}

object ForgetfulResolve {
  import MyFClause._

  def apply( clauses: List[MyFClause[FOLFormula]] ): List[List[MyFClause[FOLFormula]]] =
    clauses.map { c => apply_( clauses.dropWhile( _ != c ), c ) }.filterNot( _.isEmpty )

  def apply( f: FOLFormula ): List[FOLFormula] = apply( CNFp.toFClauseList( f ).map( toMyFClause ) ).map( CNFtoFormula )

  def apply_( clauses: List[MyFClause[FOLFormula]], c: MyFClause[FOLFormula] ): List[MyFClause[FOLFormula]] = {
    ( List[MyFClause[FOLFormula]]() /: clauses )( ( acc, ci ) =>
      if ( resolvable( ci, c ) )
        resolve( ci, c ) +: acc
      else
        acc )
  }

  // TODO: I've taken the following two functions directly from MinimizeSolution. Perhaps they already exist in the resolution code?

  // Checks if complementary literals exist, and if
  // the clauses are not identical.
  private def resolvable( l: MyFClause[FOLFormula], r: MyFClause[FOLFormula] ) =
    l != r && ( l.pos.exists( f => r.neg.contains( f ) ) || l.neg.exists( f => r.pos.contains( f ) ) )

  // Assumes that resolvable(l, r). Does propositional resolution.
  // TODO: incorporate contraction.
  private def resolve( l: MyFClause[FOLFormula], r: MyFClause[FOLFormula] ): MyFClause[FOLFormula] =
    {
      val cl = l.pos.find( f => r.neg.contains( f ) )
      if ( cl != None )
        //new MyFClause[FOLFormula]( l.neg ++ (r.neg - cl.get) , (l.pos - cl.get) ++ r.pos )
        // Using diff to remove only one copy of cl.get (the - operator is deprecated)
        new MyFClause[FOLFormula]( l.neg ++ ( r.neg.diff( List( cl.get ) ) ), ( l.pos.diff( List( cl.get ) ) ) ++ r.pos )
      else {
        val cr = l.neg.find( f => r.pos.contains( f ) ).get
        //new MyFClause[FOLFormula]( (l.neg - cr) ++ r.neg, l.pos ++ (r.pos - cr) )
        // Using diff to remove only one copy of cr (the - operator is deprecated)
        new MyFClause[FOLFormula]( ( l.neg.diff( List( cr ) ) ) ++ r.neg, l.pos ++ ( r.pos.diff( List( cr ) ) ) )
      }
    }

}

object ForgetfulParamodulate {
  import MyFClause._

  def apply( f: FOLFormula ): List[FOLFormula] = apply( CNFp.toFClauseList( f ).map( toMyFClause ) ).map( CNFtoFormula )

  def apply( clauses: List[MyFClause[FOLFormula]] ): List[List[MyFClause[FOLFormula]]] =
    {
      clauses.foldLeft( List[List[MyFClause[FOLFormula]]]() )( ( list, c1 ) =>
        list ::: clauses.dropWhile( _ != c1 ).foldLeft( List[List[MyFClause[FOLFormula]]]() )( ( list2, c2 ) =>
          if ( c1 != c2 ) { // do not paramodulate a clause into itself
            val paras = Paramodulants( c1, c2 )
            paras.map( p => ( clauses.filterNot( c => c == c1 || c == c2 ) :+ p ) ).toList ++ list2
          } else
            list2 ) )
    }
}

object Paramodulants {

  def apply( c1: MyFClause[FOLFormula], c2: MyFClause[FOLFormula] ): Set[MyFClause[FOLFormula]] =
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
  private def myParamodulants( left: MyFClause[FOLFormula], right: MyFClause[FOLFormula] ): Set[MyFClause[FOLFormula]] =
    left.pos.foldLeft( Set[MyFClause[FOLFormula]]() )( ( res, eq ) =>
      res ++ ( eq match {
        case Eq( s, t ) => right.neg.flatMap( aux => ( Paramodulants( s, t, aux ) ++ Paramodulants( t, s, aux ) ).map( para =>
          getParaLeft( eq, aux, para, left, right ) ) ) ++
          right.pos.flatMap( aux => ( Paramodulants( s, t, aux ) ++ Paramodulants( t, s, aux ) ).map( para =>
            getParaRight( eq, aux, para, left, right ) ) ).toSet
        case _ => Set()
      } ) )

  private def getArgs( margs: List[Set[FOLTerm]] ) = {
    val res = margs.foldLeft( Set( List[FOLTerm]() ) )( ( args, res ) => args.flatMap( a => res.map( r => a :+ r ) ) )
    res
  }

  private def getParaLeft( eq: FOLFormula, aux: FOLFormula, main: FOLFormula, left: MyFClause[FOLFormula], right: MyFClause[FOLFormula] ) =
    new MyFClause( left.neg ++ right.neg.filterNot( f => f == aux ) :+ main, left.pos.filterNot( f => f == eq ) ++ right.pos )

  private def getParaRight( eq: FOLFormula, aux: FOLFormula, main: FOLFormula, left: MyFClause[FOLFormula], right: MyFClause[FOLFormula] ) =
    new MyFClause( left.neg ++ right.neg, left.pos.filterNot( f => f == eq ) ++ right.pos.filterNot( f => f == aux ) :+ main )

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
  def apply( cls: List[MyFClause[( FOLFormula, Int )]], pair: ( Int, Int ) ): List[MyFClause[( FOLFormula, Int )]] = {

    /**
     * If either component of pair is present in clause, (clause',True)
     * is returned, where clause' is clause, with the occurring atoms deleted.
     * Otherwise, (clause,False) is returned.
     */
    def resolveClause( clause: MyFClause[( FOLFormula, Int )], pair: ( Int, Int ) ) = {
      val neg = clause.neg.filter( a => a._2 != pair._1 && a._2 != pair._2 )
      val pos = clause.pos.filter( a => a._2 != pair._1 && a._2 != pair._2 )

      ( new MyFClause( neg, pos ), neg.length != clause.neg.length || pos.length != clause.pos.length )
    }

    val emptyClause = new MyFClause[( FOLFormula, Int )]( Nil, Nil )

    def mergeClauses( clauses: List[MyFClause[( FOLFormula, Int )]] ): MyFClause[( FOLFormula, Int )] = {
      clauses.foldLeft( emptyClause )( ( c1, c2 ) => new MyFClause( c1.neg ++ c2.neg, c1.pos ++ c2.pos ) )
    }

    val startVal = ( List[MyFClause[( FOLFormula, Int )]](), List[MyFClause[( FOLFormula, Int )]]() )

    //Goes through all clauses with fold, trying to delete the atoms given by pair.
    val ( f, rest ) = cls.foldLeft( startVal )( ( x: ( List[MyFClause[( FOLFormula, Int )]], List[MyFClause[( FOLFormula, Int )]] ), clause: MyFClause[( FOLFormula, Int )] ) => {
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
