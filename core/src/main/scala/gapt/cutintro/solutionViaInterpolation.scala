package gapt.cutintro

import gapt.expr._
import gapt.expr.hol.simplify
import gapt.provers.smtlib.SmtInterpolSession

import scala.collection.mutable

/**
 * Solution finding algorithm for Π₁-cut-introduction based on the Duality algorithm for
 * constrained Horn clause verification[1].
 *
 * [1] K. L. McMillan, A. Rybalchenko, Solving Constrained Horn Clauses using Interpolation,
 *     technical report MSR-TR-2013-6, available at
 *     https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/MSR-TR-2013-6.pdf
 */
object solutionViaInterpolation {

  def apply( sehs: SchematicExtendedHerbrandSequent ): Seq[FOLFormula] = {
    val nameGen = rename.awayFrom( containedNames( sehs.us ) ++ containedNames( sehs.ss ) )

    val assertions = mutable.Buffer[Formula]()
    val startOfSubtree = mutable.Buffer[Int]()
    val predicate = mutable.Buffer[Int]()
    val substitution = mutable.Buffer[Substitution]()
    def mkAssRefs( i: Int, subst: Substitution ): Seq[Formula] =
      for ( s <- subst( sehs.ss( i )._2 ) ) yield {
        val vs_ = sehs.ss( i )._1.map( v => Const( nameGen.fresh( v.name ), v.ty ) )
        mkAssertions( i, subst compose Substitution( sehs.ss( i )._1 zip vs_ ) )
        And( ( vs_, s ).zipped.map( Eq( _, _ ) ) )
      }
    def mkAssertions( i: Int, subst: Substitution ): Unit = {
      val start = assertions.length
      assertions += ( And( if ( i > 0 ) mkAssRefs( i - 1, subst ) else Seq() ) &
        subst( sehs.esInstancesInScope( i ).toNegConjunction ) )
      predicate += i
      substitution += subst
      startOfSubtree += start
    }

    assertions += And( mkAssRefs( sehs.ss.size - 1, Substitution() ) )
    startOfSubtree += 0
    predicate += sehs.ss.size
    substitution += Substitution()

    import gapt.provers.Session._, cats.implicits._
    val solver = new SmtInterpolSession()
    solver.run( setOption( "produce-proofs", "true" ) >>
      setLogic( "QF_UF" ) >>
      declareSymbolsIn( assertions ) )
    val labels = for {
      a <- assertions
      l = nameGen.freshWithIndex( "l" )
      _ = solver.run( assert( a, l ) )
    } yield l

    require( solver.run( checkUnsat ).right.get )

    val interps =
      solver.script.getInterpolants(
        labels.map( solver.script.term( _ ) ).toArray,
        startOfSubtree.toArray ).
        view.
        map( solver.expr ).
        map( _.asInstanceOf[Formula] ).
        map( simplify( _ ) ).
        toList

    val generalized =
      for ( ( i, s ) <- interps zip substitution )
        yield TermReplacement( i, s.map.map( _.swap ) )

    val solution =
      for ( i <- sehs.ss.indices )
        yield And( generalized.zip( predicate ).filter( _._2 == i ).map( _._1 ).distinct )

    solution.map( _.asInstanceOf[FOLFormula] )
  }

}
