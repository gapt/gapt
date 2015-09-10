/*
 * MinimizeSolution.scala
 *
 * Code related to the improvement of the solution for the cut-introduction problem.
 * Takes an extended Herbrand sequent with an associated solution and returns another one with an improved solution.
 */

package at.logic.gapt.proofs.lk.cutIntroduction

import at.logic.gapt.proofs.resolution.{ ForgetfulResolveIndexed, ForgetfulParamodulate, ForgetfulResolve }
import at.logic.gapt.proofs.{ HOLSequent, FOLClause }
import at.logic.gapt.proofs._
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.provers.Prover
import at.logic.gapt.utils.dssupport.ListSupport
import at.logic.gapt.utils.executionModels.searchAlgorithms.SearchAlgorithms.DFS
import at.logic.gapt.utils.executionModels.searchAlgorithms.SearchAlgorithms.setSearch
import at.logic.gapt.utils.executionModels.searchAlgorithms.SetNode

object MinimizeSolution extends at.logic.gapt.utils.logging.Logger {

  // Solution simplification for n == 1 cuts, with equality.
  def applyEq( ehs: ExtendedHerbrandSequent, prover: Prover ) = {
    val improvedSol = improveSolutionGen( ehs, prover, improveSolutionEq1 )
    new ExtendedHerbrandSequent( ehs.endSequent, ehs.grammar, improvedSol )
  }

  // Solution simplification for n >= 1 cuts, without equality.
  def apply( ehs: ExtendedHerbrandSequent, prover: Prover ) = {
    val improvedSol = improveSolutionGen( ehs, prover, improveSolution1 )
    new ExtendedHerbrandSequent( ehs.endSequent, ehs.grammar, improvedSol )
  }

  private def chooseSolution( list: List[FOLFormula] ) = list.sortWith( ( r1, r2 ) => numOfAtoms( r1 ) < numOfAtoms( r2 ) ).head

  // Solution simplification for n >= 1 cuts, without equality.
  // returns the list of cut-formulas of the improved solution.
  private def improveSolutionGen( ehs: ExtendedHerbrandSequent, prover: Prover, improve1: ( ExtendedHerbrandSequent, Prover ) => List[FOLFormula] ): List[FOLFormula] = {
    val grammar = ehs.grammar
    val n = grammar.ss.size

    trace( "improving solution for n = " + n )

    val list = ( 1 to n ).foldLeft( Nil: List[FOLFormula] ) {
      case ( cfs, k ) => {
        trace( "k: " + k )
        trace( "current cut-formulas: " + cfs )
        trace( "getting intermediary solution" )
        val is = getIntermediarySolution( ehs, cfs )

        trace( "I_" + k + ": " + is )
        assert( prover.isValid( is.getDeep ) )
        trace( "I_" + k + " is valid." )

        trace( "improving intermediary solution" )
        val cf = chooseSolution( improve1( is, prover ) )
        trace( "got improved cut-formula: " + cf )

        val test_ehs = new ExtendedHerbrandSequent( is.endSequent, is.grammar, cf :: Nil )
        assert( prover.isValid( test_ehs.getDeep ) )
        trace( "I_" + k + " with cf: " + test_ehs.getDeep )

        cfs :+ cf
      }
    }
    list.reverse
  }

  // constructs the grammar U \circ_{alpha_1} S_1 ... \circ_{alpha_{l-1}} S_{l-1}
  private def getIntermediaryGrammar( l: Int, grammar: MultiGrammar ) = {
    val us = grammar.us
    val ss = grammar.ss.take( l - 1 )
    new MultiGrammar( us, ss )
  }

  // Computes T_l as in the definition of intermediary solution
  private def getT( l: Int, grammar: MultiGrammar ): Map[FOLFormula, List[List[FOLTerm]]] =
    if ( l == 0 )
      grammar.us
    else
      getIntermediaryGrammar( l, grammar ).language

  // computes D as in the proof of Lemma 11
  // cfs is the list F_n, ..., F_l
  private def getD( grammar: MultiGrammar, cfs: List[FOLFormula] ): MultiGrammar = {
    val n = grammar.ss.size
    val k = cfs.size + 1
    val l = n - k + 1

    trace( "computing D for l = " + l )

    val myss = grammar.ss.reverse.take( n - l )
    val us = getT( l, grammar )
    val p = grammar.ss( l - 1 )
    val ss = p :: Nil
    val res = new MultiGrammar( us, ss )

    assert( res.language == us ++ getT( l + 1, grammar ) )

    res
  }

  private def getCutImpl( cf: FOLFormula, alpha: List[FOLVar], ts: List[List[FOLTerm]] ) = {
    val ant = instantiate( cf, alpha )
    val succ = And( ts.map( termlist => instantiate( cf, termlist ) ).toList )
    Imp( ant, succ )
  }

  // cfs is the list F_n, ..., F_l
  private def getIntermediaryContext( grammar: MultiGrammar, cfs: List[FOLFormula] ): List[FOLFormula] = {
    val n = grammar.ss.size
    val k = cfs.size + 1
    val l = n - k + 1

    val myss = grammar.ss.reverse.take( n - l )

    ( cfs zip myss ).map {
      case ( cf, ( alpha, termlistlist ) ) => getCutImpl( cf, alpha, termlistlist )
    }
  }

  private def instantiateSequent( seq: HOLSequent, map: Map[FOLFormula, List[List[FOLTerm]]] ) = {
    def fun( l: Seq[FOLFormula] ) = l.flatMap( f =>
      map.get( f ) match {
        case None                 => f :: Nil
        case Some( termlistlist ) => instantiate( f, termlistlist )
      } )

    new HOLSequent( fun( seq.antecedent.asInstanceOf[List[FOLFormula]] ), fun( seq.succedent.asInstanceOf[List[FOLFormula]] ) )
  }

  // Computes the intermediary solution, which is an extended herbrand sequent with a MultiGrammar
  // for one cut, incorporating previous cut-formulas (in cfs) into the base sequent.
  private def getIntermediarySolution( base: ExtendedHerbrandSequent, cfs: List[FOLFormula] ) = {
    val k = cfs.size + 1
    val grammar = base.grammar
    val n = grammar.ss.size
    val alphas = grammar.eigenvariables
    val l = n - k + 1
    val orig_es = base.endSequent

    trace( "computing context of intermediary solution" )
    val es1 = new HOLSequent( getIntermediaryContext( grammar, cfs ), Nil )
    trace( "computed context (es1): " + es1 )
    //    trace( "computing ES-part of intermediary solution" )
    //    val es2 = instantiateSequent( orig_es, getT( l, grammar ) )
    //    trace( "ES-part (es2): " + es2 )

    //    trace("es1 compose es2: " + (es1 compose es2))

    val d = getD( grammar, cfs )
    trace( "d.us:" + d.us )
    trace( "d.ss:" + d.ss )
    trace( "canon. sol. based on d: " + CutIntroduction.computeCanonicalSolutions( d ) )

    new ExtendedHerbrandSequent( es1 compose orig_es, d, CutIntroduction.computeCanonicalSolutions( d ) )
  }

  // This algorithm improves the solution using forgetful resolution and forgetful paramodulation
  // for one cut.
  // The algorithm does naive search and is very redundant. An improved algorithm is not yet implemented,
  // but should be (e.g. analogously to improveSolution2)
  //
  // returns the list of improved solutions found by the forgetful resolution
  // and forgetful paramodulation (i.e. from the forgetful equality consequence generator).

  private def improveSolutionEq1( ehs: ExtendedHerbrandSequent, prover: Prover ): List[FOLFormula] = {
    assert( ehs.cutFormulas.length == 1, "Solution minimization only implemented for one cut formula." )

    trace( "entering improveSolutionEq1" )
    val cutFormula = ehs.cutFormulas.head

    // Remove quantifier 
    val ( xs, f ) = cutFormula match {
      case All.Block( vars, form ) => ( vars, form )
    }

    // Transform to conjunctive normal form
    trace( "starting CNF-Transformation" )
    val cnf = CNFp.toFormula( f )
    trace( "finished CNF-Transformation" )

    // Exhaustive search over the resolvents (depth-first search),
    // returns the list of all solutions found.
    var count = 0

    def searchSolution( f: FOLFormula ): List[FOLFormula] =
      f :: oneStepEqualityImprovement( f ).foldRight( List[FOLFormula]() )( ( r, acc ) =>
        if ( isValidWith( ehs, prover, All.Block( xs, r ) ) ) {
          count = count + 1
          searchSolution( r ) ::: acc
        } else {
          count = count + 1
          acc
        } )

    searchSolution( cnf ).map( s => All.Block( xs, s ) )
  }

  //---------------------------------------------------------------------------
  // New variant of improveSolution
  //---------------------------------------------------------------------------

  //Helper functions.

  /**
   * Give each atom in a formula an index. Multiple occurrences of the same atom get different indices.
   * @param formula A list of clauses.
   * @return Formula, but with each atom turned into a tuple. The 2nd component is the atom's index.
   */
  def numberAtoms( formula: List[FOLClause] ) =
    ListSupport.mapAccumL(
      ( c: Int, cl: FOLClause ) => ( c + cl.negative.length + cl.positive.length,
        new Clause( cl.negative zip ( Stream from c ), cl.positive zip ( Stream from ( c + cl.negative.length ) ) ) ),
      0, formula
    )._2

  /**
   * Tries to minimize the canonical solution for one cut by removing as many atoms as
   * as possible through forgetful resolution.
   *
   * The original variant did a DFS, with the successor-nodes of a formula being
   * all possible resolutions of a single pair of atoms. If we identify every
   * pair of atoms (say, the pairs a,b,c in a formula F with n atoms), then this creates
   * on the order of O((n²)!) redudant paths in the search tree, since
   * the application of the resolution to pairs [a,b] is identical to applying
   * it to pairs [b,a].
   *
   * This variant of improveSolution uses the following strategy:
   * <pre>
   * 1) assign a number to every atom in F.
   * 2) gather the positive and negative occurrences of every variable v into sets v+ and v-.
   * 3) for every variable v, generate every (v1 in v+, v2 in v-) and number all of the resultant pairs.
   *    Let this set of pairs be called PAIRS.
   * 4) let each node of the DFS be (R,V,F'), where R is the set of resolved pairs, V is the set of resolved atoms, and F' the resulting formula.
   * 4.1) let the root be ({},{},F).
   * 4.2) let the successor function be succ((R,V,F)) = {(R U r,V,F'') | r in (PAIRS - R),
   *                                                                     r intersect V =  {},
   *                                                                     r > max{R}, F'' = r applied to F',
   *                                                                     F'' is still valid}
   *      (if a node has no valid successors, it is considered an end node and added to the list of solutions.)
   * </pre>
   *
   * Due to the ordering of the pairs, no node will have descendants in which lower elements entered its R and each set of resolvents will
   * only be generated once.
   *
   * @param form The canonical solution to be improved (doesn't have to be in CNF).
   * @return The list of minimal-size solutions (=the set of end nodes as described in 4.2).
   */
  private def improveSolution1( ehs: ExtendedHerbrandSequent, prover: Prover ): List[FOLFormula] = {
    assert( ehs.cutFormulas.length == 1, "Solution minimization only implemented for one cut formula." )

    val ( xs, form2 ) = ehs.cutFormulas.head match {
      case All.Block( vars, form ) => ( vars, form )
    }

    if ( xs.length == 0 ) { throw new CutIntroException( "ERROR: Canonical solution is not quantified." ) }

    //0. Convert to a clause set where each clause is a list of positive and negative atoms.
    //1. assign a number to every atom in F.
    val fNumbered = numberAtoms( CNFp.toClauseList( form2 ).toList )

    //2. gather the positive and negative occurrences o every variable v into sets v+ and v-.
    val posNegSets = fNumbered.foldLeft( Map[FOLFormula, ( Set[Int], Set[Int] )]() ) { ( m, clause ) =>
      val neg = clause.negative
      val pos = clause.positive

      //Add the negative atoms of the clause to the negative set.
      val m2 = neg.foldLeft( m ) { ( m, pair ) =>
        {
          val ( k, v ) = pair
          val ( neg, pos ) = m.get( k ) match {
            case None      => ( Set[Int](), Set[Int]() )
            case Some( p ) => p
          }
          m + Tuple2( k, Tuple2( neg + v, pos ) )
        }
      }

      //Add the positive atoms to the positive set.
      pos.foldLeft( m2 ) { ( m, pair ) =>
        {
          val ( k, v ) = pair
          val ( neg, pos ) = m.get( k ) match {
            case None      => ( Set[Int](), Set[Int]() )
            case Some( p ) => p
          }
          m + Tuple2( k, Tuple2( neg, pos + v ) )
        }
      }
    }

    //3. for every variable v, generate every (v1 in v+, v2 in v-) and number all of the resultant pairs.
    val pairs = posNegSets.map( ( v ) => { val ( _, ( n, p ) ) = v; ListSupport.product( n.toList, p.toList ) } ).flatten.zipWithIndex.toList

    //-----------------------------------------------------------------------
    //DFS starts here
    //-----------------------------------------------------------------------

    // 4) let each node of the DFS be (R,V, F'), where R is the set of resolved pairs, V is the set of resolved atoms, and F' the resulting formula.
    class ResNode(
        val appliedPairs:   List[( ( Int, Int ), Int )],
        val remainingPairs: List[( ( Int, Int ), Int )],
        val resolvedVars:   Set[Int],
        val currentFormula: List[Clause[( FOLAtom, Int )]]
    ) extends SetNode[( Int, Int )] {

      def includedElements: List[( ( Int, Int ), Int )] = appliedPairs
      def remainingElements: List[( ( Int, Int ), Int )] = remainingPairs
      def largerElements: List[( ( Int, Int ), Int )] = {
        if ( appliedPairs.size == 0 ) { remainingPairs }
        else {
          val maxIncluded = appliedPairs.map( p => p._2 ).max
          remainingPairs.filter( p => p._2 > maxIncluded )
        }
      }

      override def addElem( p: ( ( Int, Int ), Int ) ): ResNode = {
        val ( pair, index ) = p
        new ResNode( p :: appliedPairs, remainingPairs.filter( x => x._2 != index ),
          resolvedVars + ( pair._1, pair._2 ), ForgetfulResolveIndexed( currentFormula, pair ) )
      }
    }

    // 4.1) let the root be ({},{},F).
    val rootNode = new ResNode( List[( ( Int, Int ), Int )](), pairs, Set[Int](), fNumbered )

    var satCount = 0

    // 4.2) let the successor function be succ((R,V,F)) = {(R U r,V,F'') | r in (PAIRS - R),
    //                                                                     r intersect V =  {},
    //                                                                     r > max{R}, F'' = r applied to F',
    //                                                                     F'' is still valid}
    //      (if a node has no valid successors, it is considered an end node and added to the list of solutions.)
    def elemFilter( node: ResNode, elem: ( ( Int, Int ), Int ) ): Boolean = {
      //trace("elemfilter: node.appliedPairs:   " + node.appliedPairs)
      //trace("            node.remainingPairs: " + node.remainingPairs)
      //trace("            node.resolvedVars:   " + node.resolvedVars)
      //trace("            node.largerElements: " + node.largerElements)

      val ret = ( !node.resolvedVars.contains( elem._1._1 ) && !node.resolvedVars.contains( elem._1._2 ) )
      //trace("            RETURN: " + ret)
      ret
    }

    //node-filter which checks for validity using miniSAT
    def nodeFilter( node: ResNode ): Boolean = {
      satCount = satCount + 1
      isValidWith( ehs, prover, All.Block( xs, FOLClause.NumberedCNFtoFormula( node.currentFormula ) ) )
    }

    //Perform the DFS
    val solutions = DFS[ResNode]( rootNode, ( setSearch[( Int, Int ), ResNode]( elemFilter, nodeFilter, _: ResNode ) ) )

    //All-quantify the found solutions.
    //debug("IMPROVESOLUTION 2 - # of sets examined: " + satCount + ".finished")
    solutions.map( n => FOLClause.NumberedCNFtoFormula( n.currentFormula ) ).map( s => All.Block( xs, s ) )
  }

  /**
   * Checks if the sequent is a tautology using f as the cut formula.
   *
   * @param prover A prover that performs the validity check.
   * @param f The formula to be checked. It will be instantiated with the
   *          eigenvariable of the solution's grammar.
   *          For details, see introqcuts.pdf, Chapter 5, Prop. 4, Example 6.
   * @return True iff f still represents a valid solution.
   */
  def isValidWith( ehs: ExtendedHerbrandSequent, prover: Prover, f: FOLFormula ): Boolean = {
    assert( ehs.grammar.ss.size == 1, "isValidWith: only simple grammars supported." )
    val test_ehs = new ExtendedHerbrandSequent( ehs.endSequent, ehs.grammar, f :: Nil )
    prover.isValid( test_ehs.getDeep )
  }

  // Implements the consequence generator for equality improvement:
  // either forgetful resolution or forgetful paramodulation.
  def oneStepEqualityImprovement( f: FOLFormula ): List[FOLFormula] = {
    trace( "entering oneStepEqualityImprovement" )
    val res = ForgetfulResolve( f ) ++ ForgetfulParamodulate( f )
    res
  }

}
