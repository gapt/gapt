/*
 * MinimizeSolution.scala
 *
 * Code related to the improvement of the solution for the cut-introduction problem.
 * Takes an extended Herbrand sequent with an associated solution and returns another one with an improved solution.
 */

package at.logic.algorithms.cutIntroduction

import at.logic.algorithms.resolution._
import at.logic.calculi.lk.base._
import at.logic.calculi.resolution.FClause
import at.logic.language.fol.Utils._
import at.logic.language.fol._
import at.logic.provers.Prover
import at.logic.provers.minisat.MiniSAT
import at.logic.utils.dssupport.ListSupport.mapAccumL
import at.logic.utils.executionModels.searchAlgorithms.SearchAlgorithms.DFS
import at.logic.utils.executionModels.searchAlgorithms.SearchAlgorithms.setSearch
import at.logic.utils.executionModels.searchAlgorithms.SetNode

object MinimizeSolution extends at.logic.utils.logging.Logger {

  def apply(ehs: ExtendedHerbrandSequent, prover: Prover) = {
    val minSol = improveSolution(ehs, prover).sortWith((r1,r2) => numOfAtoms(r1) < numOfAtoms(r2)).head
    new ExtendedHerbrandSequent(ehs.endSequent, ehs.grammar, minSol)
  }

  def applyEq(ehs: ExtendedHerbrandSequent, prover: Prover) = {
    val minSol = improveSolutionEq(ehs, prover).sortWith((r1,r2) => numOfAtoms(r1) < numOfAtoms(r2)).head
    new ExtendedHerbrandSequent(ehs.endSequent, ehs.grammar, minSol)
  }

  // This algorithm improves the solution using forgetful resolution and forgetful paramodulation.
  // The algorithm does naive search and is very redundant. An improved algorithm is not yet implemented,
  // but should be (e.g. analogously to improveSolution2)
  //
  // returns the list of improved solutions found by the forgetful resolution
  // and forgetful paramodulation (i.e. from the forgetful equality consequence generator).

  private def improveSolutionEq(ehs: ExtendedHerbrandSequent, prover: Prover) : List[FOLFormula] = {
    trace("entering improveSolutionEq")
    val cutFormula = ehs.cutFormula

    // Remove quantifier 
    val (xs, f) = removeQuantifiers( cutFormula )

    // Transform to conjunctive normal form
    trace( "starting CNF-Transformation" )
    val cnf = toCNF(f)
    trace( "finished CNF-Transformation" )

    // Exhaustive search over the resolvents (depth-first search),
    // returns the list of all solutions found.
    var count = 0

    def searchSolution(f: FOLFormula) : List[FOLFormula] =
      f :: oneStepEqualityImprovement(f).foldRight(List[FOLFormula]()) ( (r, acc) =>
          if( isValidWith(ehs, prover, addQuantifiers( r, xs ))) {
            count = count + 1
            searchSolution(r) ::: acc
          }
          else {
            count = count + 1
            acc
          }
        )

    searchSolution(cnf).map(s => addQuantifiers( s, xs ))
  }

  //---------------------------------------------------------------------------
  // New variant of improveSolution
  //---------------------------------------------------------------------------

  //Helper functions.

  /** Returns the Cartesian product of two sets.
    * e.g. choose2([1,2],[3,4]) = [(1,2),(1,3),(1,4),(1,5)]
    */
  def cartesianProduct[A,B](xs:List[A], ys:List[B]) = {
    xs.flatMap((x) => ys.map((y) => (x,y)))
  }

  /** Give each atom in a formula an index. Multiple occurrences of the same atom get different indices.
    * @param formula A list of clauses.
    * @return Formula, but with each atom turned into a tuple. The 2nd component is the atom's index.
    */
  def numberAtoms(formula:List[MyFClause[FOLFormula]]) =
    mapAccumL((c:Int,cl:MyFClause[FOLFormula]) => (c + cl.neg.length + cl.pos.length,
                                                   new MyFClause(cl.neg zip (Stream from c), cl.pos zip (Stream from (c + cl.neg.length)))),
              0,formula)._2

  /** Tries to minimize the canonical solution by removing as many atoms as
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
   private def improveSolution(ehs: ExtendedHerbrandSequent, prover: Prover) : List[FOLFormula] = {
      val (xs, form2) = removeQuantifiers(ehs.cutFormula)

      if (xs.length == 0) { throw new CutIntroException("ERROR: Canonical solution is not quantified.") }

      //0. Convert to a clause set where each clause is a list of positive and negative atoms.
      //1. assign a number to every atom in F.
      val fNumbered = numberAtoms(CNFp(toCNF(form2)).map(c => toMyFClause(c)).toList)

      //2. gather the positive and negative occurrences o every variable v into sets v+ and v-.
      val posNegSets = fNumbered.foldLeft(Map[FOLFormula, (Set[Int], Set[Int])]()) {(m, clause) =>
        val neg = clause.neg
        val pos = clause.pos

        //Add the negative atoms of the clause to the negative set.
        val m2 = neg.foldLeft(m) {(m, pair) => {
            val (k,v) = pair
            val (neg, pos) = m.get(k) match {
                case None => (Set[Int](),Set[Int]())
                case Some (p) => p
              }
            m + Tuple2(k, Tuple2(neg + v, pos))
          }}

        //Add the positive atoms to the positive set.
        pos.foldLeft(m2) {(m, pair) => {
            val (k,v) = pair
            val (neg, pos) = m.get(k) match {
                case None => (Set[Int](),Set[Int]())
                case Some (p) => p
              }
            m + Tuple2(k, Tuple2(neg, pos + v))
          }}
      }

      //3. for every variable v, generate every (v1 in v+, v2 in v-) and number all of the resultant pairs.
      val pairs = posNegSets.map((v) => {val (_,(n,p)) = v; cartesianProduct(n.toList,p.toList)}).flatten.zipWithIndex.toList

      //-----------------------------------------------------------------------
      //DFS starts here
      //-----------------------------------------------------------------------

      // 4) let each node of the DFS be (R,V, F'), where R is the set of resolved pairs, V is the set of resolved atoms, and F' the resulting formula.
      class ResNode(val appliedPairs:List[((Int,Int),Int)],
                    val remainingPairs:List[((Int,Int),Int)],
                    val resolvedVars:Set[Int],
                    val currentFormula: List[MyFClause[(FOLFormula, Int)]]) extends SetNode[(Int,Int)] {

        def includedElements: List[((Int, Int),Int)] = appliedPairs
        def remainingElements: List[((Int, Int),Int)] = remainingPairs
        def largerElements: List[((Int, Int),Int)] = {
          if (appliedPairs.size == 0) { remainingPairs }
          else {
            val maxIncluded = appliedPairs.map(p => p._2).max
            remainingPairs.filter(p => p._2 > maxIncluded)
          }
        }

        override def addElem(p:((Int,Int),Int)): ResNode = {
          val (pair,index) = p
          new ResNode(p::appliedPairs, remainingPairs.filter(x => x._2 != index),
                      resolvedVars + (pair._1,pair._2) , forgetfulResolve(currentFormula, pair))
        }
      }

      // 4.1) let the root be ({},{},F).
      val rootNode = new ResNode(List[((Int,Int),Int)](), pairs, Set[Int](), fNumbered)

      var satCount = 0

      // 4.2) let the successor function be succ((R,V,F)) = {(R U r,V,F'') | r in (PAIRS - R),
      //                                                                     r intersect V =  {},
      //                                                                     r > max{R}, F'' = r applied to F',
      //                                                                     F'' is still valid}
      //      (if a node has no valid successors, it is considered an end node and added to the list of solutions.)
      def elemFilter(node: ResNode, elem:((Int,Int),Int)) : Boolean = {
        //trace("elemfilter: node.appliedPairs:   " + node.appliedPairs)
        //trace("            node.remainingPairs: " + node.remainingPairs)
        //trace("            node.resolvedVars:   " + node.resolvedVars)
        //trace("            node.largerElements: " + node.largerElements)

        val ret = (!node.resolvedVars.contains(elem._1._1) && !node.resolvedVars.contains(elem._1._2))
        //trace("            RETURN: " + ret)
        ret
      }

      //node-filter which checks for validity using miniSAT
      def nodeFilter(node: ResNode) : Boolean = {
        satCount = satCount + 1
        isValidWith(ehs, prover, addQuantifiers(NumberedCNFtoFormula(node.currentFormula), xs))
      }

      //Perform the DFS
      val solutions = DFS[ResNode](rootNode, (setSearch[(Int,Int),ResNode](elemFilter, nodeFilter, _:ResNode)))

      //All-quantify the found solutions.
      //debug("IMPROVESOLUTION 2 - # of sets examined: " + satCount + ".finished")
      solutions.map(n => NumberedCNFtoFormula(n.currentFormula)).map(s => addQuantifiers(s, xs))
   }

  /** Checks if the sequent is a tautology using f as the cut formula.
    * 
    * @param prover A prover that performs the validity check.
    * @param f The formula to be checked. It will be instantiated with the
    *          eigenvariable of the solution's grammar.
    *          For details, see introqcuts.pdf, Chapter 5, Prop. 4, Example 6.
    * @return True iff f still represents a valid solution.
    */
  def isValidWith(ehs: ExtendedHerbrandSequent, prover: Prover, f: FOLFormula) : Boolean = {

    assert (ehs.grammar.slist.size == 1, "isValidWith: only simple grammars supported.")
    
    //Instantiate with the eigenvariables.
    val body = ehs.grammar.eigenvariables.foldLeft(f)((f,ev) => instantiate(f, ev))

    //Instantiate with all the values in s.
    val as = ehs.grammar.slist(0)._2.toList.foldLeft(List[FOLFormula]()) {case (acc, t) =>
      (t.foldLeft(f){case (f, sval) => instantiate(f, sval)}) :: acc
    }

    val head = And(as)

    val impl = Imp(body, head)

    val antecedent = ehs.prop_l ++ ehs.inst_l :+ impl
    val succedent = ehs.prop_r ++ ehs.inst_r

    //isTautology(FSequent(antecedent, succedent))
    //trace( "calling SAT-solver" )
    val r = prover.isValid(Imp(And(antecedent), Or(succedent)))
    //trace( "finished call to SAT-solver" )

    r
  }
  
  //------------------------ FORGETFUL RESOLUTION -------------------------//
  // TODO: this should go somewhere else.

  class MyFClause[A](val neg: List[A], val pos: List[A]) {
    override def equals( o: Any ) = o match {
      case c : MyFClause[A] => neg == c.neg && pos == c.pos
      case _ => false
    }
    override def toString = "Clause( " + neg.toString + " ; " + pos.toString + " )"
  }
 
  def toMyFClause(c: FClause) = {
    val neg = c.neg.toList.map(x => x.asInstanceOf[FOLFormula])
    val pos = c.pos.toList.map(x => x.asInstanceOf[FOLFormula])
    new MyFClause[FOLFormula](neg, pos)
  }


  // Implements the consequence generator for equality improvement:
  // either forgetful resolution or forgetful paramodulation.
  def oneStepEqualityImprovement(f: FOLFormula) : List[FOLFormula] = {
    trace("entering oneStepEqualityImprovement")
    val res = ForgetfulResolve(f) ++ ForgetfulParamodulate(f)
    res
  }


  // We assume f is in CNF. Maybe it works also for f not
  // in CNF (since CNFp transforms f to CNF?).
  //
  // Implements forgetful resolution in a naive way: if this
  // function is iterated without pruning, then duplicate
  // formulas are generated in general. This is avoided by
  // improveSolution2 (which does not use this function,
  // but implements its own version).
  //
  def ForgetfulResolve(f: FOLFormula) : List[FOLFormula] =
  {
    val clauses = CNFp(f).map(c => toMyFClause(c))
    clauses.foldLeft(List[FOLFormula]())( (list, c1) =>
      list ::: clauses.dropWhile( _ != c1).foldLeft(List[FOLFormula]())( (list2, c2) =>
        if (resolvable(c1, c2))
          CNFtoFormula( (clauses.filterNot(c => c == c1 || c == c2 ) :+ resolve(c1, c2)) )::list2
        else
          list2
      )
    )
  }

  // We assume f is in CNF. Maybe it works also for f not
  // in CNF (since CNFp transforms f to CNF?).
  //
  // Implements forgetful paramodulation.
  def ForgetfulParamodulate(f: FOLFormula) : List[FOLFormula] =
  {
    val res = ForgetfulParamodulateCNF( f ).map( cnf => CNFtoFormula( cnf.toList ) )
    trace("forgetful paramodulation generated " + res.size + " formulas.")
    res
  }

  // Implements forgetful paramodulation.
  def ForgetfulParamodulateCNF(f: FOLFormula) : List[List[MyFClause[FOLFormula]]] =
    ForgetfulParamodulateCNF( CNFp(f).map(c => toMyFClause(c)) )

  // Implements forgetful paramodulation.
  def ForgetfulParamodulateCNF(clauses: List[MyFClause[FOLFormula]]) : List[List[MyFClause[FOLFormula]]] =
  {
    clauses.foldLeft(List[List[MyFClause[FOLFormula]]]())( (list, c1) =>
      list ::: clauses.dropWhile( _ != c1).foldLeft(List[List[MyFClause[FOLFormula]]]())( (list2, c2) =>
        if ( c1 != c2 ) {  // do not paramodulate a clause into itself
          val paras = Paramodulants( c1, c2 )
          paras.map( p => (clauses.filterNot(c => c == c1 || c == c2 ) :+ p)).toList ++ list2
        } else
          list2
      )
    )
  }

  private def getArgs( margs: List[Set[FOLTerm]] ) = {
    val res = margs.foldLeft(Set(List[FOLTerm]()))( (args, res) => args.flatMap( a => res.map( r => a :+ r ) ) )
    res
  }

  // Computes ground paramodulants including the trivial one
  def Paramodulants(s: FOLTerm, t: FOLTerm, r: FOLTerm) : Set[FOLTerm] = r match {
    case _ if r == s => Set(t) ++ Set(r)
    case Function(f, args) => {
      val margs = args.map( a => Paramodulants( s, t, a ) )
      getArgs( margs ).map( args => Function( f, args ) )
    }
    case _ => Set(r)
  }

  // Computes ground paramodulants without the trivial one
  def Paramodulants(s: FOLTerm, t: FOLTerm, f: FOLFormula) : Set[FOLFormula] = {
    val res = f match {
    case Atom( x, args ) => {
      val margs = args.map( a => Paramodulants( s, t, a ) )
      getArgs( margs ).map( args => Atom( x, args ) ) - f
    }
  }
    trace("paramodulants for " + s + " = " + t + " into " + f + " : " + res)
    res
  }

  private def getParaLeft( eq: FOLFormula, aux: FOLFormula, main: FOLFormula, left: MyFClause[FOLFormula], right: MyFClause[FOLFormula] ) =
  new MyFClause( left.neg ++ right.neg.filterNot( f => f == aux ) :+ main, left.pos.filterNot( f => f == eq) ++ right.pos )

  private def getParaRight( eq: FOLFormula, aux: FOLFormula, main: FOLFormula, left: MyFClause[FOLFormula], right: MyFClause[FOLFormula] ) =
  new MyFClause( left.neg ++ right.neg, left.pos.filterNot( f => f == eq) ++ right.pos.filterNot( f => f == aux ) :+ main  )

  def Paramodulants( c1: MyFClause[FOLFormula], c2: MyFClause[FOLFormula] ) : Set[MyFClause[FOLFormula]] =
    myParamodulants( c1, c2 ) ++ myParamodulants( c2, c1 )

  // Computes ground paramodulants
  def myParamodulants( left: MyFClause[FOLFormula], right: MyFClause[FOLFormula] ) : Set[MyFClause[FOLFormula]]=
  left.pos.foldLeft(Set[MyFClause[FOLFormula]]())( (res, eq) =>
    res ++ (eq match {
      case Equation( s, t ) => right.neg.flatMap( aux => (Paramodulants( s, t, aux ) ++ Paramodulants( t, s, aux )).map( para =>
        getParaLeft( eq, aux, para, left, right )
      ) ) ++
      right.pos.flatMap( aux => (Paramodulants( s, t, aux ) ++ Paramodulants( t, s, aux )).map( para =>
        getParaRight( eq, aux, para, left, right )
      ) ).toSet
    case _ => Set()
  }))

  /** Converts a CNF back into a FOL formula.
    */
  def CNFtoFormula( cls : List[MyFClause[FOLFormula]] ) : FOLFormula =
  {
    val nonEmptyClauses = cls.filter(c => c.neg.length > 0 || c.pos.length > 0).toList

    if (nonEmptyClauses.length == 0) { TopC }
    else { And(nonEmptyClauses.map( c => Or(c.pos ++ c.neg.map( l => Neg(l) )) )) }
  }

  /** Converts a numbered CNF back into a FOL formula.
    */
  def NumberedCNFtoFormula( cls : List[MyFClause[(FOLFormula, Int)]] ) : FOLFormula = {
    val nonEmptyClauses = cls.filter(c => c.neg.length > 0 || c.pos.length > 0).toList

    if (nonEmptyClauses.length == 0) { TopC }
    else { And(nonEmptyClauses.map( c => Or(c.pos.map(l => l._1) ++ c.neg.map( l => Neg(l._1) )) )) }
  }

  // Checks if complementary literals exist, and if
  // the clauses are not identical.
  def resolvable(l: MyFClause[FOLFormula], r: MyFClause[FOLFormula]) =
    l != r && (l.pos.exists( f => r.neg.contains(f) ) || l.neg.exists(f => r.pos.contains(f)) )

  // Assumes that resolvable(l, r). Does propositional resolution.
  // TODO: incorporate contraction.
  def resolve(l: MyFClause[FOLFormula], r: MyFClause[FOLFormula]) : MyFClause[FOLFormula] =
  {
    val cl = l.pos.find( f => r.neg.contains(f) )
    if (cl != None)
      //new MyFClause[FOLFormula]( l.neg ++ (r.neg - cl.get) , (l.pos - cl.get) ++ r.pos )
      // Using diff to remove only one copy of cl.get (the - operator is deprecated)
      new MyFClause[FOLFormula]( l.neg ++ ( r.neg.diff(List(cl.get)) ) , ( l.pos.diff(List(cl.get)) ) ++ r.pos )
    else
    {
      val cr = l.neg.find( f => r.pos.contains(f) ).get
      //new MyFClause[FOLFormula]( (l.neg - cr) ++ r.neg, l.pos ++ (r.pos - cr) )
      // Using diff to remove only one copy of cr (the - operator is deprecated)
      new MyFClause[FOLFormula]( ( l.neg.diff(List(cr)) ) ++ r.neg, l.pos ++ ( r.pos.diff(List(cr)) ) )
    }
  }

  /** Given a formula and a pair of indices (i,j), resolves the two clauses which contain i & j.
    * The original two clauses are deleted and the new, merged clauses is added to the formula.
    *
    * The order of the clauses is NOT preserved!
    *
    * @param cls The formula in numbered clause form: each atom is tuple of the atom itself and its index.
    * @param pair The two atom indices indicating the atoms to be resolved.
    * @return The original formula, with the two resolved clauses deleted and the new, resolved clause added.
    */
  def forgetfulResolve(cls: List[MyFClause[(FOLFormula, Int)]], pair:(Int, Int)) : List[MyFClause[(FOLFormula, Int)]] = {

    /** If either component of pair is present in clause, (clause',True)
      * is returned, where clause' is clause, with the occurring atoms deleted.
      * Otherwise, (clause,False) is returned.
      */
    def resolveClause(clause:MyFClause[(FOLFormula, Int)], pair: (Int, Int)) = {
      val neg = clause.neg.filter(a => a._2 != pair._1 && a._2 != pair._2)
      val pos = clause.pos.filter(a => a._2 != pair._1 && a._2 != pair._2)

      (new MyFClause(neg, pos), neg.length != clause.neg.length || pos.length != clause.pos.length)
    }

    val emptyClause = new MyFClause[(FOLFormula, Int)](Nil, Nil)

    def mergeClauses(clauses:List[MyFClause[(FOLFormula, Int)]]) : MyFClause[(FOLFormula, Int)] = {
      clauses.foldLeft(emptyClause)((c1, c2) => new MyFClause(c1.neg ++ c2.neg, c1.pos ++ c2.pos))
    }

    val startVal = (List[MyFClause[(FOLFormula, Int)]](), List[MyFClause[(FOLFormula, Int)]]())

    //Goes through all clauses with fold, trying to delete the atoms given by pair.
    val (f, rest) = cls.foldLeft(startVal)((x:(List[MyFClause[(FOLFormula, Int)]], List[MyFClause[(FOLFormula, Int)]]), clause:MyFClause[(FOLFormula,Int)]) => {
        val (formula, mergingClause) = x
        val (clause2,resolved) = resolveClause(clause, pair)

        //The first clause was resolved => add it to the temporary mergingClause instead of formula.
        if (resolved && mergingClause.length == 0) { (formula, clause2::Nil) }
        //The 2nd clause was resolved => merge the two clauses and add the result to formula.
        else if (resolved) { (mergeClauses(clause2::mergingClause)::formula, Nil) }
        //No clause was resolved => add the clause as is to the formula and continue.
        else {(clause::formula, mergingClause)}
      })

    //If both atoms were part of the same clause, rest is non-empty. In this case, add rest's 1 clause again.
    if (rest.length > 0) { (rest.head)::f } else { f }
  }
 
  //-----------------------------------------------------------------------//


}
