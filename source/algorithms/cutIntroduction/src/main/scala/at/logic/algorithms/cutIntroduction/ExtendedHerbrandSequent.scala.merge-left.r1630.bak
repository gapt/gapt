/*
 *  Extended Herbrand Sequent implementation
 *
 *  For more details on what this is, see: Towards Algorithmic Cut Introduction
 *  (S. Hetzl, A. Leitsch, D. Weller - LPAR-18, 2012)
 *
 */

package at.logic.algorithms.cutIntroduction

import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.language.fol._
import at.logic.language.fol.Utils._
import at.logic.algorithms.lk.solvePropositional._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.algorithms.resolution._
import at.logic.calculi.resolution.base.FClause
import at.logic.utils.logging.Logger
import scala.collection.immutable.Stack
import at.logic.algorithms.cutIntroduction.CutIntroduction.MyFClause
import at.logic.utils.dssupport.ListSupport.mapAccumL
import at.logic.utils.executionModels.searchAlgorithms.SearchAlgorithms.DFS
import at.logic.utils.executionModels.searchAlgorithms.SearchAlgorithms.setSearch
import at.logic.utils.executionModels.searchAlgorithms.SetNode
import at.logic.provers.minisat.MiniSAT


// NOTE: implemented for the one cut case.
// NOTE2: seq should be prenex and skolemized 
class ExtendedHerbrandSequent(seq: Sequent, g: Grammar, cf: FOLFormula = null) extends Logger {
 
  val endSequent = seq
  val flatterms = g.flatterms
  val grammar = g

  // From ".map" on are lots of castings just to make the data structure right :-|
  // FormulaOccurrence to HOLFormula to FOLFormula and Seq to List...
  
  // Propositional formulas on the left
  private val prop_l : List[FOLFormula] = seq.antecedent.filter(x => !x.formula.containsQuantifier).map(x => x.formula.asInstanceOf[FOLFormula]).toList
  // Propositional formulas on the right
  private val prop_r : List[FOLFormula] = seq.succedent.filter(x => !x.formula.containsQuantifier).map(x => x.formula.asInstanceOf[FOLFormula]).toList
  
  // Instanciated (previously univ. quantified) formulas on the left
  private val inst_l : List[FOLFormula] = grammar.u.foldRight(List[FOLFormula]()) { case (term, acc) =>
    val terms = flatterms.getTermTuple(term)
    val f = flatterms.getFormula(term)
    f match {
      case AllVar(_, _) => f.instantiateAll(terms) :: acc
      case _ => acc
    }
  }
  // Instanciated (previously ex. quantified) formulas on the right
  private val inst_r : List[FOLFormula] = grammar.u.foldRight(List[FOLFormula]()) { case (term, acc) =>
    val terms = flatterms.getTermTuple(term)
    val f = flatterms.getFormula(term)
    f match {
      case ExVar(_, _) => f.instantiateAll(terms) :: acc
      case _ => acc
    }
  }

  // Separating the formulas that contain or not the eigenvariable
  val antecedent = prop_l ++ inst_l.filter(f => !f.freeVariables.contains(g.eigenvariable))
  val antecedent_alpha = inst_l.filter(f => f.freeVariables.contains(g.eigenvariable))
  val succedent = prop_r ++ inst_r.filter(f => !f.freeVariables.contains(g.eigenvariable))
  val succedent_alpha = inst_r.filter(f => f.freeVariables.contains(g.eigenvariable))

  var cutFormula = if(cf == null) CutIntroduction.computeCanonicalSolution(seq, g) else cf

  override def toString = {

    // For printing Xα -> ^ Xsi
    val X = ConstantStringSymbol("X")
    val alpha = FOLVar(new VariableStringSymbol("α"))
    val xalpha = Atom(X, alpha::Nil)
    // X[s_i] forall i
    val xs = grammar.s.map(t => Atom(X, t::Nil))
    val bigConj = andN(xs)
    // Implication parametrized with second order variable X (is this needed except for printing purposes??)
    val implication : FOLFormula = Imp(xalpha, bigConj)

    val str0 = antecedent_alpha.foldRight("") ( (f, acc) => acc + f + ", ")
    val str1 = antecedent.foldRight("") ( (f, acc) => acc + f + ", ")
    val str2 = succedent_alpha.foldRight("") ( (f, acc) => acc + f + ", ")
    val str3 = succedent.foldRight("") ( (f, acc) => acc + f + ", ")
    val str4 = cutFormula match { case AllVar( x, f ) => "λ " + x + ". " + f }
      
    (str1 + str0 + implication + " :- " + str3 + str2 + " where " + X + " = " + str4)
  }

  /** Checks if the sequent is a tautology using f as the cut formula.
    * 
    * @param sat A SAT-solver that performs the validity check.
    * @param f The formula to be checked. It will be instantiated with the
    *          eigenvariable of the solution's grammar.
    *          For details, see introqcuts.pdf, Chapter 5, Prop. 4, Example 6.
    * @return True iff f still represents a valid solution.
    */
  def isValidWith(sat: MiniSAT, f: FOLFormula) : Boolean = {

    val body = f.instantiate(grammar.eigenvariable)

    val as = grammar.s.foldRight(List[FOLFormula]()) {case (t, acc) =>
      acc :+ f.instantiate(t) 
    }
    val head = andN(as)

    val impl = Imp(body, head)

    val antecedent = this.prop_l ++ this.inst_l :+ impl
    val succedent = this.prop_r ++ this.inst_r

    //isTautology(FSequent(antecedent, succedent))
    trace( "calling SAT-solver" )
    val r = sat.isValid(Imp(andN(antecedent), orN(succedent)))
    trace( "finished call to SAT-solver" )

    r
  }

  def isValidWith(f: FOLFormula) : Boolean = {

    val body = f.instantiate(grammar.eigenvariable)

    val as = grammar.s.foldRight(List[FOLFormula]()) {case (t, acc) =>
      acc :+ f.instantiate(t) 
    }
    val head = andN(as)

    val impl = Imp(body, head)

    val antecedent = this.prop_l ++ this.inst_l :+ impl
    val succedent = this.prop_r ++ this.inst_r

    trace( "calling isTautology" )
    val r = isTautology(FSequent(antecedent, succedent))
    trace( "finished call to isTautology" )

    r
  }

  // The canonical solution computed already has only the quantified formulas 
  // from the end-sequent (propositional part is ignored).
  //
  // returns the list of improved solutions found by the forgetful resolution
  // algorithm.
  private def improveSolution : List[FOLFormula] = {

    // Remove quantifier 
    val (x, f) = cutFormula match {
      case AllVar(x, form) => (x, form)
      case _ => throw new CutIntroException("ERROR: Canonical solution is not quantified.")
    }

    // Transform to conjunctive normal form
    val cnf = f.toCNF

    // Exhaustive search over the resolvents (depth-first search),
    // returns the list of all solutions found.
    var count = 0

    def searchSolution(f: FOLFormula) : List[FOLFormula] =
      f :: CutIntroduction.ForgetfulResolve(f).foldRight(List[FOLFormula]()) ( (r, acc) =>
          if( this.isValidWith( AllVar( x, r ))) {
            trace( "found solution with " + r.numOfAtoms + " atoms: " + r )
            count = count + 1
            searchSolution(r) ::: acc
          }
          else {
            count = count + 1
            acc 
          }
        )

    val res = searchSolution(cnf).map(s => AllVar(x, s))

    debug("IMPROVESOLUTION - # of sets examined: " + count + ". finished.")
    res
  }

  def minimizeSolution = {
    trace( "minimizing solution " + cutFormula )
    val minimalSol = this.improveSolution.sortWith((r1,r2) => r1.numOfAtoms < r2.numOfAtoms).head
    this.cutFormula = minimalSol
  }

  def minimizeSolution2 = {
    trace( "minimizing solution " + cutFormula )
    val minimalSol = this.improveSolution2.sortWith((r1,r2) => r1.numOfAtoms < r2.numOfAtoms).head
    this.cutFormula = minimalSol
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
   private def improveSolution2 : List[FOLFormula] = {
      //Create a SAT-solver for the validity check
      val sat = new MiniSAT()

      // Remove quantifier 
      val (x, form2) = cutFormula match {
        case AllVar(x, form) => (x, form)
        case _ => throw new CutIntroException("ERROR: Canonical solution is not quantified.")
      }

      //0. Convert to a clause set where each clause is a list of positive and negative atoms.
      //1. assign a number to every atom in F.
      val fNumbered = numberAtoms(CNFp(form2.toCNF).map(c => CutIntroduction.toMyFClause(c)).toList)

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
                      resolvedVars + (pair._1,pair._2) , CutIntroduction.forgetfulResolve(currentFormula, pair))
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
        trace("elemfilter: node.appliedPairs:   " + node.appliedPairs)
        trace("            node.remainingPairs: " + node.remainingPairs)
        trace("            node.resolvedVars:   " + node.resolvedVars)
        trace("            node.largerElements: " + node.largerElements)

        val ret = (!node.resolvedVars.contains(elem._1._1) && !node.resolvedVars.contains(elem._1._2))
        trace("            RETURN: " + ret)
        ret
      }

      //node-filter which checks for validity using miniSAT
      def nodeFilter(node: ResNode) : Boolean = {
        satCount = satCount + 1
        isValidWith(sat, AllVar(x, CutIntroduction.NumberedCNFtoFormula(node.currentFormula)))
      }

      //Perform the DFS
      val solutions = DFS[ResNode](rootNode, (setSearch[(Int,Int),ResNode](elemFilter, nodeFilter, _:ResNode)))

      //All-quantify the found solutions.
      debug("IMPROVESOLUTION 2 - # of sets examined: " + satCount + ".finished")
      val ret = solutions.map(n => CutIntroduction.NumberedCNFtoFormula(n.currentFormula)).map(s => AllVar(x, s))
      ret
   }
}
