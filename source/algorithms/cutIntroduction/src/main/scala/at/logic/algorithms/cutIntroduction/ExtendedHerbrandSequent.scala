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
      case AllVar(_, _) => f.substituteAll(terms) :: acc
      case _ => acc
    }
  }
  // Instanciated (previously ex. quantified) formulas on the right
  private val inst_r : List[FOLFormula] = grammar.u.foldRight(List[FOLFormula]()) { case (term, acc) =>
    val terms = flatterms.getTermTuple(term)
    val f = flatterms.getFormula(term)
    f match {
      case ExVar(_, _) => f.substituteAll(terms) :: acc
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

  // Checks if the sequent is a tautology using f as the cut formula
  def isValidWith(f: FOLFormula) : Boolean = {

    val body = f.substitute(grammar.eigenvariable)

    val as = grammar.s.foldRight(List[FOLFormula]()) {case (t, acc) =>
      acc :+ f.substitute(t) 
    }
    val head = andN(as)

    val impl = Imp(body, head)

    val antecedent = this.prop_l ++ this.inst_l :+ impl
    val succedent = this.prop_r ++ this.inst_r

    isTautology(FSequent(antecedent, succedent))
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
    def searchSolution(f: FOLFormula) : List[FOLFormula] =
      f :: CutIntroduction.ForgetfulResolve(f).foldRight(List[FOLFormula]()) ( (r, acc) =>
          if( this.isValidWith( AllVar( x, r ))) {
            trace( "found solution with " + r.numOfAtoms + " atoms: " + r )
            searchSolution(r) ::: acc
          }
          else {
            acc 
          }
        )

    searchSolution(cnf).map(s => AllVar(x, s))
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

  /** Performs a map with an accumulator.
    * Useful for e.g. mapping a custom counter onto a collection.
    *
    * @param f The mapping function. Takes an accumulator and an element from the list and returns a tuple
    *        of the new accumulator value and the mapped list element.
    * @param init The initial accumulator value.
    * @param list The list on which to perform the map.
    * @return The mapped list and the final value of the accumulator.
    */
  def mapAccumL[Acc,X,Y](f:(Acc, X) => (Acc,Y), init:Acc, list:List[X]):(Acc,List[Y]) = list match {
    case Nil => (init, Nil)
    case (x::xs) => {
      val (new_acc, y) = f(init, x)
      val (new_acc2,ys) = mapAccumL(f, new_acc, xs)

      (new_acc2, y::ys)
    }
  }

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

  /** Performs a parameterizable DFS with a custom successor function.
    *
    * It is assumed that all nodes with no successors are goal nodes (true in this special case)
    * and that the successor function generates no invalid nodes.
    *
    * @param root The root node of the search.
    * @param succ The successor function which takes a node and generates all valid successors.
    * @return The list of nodes which have no successors (=goal nodes in this context).
    */
  def DFS[NodeType](root:NodeType, succ:NodeType => List[NodeType]):List[NodeType] = {
    val st = Stack[NodeType]()

    def innerDFS(st:Stack[NodeType]) : List[NodeType] = {
      //no more nodes to expand => search is finished.
      if (st.size == 0) { Nil }
      else {
        val succs = succ(st.top)

        //current node has no successors => add it to the list of solutions.
        if (succs == Nil) { (st.top) :: (innerDFS(st.pop)) }
        //otherwise, keep searching: generate successors & push them all to the search stack.
        else { innerDFS(succs.foldLeft(st.pop)((s, x) => s.push(x))) }
      }
    }

    innerDFS(st.push(root))
  }

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
      val pairs = posNegSets.map((v) => {val (_,(n,p)) = v; cartesianProduct(n.toList,p.toList)}).flatten.zipWithIndex

      //-----------------------------------------------------------------------
      //DFS starts here
      //-----------------------------------------------------------------------

      // 4) let each node of the DFS be (R,V, F'), where R is the set of resolved pairs, V is the set of resolved atoms, and F' the resulting formula.
      class ResNode(appliedPairsc:List[Int], resolvedVarsc:Set[Int], currentFormulac: List[MyFClause[(FOLFormula, Int)]]) {
        var appliedPairs:List[Int] = appliedPairsc
        var resolvedVars:Set[Int] = resolvedVarsc
        var currentFormula: List[MyFClause[(FOLFormula, Int)]] = currentFormulac

        override def toString(): String = ("RESNODE(R: " + appliedPairs.toString + ", V: " + resolvedVars.toString + ", P: " + currentFormula.toString + ")")
      }

      // 4.1) let the root be ({},{},F).
      val rootNode = new ResNode(List[Int](), Set[Int](), fNumbered)

      // 4.2) let the successor function be succ((R,V,F)) = {(R U r,V,F'') | r in (PAIRS - R),
      //                                                                     r intersect V =  {},
      //                                                                     r > max{R}, F'' = r applied to F',
      //                                                                     F'' is still valid}
      //      (if a node has no valid successors, it is considered an end node and added to the list of solutions.)
      def successorFunction(node:ResNode) : List[ResNode] = { 
        //NOTE: instead of pairs.filter, one could store the non-applied pairs in the node to avoid some unnecessary recomputation.
        val candidatePairs = pairs.filter(p => {val (pair,index) = p
                                                //r in (PAIRS - R)
                                                !node.appliedPairs.contains(index) &&
                                                //r > max{R} (the maximum index is always the head of node.appliedPairs).
                                                (node.appliedPairs.length == 0 || index > node.appliedPairs.head) &&
                                                //Pairs may share variables and the same variable cannot be resolved away twice.
                                                !node.resolvedVars.contains(pair._1) &&
                                                !node.resolvedVars.contains(pair._2)})

        //Perform resolution with each of the candidate pairs, creating the successor nodes
        val candidateNodes = candidatePairs.map(p => {
          val (pair,index) = p
          new ResNode(index::node.appliedPairs, node.resolvedVars + (pair._1, pair._2), CutIntroduction.forgetfulResolve(node.currentFormula, pair))})

        //Filter out those nodes which would leave the formula invalid.
        candidateNodes.filter(node => isValidWith(AllVar(x, CutIntroduction.NumberedCNFtoFormula(node.currentFormula)))).toList
      }

      //Perform the DFS
      val solutions = DFS[ResNode](rootNode, successorFunction)

      //All-quantify the found solutions.
      solutions.map(n => CutIntroduction.NumberedCNFtoFormula(n.currentFormula)).map(s => AllVar(x, s))
   }
}