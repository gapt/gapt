package at.logic.algorithms.cutIntroduction

/**
 * Implements the method mentioned in Eberhard, Hetzl [2014]
 * for decomposing trat-n grammars
 */

import at.logic.algorithms.cutIntroduction.MCSMethod.MCSMethod
import at.logic.language.fol._
import at.logic.language.fol.Atom
import at.logic.algorithms.cutIntroduction.Deltas._
import at.logic.language.hol.logicSymbols._
import at.logic.provers.maxsat.MaxSATSolver.MaxSATSolver
import at.logic.utils.dssupport.ListSupport
import at.logic.utils.logging.Stopwatch
import scala.collection.mutable.MutableList
import scala.collection.mutable
import at.logic.provers.maxsat.{MaxSATSolver, MapBasedInterpretation, MaxSAT}
import at.logic.utils.dssupport.ListSupport.{boundedPower, diagCross}
import at.logic.language.fol.Utils.{st, subterms, calcCharPartition, incrementAllVars, nonterminalOccurs, replaceAtPosition, getNonterminals}

/**
 * MinCostSAT Method
 * - QMaxSAT formulation
 * - Simplex formulation
 */
object MCSMethod extends Enumeration {
  type MCSMethod = Value
  val MaxSAT, Simplex = Value
}

class TreeGrammarDecompositionException(msg: String) extends Exception(msg)

object TreeGrammarDecomposition {

  var decomp : TreeGrammarDecomposition = _

  /**
   * Provided a termset/language, an integer n (representing the maximum number of non-terminals) and a method
   * (e.g. MCSMethod.QMaxSAT, MCSMethod.Simplex) the TreeGrammarDecomposition algorithm described in
   * Eberhard, Hetzl [2014] will be executed, resulting in a List of Grammars, which are minimal w.r.t. the
   * number of rules.
   *
   * @param termset language on which the TGD algorithm will operate on
   * @param n maximum number of non-terminals
   * @param method how the MinCostSAT formulation of the problem should be solved (QMaxSAT, Simplex, ...)
   * @return a list of grammars
   */
  def apply(termset: List[FOLTerm], n: Int, method: MCSMethod, satsolver: MaxSATSolver=MaxSATSolver.QMaxSAT) : Grammar = {

    method match {
      case MCSMethod.MaxSAT => {
        // instantiate TreeGrammarDecomposition object with the termset and n
        decomp = new TreeGrammarDecompositionPWM(termset, n)

      }
      case MCSMethod.Simplex => {
        // instantiate TreeGrammarDecomposition object with the termset and n
        //val decomp = new TreeGrammarDecompositionSimplex(termset, n)
        return null
      }
    }

    if(decomp != null) {
      // generating the sufficient set of keys
      val startTimeSuffKeys = System.currentTimeMillis()
      decomp.suffKeys()
      val endTimeSuffKeys = System.currentTimeMillis()
      // Generating the MinCostSAT formulation for QMaxSAT
      val f = decomp.MCS().asInstanceOf[List[FOLFormula]]
      // Generating the soft constraints for QMaxSAT to minimize the amount of rules
      val g = decomp.softConstraints().asInstanceOf[List[Tuple2[FOLFormula,Int]]]
      // Retrieving a model from a MaxSAT solver and extract the rules
      val interpretation = (new MaxSAT(satsolver)).solvePWM(f, g)
      val rules = decomp.getRules(interpretation)
      // transform the rules to a Grammar
      val grammar = decomp.getGrammar(rules)
      return grammar
    }
    else{
      return null
    }
  }


  /**
   * Provided a termset/language, an integer n (representing the maximum number of non-terminals) and a method
   * (e.g. MCSMethod.QMaxSAT, MCSMethod.Simplex) the TreeGrammarDecomposition algorithm described in
   * Eberhard, Hetzl [2014] will be executed, resulting in a List of Grammars, which are minimal w.r.t. the
   * number of rules.
   * Returns additonal statistical information
   *
   * @param termset language on which the TGD algorithm will operate on
   * @param n maximum number of non-terminals
   * @param method how the MinCostSAT formulation of the problem should be solved (QMaxSAT, Simplex, ...)
   * @return (list of grammars, status, log)
   */
  def applyStat(termset: List[FOLTerm], n:Int, method: MCSMethod=MCSMethod.MaxSAT, satsolver: MaxSATSolver=MaxSATSolver.QMaxSAT) : Option[Grammar] = {

    var phase = "TGD"

    var grammar : Option[Grammar] = None

    method match {
      case MCSMethod.MaxSAT => {
        // instantiate TreeGrammarDecomposition object with the termset and n
        decomp = new TreeGrammarDecompositionPWM(termset, n)

      }
      case MCSMethod.Simplex => {
        // instantiate TreeGrammarDecomposition object with the termset and n
        //val decomp = new TreeGrammarDecompositionSimplex(termset, n)
        return null
      }
    }

    if (decomp != null) {

      phase = "suffKeys"

      // generating the sufficient set of keys
      decomp.suffKeys()

      phase = "MCS"

      // Generating the MinCostSAT formulation for QMaxSAT
      val f = decomp.MCS().asInstanceOf[List[FOLFormula]]
      // Generating the soft constraints for QMaxSAT to minimize the amount of rules
      val g = decomp.softConstraints().asInstanceOf[List[Tuple2[FOLFormula, Int]]]

      phase = "CNF/MaxSAT"

      // Retrieving a model from a MaxSAT solver and extract the rules
      val interpretation = (new MaxSAT(satsolver)).solvePWM(f, g)

      phase = "interpret"
      val rules = decomp.getRules(interpretation)

      // transform the rules to a Grammar
      grammar = Some(decomp.getGrammar(rules))
    }
    else {
      throw new TreeGrammarDecompositionException("Unsupported TreeGrammarDecomposition method")
    }
    grammar
  }
}


abstract class TreeGrammarDecomposition(val termset: List[FOLTerm], val n: Int) {

  // Symbols used for non-terminals within the algorithm
  val nonterminal_a = "α"
  val nonterminal_b = "β"

  // mapping all sub-/terms of the language to a unique index
  var termMap : mutable.Map[FOLTerm,Int]
  // reversed map of all sub-/terms
  var reverseTermMap : mutable.Map[Int,FOLTerm]
  // counter for uniquely defined terms indexes
  var termIndex : Int

  // the sufficient set of keys represented as a list
  var keyList : mutable.MutableList[FOLTerm]

  // a Map storing for every key its index in keyList
  var keyIndexMap : mutable.Map[FOLTerm,Int]

  // stores tuples (term,keyset), where keyset is a list of indexes of keys in keyList
  // which produce the particular term
  var keyMap : mutable.Map[FOLTerm,mutable.Set[Int]]

  // mapping keys to a list of terms which can be produced by a particular key
  var decompMap : mutable.Map[FOLTerm,mutable.Set[List[FOLTerm]]]

  // abstract method definitions for individual implementation
  // w.r.t. the method type
  def getRules(interpretation: Option[MapBasedInterpretation]) : Set[Tuple2[Int,FOLTerm]]
  def softConstraints() : Any
  def MCS() : Any
  def R(qindex: Int, qsubtermIndexes: Set[Int]) : FOLFormula
  def printExpression(f: FOLExpression) : String
  def pA(c:FOLFormula) : String
  def D(t: FOLTerm, l: Int, q: FOLTerm): Option[FOLFormula]
  def C(q: FOLTerm) : FOLFormula


  /**
   * Eventually adds a term to the term map and returns its index
   * @param t term which is going to be added to the map, if it does not exist yet
   * @return the index of t in termMap
   */
  def addToTermMap(t: FOLTerm) : Int = {
    // is the term already associated with an index?
    if(!termMap.exists(_._1 == t))
    {
      termMap(t) = termIndex
      termIndex += 1
    }
    termMap(t)
  }

  /**
   * suffKeys - as described in Eberhard [2014] -
   * generates a sufficient set of keys w.r.t. a termset/language l
   */
  def suffKeys() {

    //var result = scala.collection.mutable.Set[FOLTerm]()
    val st = subterms(termset)
    // since we only need to construct terms with n nonterminals, we only have to consider
    // subsets of st(L') with a size of at most n+1
    val poweredSubSets = boundedPower(st.toList, n+1)

    // for each subset of size 1 <= |sub| <= n+1,
    // add all keys of normform(sub) to keySet
    poweredSubSets.foreach( sub => {
      val keys = normform(sub)
      // the indexes of the keys in normalform in the keyList
      val keyIndexes = keys.foldLeft(List[Int]())((acc,k) => addKey(k) :: acc)

      // for every term t
      // save the corresponding keyIndexes of the keys
      // which produce this particular term
      sub.foreach(t => {
        // if the key does not already exist
        if(!keyMap.exists(_._1 == t)){
          // add it
          keyMap(t) = mutable.Set(keyIndexes :_*)
        }
        else{
          keyMap(t) ++= keyIndexes
        }
      })
    })
  }

  /**
   * Adds a key k to the keyList and the keyIndexMap
   *
   * @param k key
   * @return index of the key in keyList
   */
  def addKey(k : FOLTerm) : Int = {
    // if the key does not already exist
    // in the keyIndexMap
    if(!keyIndexMap.exists(_._1 == k)){
      // add it to keyList and keyIndexMap
      keyList += k
      keyIndexMap(k) = keyList.size - 1
    }
    return keyIndexMap(k)
  }





  /**
   * normform produces, depending on a language l
   * a set of keys in normalform.
   *
   * @param l termset (language)
   * @return key in normal form of l
   */
  def normform(l: List[FOLTerm]) : List[FOLTerm] = {

    val result = MutableList[FOLTerm]()

    // initialize delta vector
    var delta = new UnboundedVariableDelta()

    val decomps = delta.computeDelta(l, nonterminal_b)

    // retrieve the key, since computeDelta returns a decomposition T = U o S
    var decomposition = decomps.toList(0)

    // add the decomposition to the key map
    // TODO: eventually check if the nonterminals in k are ambigous
    val k = incrementAllVars(decomposition._1,nonterminal_b)
    // calculate the characteristic partition
    var charPartition = calcCharPartition(k)

    // generate all substitutions (subs) which are later on applied to restfragments
    // to generate real rests out of them
    val nonterminals = getNonterminals(k, nonterminal_b).distinct.sorted
    val evs = nonterminals.map(x => FOLVar(x))
    val subs = decomposition._2.map(x => Substitution(evs.zip(x)))

    // get all subsets of charPartitions of size at most n
    // and permute them
    var permutedCharPartition = boundedPower(charPartition,n).map(_.permutations.toList).flatten

      // for each ordered list of position sets
      permutedCharPartition.foreach(partition => {
        // new_key as in Eberhard [2014]
        var new_key = k
        // for every position in the set
        // try to replace the term on that position by a non-terminal
        val allrests = mutable.Map[Int, FOLExpression]()
        for (i <- List.range(0, partition.size)) {
          // backup new_key since we want to know at the end if we were able
          // to substitute anything
          var old_key = new_key
          // get the current positions, we want to substitute
          val positionSet = partition(i)
          // since the rest fragments of all positions are the same, we can take an arbitrary one
          val r = at.logic.language.fol.replacements.getAtPositionFOL(k, positionSet(0))
          // do the substitutions at the corresponding positions
          new_key = positionSet.foldLeft(new_key)((acc, pos) => replaceAtPosition(acc, nonterminal_a, pos, i+1))
          // if we were able to substitute anything
          if (old_key != new_key) {
            // if the positions exist and we could successfully substitute all of them,
            // we add the rest fragment to the map
            allrests(i + 1) = r
          }
        }
        // if new_key does not contain the previously introduced non-terminals nonterminal_b
        // i.e. only non-terminals nonterminal_a occur
        // add the key to the outputset
        if (!nonterminalOccurs(new_key, nonterminal_b)) {

          // be sure to calculate the real rests, i.e. rests from gdv, substituted with the restfragments between α_i and β_i
          // sort allrests and get rid of non-terminals (with their resp. rests),
          // which got replaced by other non-terminals throughout the procedure

          // for this start with a list of non-terminal indexes occuring in new_key
          val ntsNewKey = getNonterminals(new_key, nonterminal_a).map(v => v.split("_").last.toInt)
          // filter out all rests, where the corresponding non-terminal is not present in new_key
          // anymore
          val prefinalrests = allrests.toList.filter(ir => ntsNewKey.contains(ir._1)).unzip._2
          // now apply the corresponding substitution to make
          // those restfragments to real rests
          val finalrests = subs.map(sub => prefinalrests.map(pfr => sub(pfr).asInstanceOf[FOLTerm]))

          // add the key to the resultset
          result += new_key

          // add the keys real rests to the decompMap
          if (decompMap.exists(_._1 == new_key)) {
            decompMap(new_key) ++= finalrests
          }
          else {
            decompMap(new_key) = mutable.Set(finalrests.toSeq: _*)
          }
        }
      })
    return result.toList
  }


  /**
   * Provided a set of rules of a grammar, the function converts them into
   * a List of Grammars.
   * e.g.
   *  (1,f(α_2)), (2,g(α_3)), (3,h(0)) =>
   *    [ ({α_1} o {f(α_2)}),
   *      ({f(α_2)} o {f(g(α_3))}),
   *      ({f(g(α_3))} o {f(g(h(0)))})
   *    ]
   *
   * @param rules a set of of tuples of the form {(<non-terminal-index>, <FOLTerm>}
   * @return grammars representing provided rules
   */
  def getGrammar(rules: Set[Tuple2[Int,FOLTerm]]) : Grammar = {
    
    val slist = mutable.MutableList[(List[FOLVar],Set[List[FOLTerm]])]()

    // get all nonterminals in rules
    val evs = rules.foldLeft(List[String]())( (acc,r) => getNonterminals(r._2, nonterminal_a+"_") ::: acc).distinct.sorted

    // don't forget to add the α_0
    // to the list of all nonterminal indexes
    val indexes = 0 :: evs.map( x => x.split("_").last.toInt)

    // divide the rules by the nonterminal index
    val decomps = indexes.foldLeft(List[(Int,Set[List[FOLTerm]])]())((acc,i) => (i,rules.filter(_._1 == i).map( x => List(x._2)).toSet) :: acc).toMap
    var u = decomps(0).flatten.toList

    for(i <- indexes){
      if(i != 0) {
        val s = decomps(i)
        val quantifiedVars = List(FOLVar(nonterminal_a+"_"+i))
        slist += Tuple2(quantifiedVars,s)

        // TODO: (X) this part denoted the substitutions which have to be 
	// performed on U for each rule \alpha_i => S_i. This should possibly 
	// be part of computeCanonicalSolutions
        /*val subs = s.foldLeft(List[Substitution]())((acc2,s0) => {
          Substitution(s0.map( s1 => (FOLVar(nonterminal_a+"_"+ i), s1))) :: acc2
        })

        u = u.foldLeft(List[FOLTerm]())((acc, u0) => subs.map(sub => sub(u0)) ::: acc)*/
      }
    }
    return new Grammar(u, slist.toList)
  }

  /**
   * Checks if a rest r is a rest w.r.t. a key k in a term t
   * i.e. t = k[\alpha_1 \ r(0)]...[\alpha_{n+1} \ r(n)]
   *
   * @param t term
   * @param k key
   * @param r rest
   * @return true if t = {k} o {r}
   */
  def isRest(t: FOLTerm, k: FOLTerm, r: List[FOLTerm]) : Boolean = {
    val evs = getNonterminals(k, nonterminal_a).sorted.map(x => FOLVar(x))
    val sub = Substitution(evs.zip(r))
    return t == sub(k)
  }


}

class TreeGrammarDecompositionPWM(override val termset: List[FOLTerm], override val n: Int) extends TreeGrammarDecomposition(termset, n) {

  // mapping all sub-/terms of the language to a unique index
  var termMap : mutable.Map[FOLTerm,Int] = mutable.Map[FOLTerm,Int]()
  // reversed map of all sub-/terms
  var reverseTermMap : mutable.Map[Int,FOLTerm] = mutable.Map[Int,FOLTerm]()
  // counter for uniquely defined terms indexes
  var termIndex = 0

  // the sufficient set of keys represented as a list
  var keyList : mutable.MutableList[FOLTerm] = mutable.MutableList[FOLTerm]()

  // a Map storing for every key its index in keyList
  var keyIndexMap : mutable.Map[FOLTerm,Int] = mutable.Map[FOLTerm,Int]()

  // stores tuples (term,keyset), where keyset is a list of indexes of keys in keyList
  // which produce the particular term
  var keyMap : mutable.Map[FOLTerm,mutable.Set[Int]] = mutable.Map[FOLTerm,mutable.Set[Int]]()

  // mapping keys to a list of terms which can be produced by a particular key
  var decompMap : mutable.Map[FOLTerm,mutable.Set[List[FOLTerm]]] = mutable.Map[FOLTerm,mutable.Set[List[FOLTerm]]]()


  // all constants of the form x_{i,k_j}, where
  // i = non-terminal index, k_j = key
  var propRules : mutable.Map[FOLFormula,(Int,Int)] = mutable.Map[FOLFormula,(Int,Int)]()

  // all constants of the form x_{t,i,q}, where
  // t = subterm of q, i = non-terminal index, q = term of the language (termset)
  var propRests : mutable.Map[FOLFormula,(Int,Int,Int)] = mutable.Map[FOLFormula,(Int,Int,Int)]()


  /**
   * Given an interpretation, a Set of tuples will be returned of the form
   * (non-terminal-index,folterm), which represent a rule of the form
   * α_i -> term (containing at most non-terminals α_j where j > i)
   *
   * @param interpretation a MapBasedInterpretation of the MCS formulation
   * @return a set of rules
   */
  def getRules(interpretation: Option[MapBasedInterpretation]) : Set[Tuple2[Int,FOLTerm]] = {
    interpretation match {
      case Some(model) => {
        propRules.foldLeft(Set[Tuple2[Int, FOLTerm]]())((acc, x) => {
          // if x_{i,k} is true
          // generate the rule α_i -> k
          if (model.interpretAtom(x._1)) {
            acc + Tuple2(x._2._1, keyList(x._2._2))
          }
          else {
            acc
          }
        })
      }
      case None => Set.empty
    }
  }


  /**
   * Generates the soft constraints for
   * the MCS formulation as a partial weighted MaxSAT problem,
   * where \neg x_{i,k} has cost 1 for all non-terminals α_i and keys k
   *
   * @return G formula for QMaxSAT
   */

  override def softConstraints() : List[Tuple2[FOLFormula,Int]] = {
    propRules.foldLeft(List[Tuple2[FOLFormula,Int]]())((acc,x) => acc :+ Tuple2(Neg(x._1),1))
  }


  /**
   * Transforms a sufficient set of keys into a propositional
   * formula as described in Eberhard [2014].
   *
   * @return MinCostSAT formulation of the problem for applying it to the QMaxSAT solver
   */
  override def MCS() : List[FOLFormula] = {
    val f = termset.foldLeft(List[FOLFormula]())((acc,q) => C(q) :: acc).distinct
    // update the reverse term map
    reverseTermMap = mutable.Map(termMap.toList.map(x => x.swap).toSeq:_*)
   return f
  }

  /**
   * Generates the formula R mentioned in Eberhard [2014]
   *
   * @param qindex index of term in termset (language)
   * @param qsubtermIndexes indexes of all subterms of q in termMap
   * @return R formula
   */
  def R(qindex: Int, qsubtermIndexes: Set[Int]) : FOLFormula = {
    // for all pairs t_0,t_1 \in st({q}), s.t. t_0 != t_1
    // since we don't need to generate all pairs, due to commutativity of \lor
    // we need only the cartesian product of qsubtermindexes, without the diagonal
    val pairs = diagCross(qsubtermIndexes.toList)
    // generate the formula \neg x_{t_0,i,q} \lor \neg x_{t_1,i,q}
    And(pairs.foldLeft(List[FOLFormula]())((acc1,t) => {
      Range(1,n+1).foldLeft(List[FOLFormula]())((acc2,i) => {
        val co1 = Atom(t._1 + "_" + i + "_" + qindex, Nil)
        val co2 = Atom(t._2 + "_" + i + "_" + qindex, Nil)
        propRests(co1) = (t._1, i, qindex)
        propRests(co2) = (t._2, i, qindex)
        List(Or(Neg(co1), Neg(co2))) ++ acc2
        }) ++ acc1
    }))
  }


  /**
   * For debugging purpose.
   * This function is helpful for providing the MinCostSAT formula in a
   * human readable way.
   * In order to call it one may have to call suffKeys, MCS and softConstraints first.
   * @param e a FOLExpression
   * @return a latex string of the particular expression
   */
    def PrettyPrinter(e:FOLExpression) : String = {

      val p = pretty(e)

      val r : String = e match {
        case Function(x, args) => {
          //if(p._1 != p._2 && p._2 != "tuple1")
            if(p._3 > 1)
              return p._2 + "^{"+(p._3)+"}("+p._1+") "
            else if(p._3 == 1)
              return p._2+"("+p._1+") "
            else
              return p._1
          //else
          //  return p._1
        }
        case _ => return p._1
      }

      return r
    }

  /**
   * For debugging purpose.
   * Helps to abbreviate certain monadic function symbols
   * @param exp a FOLExpression
   * @return a triple to distinguish between monadic and other function calls
   */
    private def pretty(exp : FOLExpression) : (String, String, Int) = {

      val s : (String, String, Int) = exp match {
        case null => ("null", "null", -2)
        case FOLVar(x) => (x.toString(), x.toString(), 0)
        case atom@Atom(x,args) if args.isEmpty => (pA(atom.asInstanceOf[FOLFormula]), x.toString, 0)//(PrettyPrinter(args(0)),PrettyPrinter(args(0)),0)
        case Atom(x, args) => (x.toString() + "("+ListSupport.lst2string(PrettyPrinter, ", ", args)+")", x.toString(), 0)
        case Function(x, args) => {
          // if only 1 argument is provided
          // check if abbreviating of recursive function calls is possible
          if(args.size == 1)
          {
            val p = pretty(args.head)

            // current function is equal to first and ONLY argument
            if( p._2 == x.toString() )
            {
              // increment counter and return (<current-string>, <functionsymbol>, <counter>)
              return (p._1, x.toString(), p._3+1)
            }
            // function symbol has changed from next to this level
            else
            {

              // in case of multiple recursive function calls
              if(p._3 > 1)
              {
                  return (p._2+"^{"+p._3+"}("+p._1+")", x.toString(), 1)
              }
              else if(p._3 == 1)
              {
                return (p._2+"("+p._1+")", x.toString(), 1)
              }
              // otherwise
              else
              {
                return (p._1, x.toString(), 1)
              }
            }
          }
          else
          {
            return (x.toString()+"("+ ListSupport.lst2string(PrettyPrinter, ",", args)+")", x.toString(), 0)
          }

        }
        case And(x,y) => (PrettyPrinter(x) + " \\land " + PrettyPrinter(y), AndSymbol.toString(), 0)
        case Equation(x,y) => (PrettyPrinter(x) + " " + EqSymbol + " " + PrettyPrinter(y), EqSymbol.toString(), 0)
        case Or(x,y) => (PrettyPrinter(x) + " \\lor " + PrettyPrinter(y), OrSymbol.toString(), 0)
        case Imp(x,y) => ("("+PrettyPrinter(x) + " \\to " + "("+PrettyPrinter(y)+"))", ImpSymbol.toString(), 0)
        case Neg(x) => ("\\neg "+PrettyPrinter(x), NegSymbol.toString(), 0)
        case ExVar(x,f) => ("\\exists " + PrettyPrinter(x) + "." + PrettyPrinter(f), ExistsSymbol.toString(), 0)
        case AllVar(x,f) => ("\\forall " + PrettyPrinter(x) + "." + PrettyPrinter(f), ForallSymbol.toString(), 0)
        //case FOLAbs(v, exp) => ("(\\lambda " + PrettyPrinter(v) + "." + PrettyPrinter(exp), "λ", 0)
        //case FOLApp(l,r) => ("(" + PrettyPrinter(l) + ")(" + PrettyPrinter(r)+ ")", "()()", 0)
        case FOLConst(x) => (x.toString, x.toString, 0) //(pA(FOLConst(x)),pA(FOLConst(x)), 0)
        case _ => throw new Exception("ERROR: Unknown FOL expression.");
      }
      return s

    }

  /**
   * Returns for a given formula f (of a QMaxSAT instance) its latex code
   * (for debugging purposes)
   *
   * @param exp FOLExpression
   * @return latex representation of f
   */
  def printExpression(exp: FOLExpression) : String = {
    exp match {
      case And(a,b) => printExpression(a) + " \\land " + printExpression(b)
      case Or(a,b) => printExpression(a) + " \\lor " + printExpression(b)
      case Neg(e) => "\\neg " + printExpression(e)
      case Imp(a,b) => printExpression(a) + " \\to " + printExpression(b)
      case FOLVar(x) => x.toString
      case FOLConst(x) => x.toString //pA(FOLConst(x))
      case Function(f,l) => f+"("+ListSupport.lst2string(printExpression, ",", l)+")"
      //case Atom(a,l) => a+"("+l.foldLeft("")((acc:String,x:FOLExpression) => printExpression(x) + ", " + acc ).dropRight(2)+")"
      case atom@Atom(a,l) => pA(atom.asInstanceOf[FOLFormula])//l.foldLeft("")((acc:String,x:FOLExpression) => printExpression(x) + ", " + acc ).dropRight(2)
    }
  }

  /**
   * A method which returns a latex representation of an Atom according
   * to the propositional MaxSAT formulation
   *
   * @param atom an Atom
   * @return latex representation of atom
   */
  def pA(atom:FOLFormula) : String = atom match {
      case a@Atom(aSymbol,args) => {
        val astr = aSymbol.toString
        val s = astr.split("_")
        if (astr(0).isDigit && s.size == 2) {
          return "x_{\\alpha_{" + s(0) + "}," + PrettyPrinter(keyList(s(1).toInt)) + "}"
        } else if (astr(0).isDigit && s.size == 3) {
          return "x_{" + PrettyPrinter(reverseTermMap(s(0).toInt)) + ",\\alpha_{" + s(1) + "}," + PrettyPrinter(reverseTermMap(s(2).toInt)) + "}"
        }
        else {
          return astr.toString+"("+args.map(arg => PrettyPrinter(arg))+")"
        }
      }
    }

  /**
   * Generates the formula D_{L,S}(t,i,q) according to
   * Eberhard [2014]
   *
   * @param t subterm of q
   * @param l index of non-terminal
   * @param q a term of the termset (language)
   * @return some QMaxSAT formulation D_{L,S}(t,j,q) or None if its empty
   */
  def D(t: FOLTerm, l: Int, q: FOLTerm): Option[FOLFormula] = {

      val qindex = addToTermMap(q)

      // for every key k_j producing t, which
      // ONLY CONTAINS α_i, where i > l
      val disjunctionList = keyMap(t).foldLeft(List[FOLFormula]())((acc1,klistindex) => {
        // add the propositional variable x_{k_j}
        // and create the corresponding propositional variable for this rule
        val ruleVar = Atom(l+"_"+klistindex, Nil)
        propRules(ruleVar) = (l,klistindex)

        // get the key we are currently observing
        val k = keyList(klistindex)

        // get all nonterminals occuring in the subterm t
        // and sort them
        val evs = getNonterminals(k,nonterminal_a).distinct.sorted
        // get their respective indexes
        val evIndexes = evs.map(x => x.split("_").last.toInt).sorted
        // check if all nonterminals α_i suffice i > l
        if(evIndexes.forall(evi => evi > l )){

            // for every possible restvector of this rule add a new conjunction with their rests respectively
            val conjunctionList = ruleVar :: decompMap(k).foldLeft(List[FOLFormula]())((acc2,d) => {

            // if the restset d represents rests of k regarding t
            // add all of the rests to the formula
            val rests = isRest(t, k, d) match {
              case true => {
                // create tuples of non-terminal indexes with resp. rests
                // (i, r_i)
                val restTuples = evIndexes.zip(d)

                // for every element r_j in the decomposition's sublanguage S where kj is its U
                restTuples.foldLeft(List[FOLFormula]())((acc3,rt) => {
                    val evindex = rt._1
                    val rindex = addToTermMap(rt._2)
                    val restvar = Atom(rindex + "_" + evindex + "_" + qindex, Nil)
                    // create rest if it does not already exist
                    propRests(restvar) = (rindex,evindex,qindex)
                    // take the rest of the particular nonterminal
                    restvar :: acc3
                })
              }
              case false => List[FOLFormula]()
            }
            rests ::: acc2
          })
          // if not a single valid rest had been found for a non-trivial key, don't
          // add the rule
          if(conjunctionList.size == 1 && evIndexes.size > 0)
          {
            acc1
          }
          else {
            // connect them through a conjunction and add them to the
            // list of disjunctions
            And(conjunctionList) :: acc1
          }
        }
        else{
          acc1
        }
    })
    // if there was at least one fitting rest
    if(disjunctionList.size > 0){
      // connect the list through disjunction and return it
      Some(Or(disjunctionList))
    }
    // if there was no single fitting rest, i.e. we can not apply
    // a nested rule, just return None and later on the trivial key will be added
    else{
      None
    }
  }


  /**
   * Generates out of a term q the formula
   * C_{L,S}(q) as written in Eberhard [2014]
   *
   * @param q term q of the termset (language)
   * @return QMaxSAT formulation C_{L,S}(q)
   */
  def C(q: FOLTerm) : FOLFormula = {

    val subterms = st(q)
    // save the index of the term for later
    val qindex = addToTermMap(q)
    var qsubtermIndexes = mutable.Set[Int]()
    // for each subterm generate the formula according to Eberhard [2014]
    val formulas: List[FOLFormula] = subterms.foldLeft(List[FOLFormula]())((acc1,t) => {
      // save the index of the subterm for later
      val tindex = addToTermMap(t)
      qsubtermIndexes += tindex

      // For t \in st({q})
      // 1 <= i <= n
      Range(1,n+1).foldLeft(List[FOLFormula]())((acc2,i) => {
        val co = Atom(tindex+"_"+i+"_"+qindex, Nil)
        propRests(co) = (tindex,i,qindex)

        val trivialKeyIndex = addKey(t)
        val trivialKeyRule = Atom(i+"_"+trivialKeyIndex, Nil)

        propRules(trivialKeyRule) = (i,trivialKeyIndex)
        // add the trivial keys to the rhs of the implication
        var d = D(t,i,q)
        // Or(Nil) => if D(...) is empty
        val d2 = d match {
          case Some(disjunction) => Or(trivialKeyRule, disjunction)
          case None => trivialKeyRule
        }
        Imp(co, d2) :: acc2
      })::: acc1
    })
    val r = R(qindex,qsubtermIndexes.toSet)
    val d = D(q,0,q)
    // don't forget to add the possibility to the disjunctions
    // that \alpha_0 => trivialkey
    val trivialKeyIndex = addKey(q)
    val trivialKeyRule = Atom(0+"_"+trivialKeyIndex, Nil)
    propRules(trivialKeyRule) = (0, trivialKeyIndex)
    val d2 = d match {
      case Some(disjunction) => Or(trivialKeyRule ,disjunction)
      case None => trivialKeyRule
    }
    And(formulas ++ List(d2, r))
  }

}
