package at.logic.algorithms.cutIntroduction

/**
 * Created by spoerk on 7/1/14.
 */

import at.logic.language.fol._
import at.logic.calculi.expansionTrees.{quantRulesNumber => quantRulesNumberET}
import at.logic.algorithms.cutIntroduction.Deltas._
import scala.collection.mutable.HashMap
import scala.collection.mutable.MutableList
import scala.collection.mutable
import at.logic.language.fol.replacements.getAllPositionsFOL
import at.logic.language.fol.replacements.getAtPositionFOL
import at.logic.provers.qmaxsat.{MapBasedInterpretation, QMaxSAT}
import scala.Some
import scala.Tuple2
import scala.Some
import scala.Tuple2


object TreeGrammarDecomposition{
  def apply(termset: List[FOLTerm], n:Int) = {
    val decomp = new TreeGrammarDecomposition(termset,n)
    decomp.suffKeys()
    debug("Generating MinCostSAT formulation")
    //val f = Set(decomp.MCS())//, decomp.additionalFormula())
    val f = decomp.MCS()
    val g = decomp.softConstraints()
    println("G: \n"+g)
    debug("Starting up QMaxSAT Solver")
    println(decomp.getRules((new QMaxSAT).solvePWM(f.toSet,g)))
  }
}


class TreeGrammarDecomposition(termset: List[FOLTerm], n: Int) extends at.logic.utils.logging.Logger {

  // mapping all sub-/terms of the language to a unique index
  var termMap : mutable.HashMap[FOLTerm,Int] = mutable.HashMap[FOLTerm,Int]()
  // reversed map of all sub-/terms
  var reverseTermMap : mutable.HashMap[Int,FOLTerm] = mutable.HashMap[Int,FOLTerm]()
  // counter for uniquely defined terms indexes
  var termIndex = 0

  // the sufficient set of keys represented as a list
  var keyList : mutable.MutableList[FOLTerm] = mutable.MutableList[FOLTerm]()

  // a hashmap storing for every key its index in keyList
  var keyIndexMap : mutable.HashMap[FOLTerm,Int] = mutable.HashMap[FOLTerm,Int]()

  // stores tuples (term,keyset), where keyset is a list of indexes of keys in keyList
  // which produce the particular term
  var keyMap : mutable.HashMap[FOLTerm,mutable.Set[Int]] = mutable.HashMap[FOLTerm,mutable.Set[Int]]()

  // all constants of the form x_{i,k_j}, where
  // i = non-terminal index, k_j = key
  var propRules : mutable.HashMap[FOLConst,(Int,Int)] = mutable.HashMap[FOLConst,(Int,Int)]()

  // all constants of the form x_{t,i,q}, where
  // t = subterm of q, i = non-terminal index, q = term of the language (termset)
  var propRests : mutable.HashMap[FOLConst,(Int,Int,Int)] = mutable.HashMap[FOLConst,(Int,Int,Int)]()

  // mapping keys to a list of terms which can be produced by a particular key
  var decompMap : mutable.HashMap[FOLTerm,Set[List[FOLTerm]]] = mutable.HashMap[FOLTerm,Set[List[FOLTerm]]]()

  /**
   * Generates the soft constraints for
   * the MCS formulation as a partial weighted MaxSAT problem,
   * where -x_{i,k} has cost 1 for all non-terminals α_i and keys k
   *
   * @return G formula for QMaxSAT
   */
  def softConstraints() : Set[Tuple2[FOLFormula,Int]] = {
    propRules.foldLeft(Set[Tuple2[FOLFormula,Int]]())((acc,x) => acc + Tuple2(Neg(Atom("X",List(x._1))),1))
  }


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
          if (model.interpretAtom(Atom("X", List(x._1)))) {
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
   * Checks if a rest r is a rest w.r.t. a key k in a term t
   * i.e. t = k[\alpha_1 \ r(0)]...[\alpha_{n+1} \ r(n)]
   *
   * @param t term
   * @param k key
   * @param r rest
   * @return true if t = {k} o {r}
   */
  def isRest(t: FOLTerm, k: FOLTerm, r: List[FOLTerm]) : Boolean = {
    val evs = for (x <- List.range(1, 1+r.size)) yield FOLVar("α_"+x)
    val sub = Substitution(evs.zip(r))
    return t == sub(k)
  }

  /**
   * Generates out of a list l
   * the diagonal cartesian product l² of it
   * minus the diagonal and mirrorcases
   *
   * @param l list of elements
   * @return diagonal cartesian product of l
   */
  def diagCross(l:List[Int]) : List[(Int,Int)] = {
    l match {
      case x::xs => xs.map(y => (x,y)) ++ diagCross(xs)
      case _ => Nil
    }
  }

  /**
   * Transforms a sufficient set of keys into a propositional
   * formula as described in Eberhard [2014].
   *
   * @return
   */
  def MCS() : List[FOLFormula] = {
    //And(termset.foldLeft(List[FOLFormula]())((acc,q) => C(q) :: acc))
    val f = termset.foldLeft(List[FOLFormula]())((acc,q) => C(q) ::: acc)
    // update the reverse term map
    reverseTermMap = mutable.HashMap(termMap.toList.map(x => x.swap).toSeq:_*)
    debug("F: "+f.foldLeft("")((acc,x) => acc + "\\\\ \n"+printExpression(x).replaceAllLiterally("α", "\\alpha")))
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
        val co1 = FOLConst(t._1 + "_" + i + "_" + qindex)
        val co2 = FOLConst(t._2 + "_" + i + "_" + qindex)
        propRests(co1) = (t._1, i, qindex)
        propRests(co2) = (t._2, i, qindex)
        List(Or(Neg(Atom("X", List(co1))), Neg(Atom("X", List(co2))))) ++ acc2
        }) ++ acc1
    }))
  }
  /**
   * Given a FOLTerm and a prefix for a variable,
   * this function returns a list of all FOLVars in t starting
   * with the particular prefix
   *
   * @param t FOLTerm
   * @param nonterminal_prefix prefix of non-terminals
   * @return a list of strings representing all non-terminals in t
   */
  def getNonterminals(t: FOLTerm, nonterminal_prefix: String) : List[String] = {
    val s = t match {
      case Function(f,args) => args.foldLeft(Set[String]())((prevargs,arg) => prevargs ++ getNonterminals(arg, nonterminal_prefix))
      case FOLVar(v) => if(v.toString.startsWith(nonterminal_prefix)) Set[String](v.toString()) else Set[String]()
      case _ => Set[String]()
    }
    s.toList

  }


  /**
   * Returns for a given formula f (of a QMaxSAT instance) its latex code
   * (for debugging purposes)
   *
   * @param f FOLExpression
   * @return latex representation of f
   */
  def printExpression(f: FOLExpression) : String = {
    f match {
      case And(a,b) => printExpression(a) + " \\land " + printExpression(b)
      case Or(a,b) => printExpression(a) + " \\lor " + printExpression(b)
      case Neg(e) => "\\neg " + printExpression(e)
      case Imp(a,b) => printExpression(a) + " \\to " + printExpression(b)
      case FOLVar(x) => x.toString
      case FOLConst(x) => pA(FOLConst(x))
      case Function(f,l) => f+"("+l.foldLeft("")((acc:String,x:FOLExpression) => printExpression(x) + ", " + acc ).dropRight(2)+")"
      //case Atom(a,l) => a+"("+l.foldLeft("")((acc:String,x:FOLExpression) => printExpression(x) + ", " + acc ).dropRight(2)+")"
      case Atom(a,l) => l.foldLeft("")((acc:String,x:FOLExpression) => printExpression(x) + ", " + acc ).dropRight(2)
    }
  }

  /**
   * A method which returns a latex representation of a FOLConst according
   * to the propositional QMaxSAT formulation
   *
   * @param c a FOLConst
   * @return latex representation of c
   */
  def pA(c:FOLConst) : String = {
    val s = c.toString.split("_")
    if(s.size == 2)
    {
      return "x_{\\alpha_{"+s(0)+"},"+keyList(s(1).toInt)+"}"
    }else{
      return "x_{"+reverseTermMap(s(0).toInt)+",\\alpha_{"+s(1)+"},"+reverseTermMap(s(2).toInt)+"}"
    }
  }

  /**
   * Generates the formula D_{L,S}(t,i,q) according to
   * Eberhard [2014]
   *
   * @param t subterm of q
   * @param l index of non-terminal
   * @param q a term of the termset (language)
   * @return QMaxSAT formulation D_{L,S}(t,j,q)
   */
  def D(t: FOLTerm, l: Int, q: FOLTerm): FOLFormula = {

      // for every key k_j producing t, which
      // ONLY CONTAINS α_i, where i > l
      Or(keyMap(t).foldLeft(List[FOLFormula]())((acc1,klistindex) => {
        // add the propositional variable x_{k_j}
        val x_l_kj = FOLConst(l+"_"+klistindex)
        propRules(x_l_kj) = (l,klistindex)

        val ruleVar : FOLFormula = Atom("X",List(x_l_kj))

        // get all nonterminals occuring in the subterm t
        val evs = getNonterminals(keyList(klistindex),"α")//.map(x => FOLVar(x))
        // check if all nonterminals α_i suffice i > l
        if(evs.foldLeft(true)((acc,x) => acc && (x.split("_").last.toInt > l ))){
          //debug("NOT skipping key='"+keyList(klistindex)+"' for l="+l)
          // for every nonterminal in k_j
          And(ruleVar :: evs.foldLeft(List[FOLFormula]())((acc2,ev) => {
            // get the nonterminals index i
            val evindex = ev.split("_").last.toInt
            // TODO: Note: x = 0 is used due to the fact that we don't consider blocks of quantifiers
            val x = 0
            // and for every element r_j in the decomposition's sublanguage S where kj is its U
            val k = keyList(klistindex)
            decompMap(k).foldLeft(List[FOLFormula]())((acc3,d) => {

              // if d is a rest of k regarding t
              // add it to the formula
              if(isRest(t, k, d)) {
                val rindex = addToTermMap(d(x))
                val qindex = addToTermMap(q)
                // take the rest of the particular nonterminal
                Atom("X", List(FOLConst(rindex + "_" + evindex + "_" + qindex))) :: acc3
              }else{
                // otherwise don't
                acc3
              }
            }) ::: acc2
          })) :: acc1
        }
        else{
          acc1
        }
    }))
  }


  /**
   * Generates out of a term q the formula
   * C_{L,S}(q) as written in Eberhard [2014]
   *
   * @param q term q of the termset (language)
   * @return QMaxSAT formulation C_{L,S}(q)
   */
  def C(q: FOLTerm) : List[FOLFormula] = {

    debug("GENERATING C(q), where q = '"+q+"'")
    val subterms = st(q)
    // save the index of the term for later
    val qindex = addToTermMap(q)
    var qsubtermIndexes = mutable.Set[Int]()
    val formulas: List[FOLFormula] = subterms.foldLeft(List[FOLFormula]())((acc1,t) => {
      // save the index of the subterm for later
      val tindex = addToTermMap(t)
      debug("Term "+t+" has index "+tindex)
      qsubtermIndexes += tindex

      // For t \in st({q})
      // 1 <= i <= n
      Range(1,n+1).foldLeft(List[FOLFormula]())((acc2,i) => {
        val co = FOLConst(tindex+"_"+i+"_"+qindex)
        propRests(co) = (tindex,i,qindex)

        val trivialKeyIndex = addKey(t)
        val trivialKey = FOLConst(i+"_"+trivialKeyIndex)

        propRules(trivialKey) = (i,trivialKeyIndex)
        // add the trvial keys to the rhs of the implication
        var d = D(t,i,q)
        // Or(Nil) => if D(...) is empty
        if(d == Or(Nil))
        {
          d = Atom("X", trivialKey :: Nil)
        }
        else{
          d = Or(d, Atom("X", trivialKey :: Nil))
        }

        //debug("D("+tindex+","+i+","+qindex+") = D("+t+","+i+","+q+") = "+d)
        Imp(Atom("X",co :: Nil), d) :: acc2
      }) ::: acc1
    })
    val r = R(qindex,qsubtermIndexes.toSet)
    val d = D(q,0,q)
    debug("formulas = "+formulas)
    debug("D("+q+",0,"+q+") = "+d)
    debug("R("+qindex+","+qsubtermIndexes.toSet+") = "+r)
    //And(
    formulas ++ List(d, r)//)
  }


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
   * A method for traversing a term to return a list of all subterms
   *
   * @param subterms subterms so far
   * @param term term, which is processed
   * @return a HasMap of all subterms represented as string => subterm
   */
  def st_trav(subterms:  HashMap[String, FOLTerm], term: FOLTerm) :  HashMap[String, FOLTerm] = {
    // if the term is not in the set of subterms yet
    // add it and add all its subterms
    if(!subterms.contains(term.toString())){
      // add a term
      subterms(term.toString()) = term
      // generate all subterms
      val ts = term match {
        case FOLVar(v) => Map[String, FOLTerm]()
        case FOLConst(c) =>  Map[String, FOLTerm]()
        case Function(f,args)  =>  args.flatMap(((t: FOLTerm) => st_trav(subterms, t)))
      }
      subterms ++= ts
    }
    subterms
  }

  /**
   * Extracting the result of st_trav for a term t
   * 
   * @param t FOLTerm for which all subterms are calculated
   * @return list of all subterms
   */
  def st(t: FOLTerm) : List[FOLTerm] = {
    // extract the list of all subterms of the term
    st_trav(HashMap[String, FOLTerm](), t).map(_._2).toList
  }

  /**
   * Generating all subterms of a language of FOLTerms
   *
   * @param language termset for which st is called for each element
   * @return list of all subterms
   */
  def subterms(language: List[FOLTerm]) : List[FOLTerm] = {
    val terms = HashMap[String, FOLTerm]()
    for(t <- language){
      if(!terms.contains(t.toString())){
        terms ++= st_trav(terms, t)
      }
    }
    terms.map(_._2).toList
  }

  /**
   * Generates the powerset S as a List of a List, where
   * |S| <= n
   *
   * @param s list
   * @param n upperbound for the powerset
   * @tparam A type of the list
   * @return bounded powerset
   */
  def boundedPower[A](s: List[A], n: Int): List[List[A]] = {
    // init powerset
    val powerset = List[List[A]]()

    // function for generating a subset of the powerset of a particular size
    def genLists(l: List[A], i:Int, n: Int): List[List[A]] = l match {
      // if no elements are left terminate
      case Nil        => List[List[A]]()
      // if we can still add an element
      // EITHER do not add it and leave i (size of already chosen elements) as it is
      // OR add it and increment i
      case a :: as  if i+1 < n  => genLists(as,i,n) ++ (genLists(as,i+1,n) map (a :: _))
      // if we can add just one more element
      // either do so, or not
      case a :: as  if i+1 >= n => List(List(a)) ++ genLists(as,i,n)
    }
    // call genLists for 1 <= i <= n times
    // and concatenate all results, s.t. we get the intended result
    (for (i <- List.range(1, n+1)) yield genLists(s,0,i)).foldLeft(List[List[A]]())( (prevLists,l) => prevLists ++ l)
  }

  /**
   * suffKeys - as described in Eberhard [2014] -
   * generates a sufficient set of keys w.r.t. a termset/language l
   */
  def suffKeys() {

    //var result = scala.collection.mutable.Set[FOLTerm]()
    val st = subterms(termset)
    //       This is kind of tricky, because we don't know a priori
    //       how large n can get
    //       for now we just take a provided n
    val poweredSubSets = boundedPower(st, n)

    // for each subset of size 1 <= |sub| <= n+1,
    // add all keys of normform(sub) to keySet
    var i = 0
    var x = 0
    poweredSubSets.foreach( sub => {
      // just for logging
      val t = (100*(i.toFloat/poweredSubSets.size)).toInt
      if( t % 10 == 0 && t != x)
      {
        x = t
        debug("Generated "+(100*(i.toFloat/poweredSubSets.size)).toInt+"% of suffKeys")
      }
      i+=1
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
    debug("Generated 100% of suffKeys")
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
   * Calculates the characteristic partition of a term t
   * as described in Eberhard [2014], w.r.t. a non-terminal
   *
   * @param t term for which the characteristic Partition is calculated
   * @param nonterminal string representing a non-terminal
   * @return characteristic partition of t
   */
  def calcCharPartition(t: FOLTerm, nonterminal: String) : List[List[Int]] = {
    val positions = getAllPositionsFOL(t)
    val pos = positions.foldLeft(List[Option[List[Int]]]())((acc,p) => (p match {
      case (pos, FOLVar(x)) if x.startsWith(nonterminal) => Some(pos)
      case _ => None
    }) :: acc)

    return ((pos.flatten) ::: List())
  }

  /**
   * If for a given term t, the termposition position exists
   * replace the subtree with the root at position with a FOLVar(variable_index).
   * Otherwise return the term as it is.
   *
   * @param t term
   * @param variable string representation of the nonterminal prefix
   * @param position list of positions of variable
   * @param index nonterminal index i
   * @return the original term if the replacement could not be processed, or t|p_1 = α_i ... t|p_n = α_i
   */
  def replaceAtPosition(t: FOLTerm, variable: String, position: List[Int], index: Int) : FOLTerm = {
    try{
      val replacement = new at.logic.language.fol.replacements.Replacement(position, FOLVar(variable+"_"+index))
      return replacement(t).asInstanceOf[FOLTerm]
    }catch{
      case e: IllegalArgumentException =>  // Possible, nothing special to do here.
    }
    return t
  }

  /**
   * Checks if a FOLVar exists in t with a certain variable_prefix.
   * e.g. nonterminalOccurs(f(x1,y2,z1), "y") = true
   *
   * @param t term
   * @param variable_prefix variable prefix
   * @return true if a variable with the particular prefix exists in t, otherwise false
   */
  def nonterminalOccurs(t: FOLTerm, variable_prefix: String) : Boolean = t match {
    case FOLVar(x) => return x.startsWith(variable_prefix)
    case FOLConst(x) => false
    case Function(x, args) => return args.foldLeft(false)((s,a) => s || nonterminalOccurs(a, variable_prefix))
    case _ => return false
  }


  /**
   * increments the index of a FOLVar by 1, if it has an index
   * otherwise do nothing
   *
   * @param v FOLVar to be processed
   * @return v with incremented index
   */
  def incrementIndex(v: FOLVar) : FOLVar = {
    val parts = v.toString.split("_")
    try {
      val index = parts.last.toInt
      FOLVar((parts.take(parts.size - 1).foldLeft("")((acc, x) => acc + "_" + x) + "_" + (index + 1)).substring(1))
    }catch{
      case e: NumberFormatException => return v //variable has no index
    }
  }

  /**
   * for a particular term increment all variables indexes
   *
   * @param t term
   * @return term with incremented variable indexes
   */
  def incrementAllVars(t: FOLTerm) : FOLTerm = {
    t match {
      case FOLVar(x) => incrementIndex(FOLVar(x))
      case FOLConst(c) => FOLConst(c)
      case Function(f,l) => Function(f,l.map(p => incrementAllVars(p)))
      case _ => {warn("An unexpected case happened. Maleformed FOLTerm.");
                t}
    }
  }

  def replaceAllVars(t: FOLTerm, prefix1: String, prefix2:String) : FOLTerm = {
    t match {
      case FOLVar(x) => FOLVar(x.replace(prefix1,prefix2))
      case FOLConst(c) => FOLConst(c)
      case Function(f,l) => Function(f,l.map(p => replaceAllVars(p, prefix1, prefix2)))
      case _ => {warn("An unexpected case happened. Maleformed FOLTerm.");
        t}
    }
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

    val nonterminal_a = "α"
    val nonterminal_b = "β"

    // initialize delta vector
    var delta = new UnboundedVariableDelta()
    // retrieve the key, since computeDelta returns a decomposition T = U o S
    var decomposition = delta.computeDelta(l, nonterminal_b).toList(0)

    // add the decomposition to the key map
    // TODO: eventually check if the nonterminals in k are ambigous
    val k = incrementAllVars(decomposition._1)//decomposition._1

    // calculate the characteristic partition
    var charPartition = calcCharPartition(k, nonterminal_b)
    var permutedCharPartition = charPartition.permutations.toList

    // for each ordered list of position sets
    permutedCharPartition.foreach(p => {
      // nonterminal index
      var index = 1
      // new_key as in Eberhard [2014]
      var new_key = k
      // for every position in the set
      // try to replace the term on that position by a non-terminal
      for( i <- Range(0,p.size)){
        var old_key = new_key
        new_key = replaceAtPosition(new_key, nonterminal_a, p(i), index)
        // if the key has changed, increment the
        // non-terminal index
        if(old_key != new_key)
        {
          index+=1
        }
      }
      // if new_key does not contain the previously introduced non-terminals nonterminal_b
      // i.e. only non-terminals nonterminal_a occur
      // add the key to the outputset
      if(!nonterminalOccurs(new_key, nonterminal_b)){
        result += new_key
        decompMap(new_key) = decomposition._2
      }
    })
    return result.toList

  }

}
