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




class TreeGrammarDecomposition(termset: List[FOLTerm], n: Int) {

  // an ordering to order FOLTerms by their string representation
  //val order = Ordering[String].on[FOLTerm](s => s.toString)
  // the sufficient set of keys represented as a sorted set on above order
  //private var keySet : mutable.SortedSet[FOLTerm] = mutable.SortedSet[FOLTerm]()(order)

  var termMap : mutable.HashMap[FOLTerm,Int] = mutable.HashMap[FOLTerm,Int]()
  var termIndex = 0

  // the sufficient set of keys represented as a list
  var keyList : mutable.MutableList[FOLTerm] = mutable.MutableList[FOLTerm]()

  // a hashmap storing for every key its index in keyList
  var keyIndexMap : mutable.HashMap[FOLTerm,Int] = mutable.HashMap[FOLTerm,Int]()

  // stores tuples (term,keyset), where keyset is a list of indexes of keys in keyset
  // which produce a particular term
  var keyMap : mutable.HashMap[FOLTerm,mutable.Set[Int]] = mutable.HashMap[FOLTerm,mutable.Set[Int]]()

  var propRules : mutable.HashMap[FOLConst,(Int,Int)] = mutable.HashMap[FOLConst,(Int,Int)]()
  var propRests : mutable.HashMap[FOLConst,(Int,Int,Int)] = mutable.HashMap[FOLConst,(Int,Int,Int)]()

  /*
   * Transforms a sufficient set of keys into a propositional
   * formula as described in Eberhard [2014].
   * n the number of non-terminals
   */
  def MCS() : FOLFormula = {
    val formula = termset.foldLeft(List[FOLFormula]())((acc,q) => C(q) :: acc)
    And(formula)
  }

  def R(qindex: Int, qsubtermIndexes: Set[Int]) : FOLFormula = {
    // for all pairs t_0,t_1 \in st({q}), s.t. t_0 != t_1
    val pairs = qsubtermIndexes.flatMap(t0 => qsubtermIndexes.map(t1 => (t0,t1)))
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

  /*
   * TODO: Develop the formula for generating D_{L,S}(t,i,q)
   */
  def D(tindex: Int, i: Int, qindex: Int): FOLFormula = {
    Atom("P",Nil)
  }

  /*
       * Generates out of a term q the formula
       * C_{L,S}(q) as written in Eberhard [2014]
       */
  def C(q: FOLTerm) : FOLFormula = {

    val subterms = st(q)
    // save the index of the term for later
    val qindex = addToTermMap(q)
    var qsubtermIndexes = mutable.Set[Int]()
    val formulas: List[FOLFormula] = subterms.foldLeft(List[FOLFormula]())((acc,t) => {
      // save the index of the term for later
      val tindex = addToTermMap(t)
      qsubtermIndexes += tindex

      // For t \in st({q}), 1 <= i <= n
      Range(1,n+1).foldLeft(List[FOLFormula]())((acc,i) => {
        val co = FOLConst(tindex+"_"+i+"_"+qindex)
        propRests(co) = (tindex,i,qindex)
        Imp(Atom("X",co :: Nil), D(tindex,i,qindex)) :: acc
      })
    })

    And(formulas ++ List(D(qindex,0,qindex), R(qindex,qsubtermIndexes.toSet)))
  }

  /*
   * Evetnually adds a term to the term map and returns its index
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

  def st(term: FOLTerm) : List[FOLTerm] = {
    // extract the list of all subterms of the term
    st_trav(HashMap[String, FOLTerm](), term).map(_._2).toList
  }

  /*
   * Generating all subterms of a language of FOLTerms
   *
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

  /*
   * Generates the powerset S as a List of a List, where
   * |S| <= n
   *
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

  /*
   * suffKeys - as described in Eberhard [2014] -
   * generates a sufficient set of keys w.r.t. a termset/language l
   */
  def suffKeys() {

    var result = scala.collection.mutable.Set[FOLTerm]()
    val st = subterms(termset)
    // TODO: check how to calculate n before calling normform
    //       This is kind of tricky, because we don't know a priori
    //       how large n can get
    //       For now, we just take the size of the set of subterms
    val poweredSubSets = boundedPower(st, st.size+1)

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
      var keyIndexes = mutable.Set[Int]()
      keys.foreach(k => {
        // if the key does not already exist
        // in the keyIndexMap
        if(!keyIndexMap.exists(_._1 == k)){
          // add it to keyList and keyIndexMap
          keyList += k
          keyIndexMap(k) = keyList.size - 1
          keyIndexes += keyList.size - 1
        }
        else{
          keyIndexes += keyIndexMap(k)
        }
      })
      //keyList ++= keys

      // for every term t
      // save the corresponding keyIndexes of the keys
      // which produce this particular term
      sub.foreach(t => {
        // if the key does not already exist
        if(!keyMap.exists(_._1 == t)){
          // add it
          keyMap(t) = keyIndexes
        }
        else{
          keyMap(t) ++= keyIndexes
        }
      })
    })
    debug("Generated 100% of suffKeys")
  }

  /*
   * Adds a list of keys to the keymap
   */
  def addToKeyMap(term: FOLTerm, keys: List[Int]) {
    // if the term is already in the map
    if(keyMap.exists(_._1 == term)){
      // merge the lists
      keyMap(term) ++: keys
    }
    else{
      // create a new (term,set) pair in the map
      keyMap(term) = mutable.Set(keys :_*)
    }
  }

  /*
   * Calculates the characteristic partition of a term t
   * as described in Eberhard [2014], w.r.t. an eigenvariable
   */
  def calcCharPartition(t: FOLTerm, eigenvariable: String) : List[List[Int]] = {
    var positions = getAllPositionsFOL(t)
    var pos = positions.foldLeft(List[Option[List[Int]]]())((acc,p) => (p match {
      case (pos, FOLVar(x)) if x.startsWith(eigenvariable) => Some(pos)
      case _ => None
    }) :: acc)

    return ((pos.flatten) ::: List())
  }

  /*
   * If for a given term t, the termposition position exists
   * replace the subtree with the root at position with a FOLVar(variable_index).
   * Otherwise return the term as it is.
   */
  def replaceAtPosition(t: FOLTerm, variable: String, position: List[Int], index: Int) : FOLTerm = {
    try{
      val termToReplace = getAtPositionFOL(t,position)
      val replacement = new at.logic.language.fol.replacements.Replacement(position, FOLVar(variable+"_"+index))
      return replacement(t).asInstanceOf[FOLTerm]
    }catch{
      case e: IllegalArgumentException =>  // Possible, nothing special to do here.
    }
    return t
  }

  /*
   * Checks if a FOLVar exists in <t> with a certain <variable_prefix>.
   * e.g. eigenvariableOccurs(f(x1,y2,z1), "y") = True
   */
  def eigenvariableOccurs(t: FOLTerm, variable_prefix: String) : Boolean = t match {
    case FOLVar(x) => return x.startsWith(variable_prefix)
    case FOLConst(x) => false
    case Function(x, args) => return args.foldLeft(false)((s,a) => s || eigenvariableOccurs(a, variable_prefix))
    case _ => return false
  }
  /*
   * normform produces, depending on a language l
   * a set of keys in normalform.
   * TODO: check if isomorphic keys can be purged, i.e. {f(g(α_1),α_2), f(g(α_2),α_1)}
   */
  def normform(l: List[FOLTerm]) : List[FOLTerm] = {

    val result = MutableList[FOLTerm]()

    val eigenvariable_a = "α"
    val eigenvariable_b = "β"

    // initialize delta vector
    var delta = new UnboundedVariableDelta()
    // retrieve the key, since computeDelta returns a decomposition T = U o S
    var k = delta.computeDelta(l, eigenvariable_b).toList(0)._1

    // calculate the characteristic partition
    var charPartition = calcCharPartition(k, eigenvariable_b)
    // TODO: check if removing of duplicates is necessary
    charPartition = charPartition.distinct
    var permutedCharPartition = charPartition.permutations.toList

    // for each ordered list of position sets
    permutedCharPartition.foreach(p => {
      // eigenvariable index
      var index = 0
      // new_key as in Eberhard [2014]
      var new_key = k
      // for every position in the set
      // try to replace the term on that position by a non-terminal
      for( i <- Range(0,p.size)){
        var old_key = new_key
        new_key = replaceAtPosition(new_key, eigenvariable_a, p(i), index)
        // if the key has changed, increment the
        // non-terminal index
        if(old_key != new_key)
        {
          index+=1
        }
      }
      // if new_key does not contain the previously introduced non-terminals eigenvariable_b
      // i.e. only non-terminals eigenvariable_a occur
      // add the key to the outputset
      if(!eigenvariableOccurs(new_key, eigenvariable_b)){
        result += new_key
      }
    })
    return result.toList

  }

}
