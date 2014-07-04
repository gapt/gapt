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


object TreeGrammarDecomposition{
  def apply(termset: List[FOLTerm], n:Int) = {
    val decomp = new TreeGrammarDecomposition(termset,n)
    decomp.suffKeys()
    debug("Generating MinCostSAT formulation")
    val f = Set(decomp.MCS())//, decomp.additionalFormula())
    println("F: \n")
    f.foreach(x => println(x+"\n"))
    val g = decomp.softConstraints()
    println("G: \n"+g)
    debug("Starting up QMaxSAT Solver")
    println(decomp.getRules((new QMaxSAT).solvePWM(f,g)))
  }
}


class TreeGrammarDecomposition(termset: List[FOLTerm], n: Int) extends at.logic.utils.logging.Logger {

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

  // stores tuples (term,keyset), where keyset is a list of indexes of keys in keyList
  // which produce the particular term
  var keyMap : mutable.HashMap[FOLTerm,mutable.Set[Int]] = mutable.HashMap[FOLTerm,mutable.Set[Int]]()

  var propRules : mutable.HashMap[FOLConst,(Int,Int)] = mutable.HashMap[FOLConst,(Int,Int)]()
  var propRests : mutable.HashMap[FOLConst,(Int,Int,Int)] = mutable.HashMap[FOLConst,(Int,Int,Int)]()

  var decompMap : mutable.HashMap[FOLTerm,Set[List[FOLTerm]]] = mutable.HashMap[FOLTerm,Set[List[FOLTerm]]]()

  /*
   * Generates the soft constraints for
   * the MCS formulation as a partial weighted MaxSAT problem,
   * where -x_{i,k} has cost 1 for all non-terminals α_i and keys k
   */
  def softConstraints() : Set[Tuple2[FOLFormula,Int]] = {
    propRules.foldLeft(Set[Tuple2[FOLFormula,Int]]())((acc,x) => acc + Tuple2(Neg(Atom("X",List(x._1))),1))
  }

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

  /*
   * Transforms a sufficient set of keys into a propositional
   * formula as described in Eberhard [2014].
   * n the number of non-terminals
   */
  def MCS() : FOLFormula = {
    And(termset.foldLeft(List[FOLFormula]())((acc,q) => C(q) :: acc))
  }

  def R(qindex: Int, qsubtermIndexes: Set[Int]) : FOLFormula = {
    // for all pairs t_0,t_1 \in st({q}), s.t. t_0 != t_1
    val pairs = qsubtermIndexes.flatMap(t0 => qsubtermIndexes.foldLeft(List[(Int,Int)]())((acc,t1) => {
      if(t1 != t0){
        (t0,t1) :: acc
      }
      else{
        acc
      }
    }))
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
   * Given a FOLTerm and a prefix for a variable,
   * this function returns a list of all FOLVars in t starting
   * with the particular prefix
   */
  def getEigenvariables(t: FOLTerm, eigenvariable_prefix: String) : List[String] = {
    val s = t match {
      case Function(f,args) => args.foldLeft(Set[String]())((prevargs,arg) => prevargs ++ getEigenvariables(arg, eigenvariable_prefix))
      case FOLVar(v) => if(v.toString.startsWith(eigenvariable_prefix)) Set[String](v.toString()) else Set[String]()
      case _ => Set[String]()
    }
    s.toList

  }

  def additionalFormula() : FOLFormula = {
    Or(propRules.map( x => Atom("X",List(x._1))).toList)
  }

  /*
   * Generates the formula D_{L,S}(t,i,q) according to
   * Eberhard [2014]
   */
  def D(t: FOLTerm, l: Int, q: FOLTerm): FOLFormula = {

      // for every key k_j producing t, which
      // ONLY CONTAINS α_i, where i > l
      Or(keyMap(t).foldLeft(List[FOLFormula]())((acc1,klistindex) => {
        // add the propositional variable x_{k_j}
        val x_l_kj = FOLConst(l+"_"+klistindex)
        propRules(x_l_kj) = (l,klistindex)
        // get all eigenvariables occuring in the subterm t
        val evs = getEigenvariables(keyList(klistindex),"α")//.map(x => FOLVar(x))
        // check if all eigenvariables α_i suffice i > l
        if(evs.foldLeft(true)((acc,x) => acc && (x.split("_").last.toInt > l ))){
          //debug("NOT skipping key '"+keyList(klistindex)+"' for l="+l)
          // for every eigenvariable in k_j
          And(evs.foldLeft(List[FOLFormula](Atom("X",List(x_l_kj))))((acc2,ev) => {
            // get the eigenvariables index i
            val evindex = ev.split("_").last.toInt
            var rests = mutable.MutableList[FOLFormula]()
            val x = 0
            // and for every element r_j in the decomposition's sublanguage S where kj is its U
            // TODO: Note: That for blocks of quantifiers here decompMap eventually does not contain mirror cases of keys like f(g(α_2),α_1), but f(g(α_1),α_2)
            decompMap(keyList(klistindex)).foreach(d => {
              val rindex = addToTermMap(d(x))
              val qindex = addToTermMap(q)
              // take the rest of the particular eigenvariable
              rests += Atom("X",List(FOLConst(rindex+"_"+evindex+"_"+qindex)))
            })
            (rests.toList ::: acc2)
          }))  :: acc1
        }
        else{
          //debug("Skipping key '"+keyList(klistindex)+"' for l="+l)
          acc1
        }
    }))
  }

  /*
   * Generates out of a term q the formula
   * C_{L,S}(q) as written in Eberhard [2014]
   */
  def C(q: FOLTerm) : FOLFormula = {

    debug("Generating C(q), where q = '"+q+"'")
    val subterms = st(q)
    // save the index of the term for later
    val qindex = addToTermMap(q)
    var qsubtermIndexes = mutable.Set[Int]()
    val formulas: List[FOLFormula] = subterms.foldLeft(List[FOLFormula]())((acc,t) => {
      // save the index of the subterm for later
      val tindex = addToTermMap(t)
      qsubtermIndexes += tindex

      // For t \in st({q}), 1 <= i <= n
      Range(1,n+1).foldLeft(List[FOLFormula]())((acc,i) => {
        val co = FOLConst(tindex+"_"+i+"_"+qindex)
        propRests(co) = (tindex,i,qindex)
        Imp(Atom("X",co :: Nil), D(t,i,q)) :: acc
      })
    })

    And(formulas ++ List(D(q,0,q), R(qindex,qsubtermIndexes.toSet)))
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

    //var result = scala.collection.mutable.Set[FOLTerm]()
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
    val positions = getAllPositionsFOL(t)
    val pos = positions.foldLeft(List[Option[List[Int]]]())((acc,p) => (p match {
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
   * increments the index of a FOLVar by 1
   * TODO: Error Handling
   */
  def incrementIndex(v: FOLVar) : FOLVar = {
    val parts = v.toString.split("_")
    val index = parts.last.toInt
    FOLVar((parts.take(parts.size - 1).foldLeft("")((acc,x) => acc+"_"+x)+"_"+(index+1)).substring(1))
  }

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
    var decomposition = delta.computeDelta(l, eigenvariable_b).toList(0)

    // add the decomposition to the key map
    // TODO: eventually check if the eigenvariables in k are ambigous
    val k = incrementAllVars(decomposition._1)//decomposition._1
    //decompMap(k) = decomposition._2
    decompMap(replaceAllVars(k,eigenvariable_b,eigenvariable_a)) = decomposition._2

    // calculate the characteristic partition
    var charPartition = calcCharPartition(k, eigenvariable_b)
    // TODO: check if removing of duplicates is necessary
    charPartition = charPartition.distinct
    var permutedCharPartition = charPartition.permutations.toList

    // for each ordered list of position sets
    permutedCharPartition.foreach(p => {
      // eigenvariable index
      var index = 1
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
