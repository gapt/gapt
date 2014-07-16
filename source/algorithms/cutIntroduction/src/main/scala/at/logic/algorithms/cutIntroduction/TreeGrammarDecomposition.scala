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
   * Checks if a rest r is a rest w.r.t. a key k in a term t
   * i.e. t = k[\alpha_1 \ r(0)]...[\alpha_{n+1} \ r(n)]
   */
  def isRest(t: FOLTerm, k: FOLTerm, r: List[FOLTerm]) : Boolean = {
    val evs = for (x <- List.range(1, 1+r.size)) yield FOLVar("α_"+x)
    val sub = Substitution(evs.zip(r))
    return t == sub(k)
  }

  /*
   * Generates out of a set S
   * the diagonal cartesian product S² of it
   */
  def diagCross(l:List[Int]) : List[(Int,Int)] = {
    l match {
      case x::xs => xs.map(y => (x,y)) ++ diagCross(xs)
      case _ => Nil
    }
  }

  /*
   * Transforms a sufficient set of keys into a propositional
   * formula as described in Eberhard [2014].
   * n the number of non-terminals
   */
  def MCS() : List[FOLFormula] = {
    //And(termset.foldLeft(List[FOLFormula]())((acc,q) => C(q) :: acc))
    val f = termset.foldLeft(List[FOLFormula]())((acc,q) => C(q) ::: acc)
    debug("F: "+f.foldLeft("")((acc,x) => acc + "\\\\ \n"+printExpression(x).replaceAllLiterally("α", "\\alpha")))
    return f
  }

  def R(qindex: Int, qsubtermIndexes: Set[Int]) : FOLFormula = {
    // for all pairs t_0,t_1 \in st({q}), s.t. t_0 != t_1
    /*val pairs = qsubtermIndexes.flatMap(t0 => qsubtermIndexes.foldLeft(List[(Int,Int)]())((acc,t1) => {
      if(t1 != t0){
        (t0,t1) :: acc
      }
      else{
        acc
      }
    }))*/
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

  def pA(c:FOLConst) : String = {
    val s = c.toString.split("_")
    if(s.size == 2)
    {
      return "x_{\\alpha_{"+s(0)+"},"+keyList(s(1).toInt)+"}"
    }else{
      return "x_{"+termset(s(0).toInt)+",\\alpha_{"+s(1)+"},"+termset(s(2).toInt)+"}"
    }
  }

  /*
   * Generates the formula D_{L,S}(t,i,q) according to
   * Eberhard [2014]
   */
  def D(t: FOLTerm, l: Int, q: FOLTerm): FOLFormula = {

      // for every key k_j producing t, which
      // ONLY CONTAINS α_i, where i > l
      //debug("D -> keyMap("+t+") = "+keyMap(t))
      Or(keyMap(t).foldLeft(List[FOLFormula]())((acc1,klistindex) => {
        // add the propositional variable x_{k_j}
        val x_l_kj = FOLConst(l+"_"+klistindex)
        propRules(x_l_kj) = (l,klistindex)

        val ruleVar : FOLFormula = Atom("X",List(x_l_kj))

        // get all eigenvariables occuring in the subterm t
        val evs = getEigenvariables(keyList(klistindex),"α")//.map(x => FOLVar(x))
        // check if all eigenvariables α_i suffice i > l
        if(evs.foldLeft(true)((acc,x) => acc && (x.split("_").last.toInt > l ))){
          //debug("NOT skipping key='"+keyList(klistindex)+"' for l="+l)
          // for every eigenvariable in k_j
          And(ruleVar :: evs.foldLeft(List[FOLFormula]())((acc2,ev) => {
            // get the eigenvariables index i
            val evindex = ev.split("_").last.toInt
            // TODO: Note: x = 0 is used due to the fact that we don't consider blocks of quantifiers
            val x = 0
            // and for every element r_j in the decomposition's sublanguage S where kj is its U
            // TODO: Note: That for blocks of quantifiers here decompMap eventually does not contain mirror cases of keys like f(g(α_2),α_1), but f(g(α_1),α_2)
            //debug("Generating REST-Var Conjunction for rests decompMap("+keyList(klistindex)+") = "+decompMap(keyList(klistindex)))
            val k = keyList(klistindex)
            decompMap(k).foldLeft(List[FOLFormula]())((acc3,d) => {

              // if d is a rest of k regarding t
              // add it to the formula
              if(isRest(t, k, d)) {
                val rindex = addToTermMap(d(x))
                val qindex = addToTermMap(q)
                // take the rest of the particular eigenvariable
                Atom("X", List(FOLConst(rindex + "_" + evindex + "_" + qindex))) :: acc3
              }else{
                // otherwise don't
                acc3
              }
            }) ::: acc2
          })) :: acc1
        }
        else{
          //debug("Skipping key '"+keyList(klistindex)+"' for l="+l)
          ruleVar :: acc1
        }
    }))
  }

  /*
   * Generates out of a term q the formula
   * C_{L,S}(q) as written in Eberhard [2014]
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
        val d = D(t,i,q)
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

  /*
   * Eventually adds a term to the term map and returns its index
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
