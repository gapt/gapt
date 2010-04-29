package at.logic.algorithms.diophantine

import at.logic.language.hol.logicSymbols.{ConstantStringSymbol, ConstantSymbolA}
import at.logic.language.fol._
import at.logic.algorithms.diophantine.{Vector, LankfordSolver}
import at.logic.language.lambda.symbols.{VariableSymbolA, VariableStringSymbol}
import at.logic.language.lambda.substitutions.Substitution

import collection.mutable.HashMap

object ACUnification {
  type TermCount = (FOLTerm,Int)
  type ListEntry = (Int, Vector, List[Vector])
  type MapEntry = (Int, List[Vector])
  type ArrayEntry = (Vector, MapEntry)

  var constant_prefix = "z_"
  var unit_constant = FOLConst(new ConstantStringSymbol("1"))
  var maxindex = 0

  val is_ac1 : Boolean = false
  val debuglevel = 0 // 0... no output, 1 ... show unifiers after unification 2--- also before unification 3... maximum

  def debug(level:Int, msg:String) = if (debuglevel>=level) println("DEBUG: "+msg+" \\\\")

  def potbrak(m:Int,s:String) : String = if (m<10) "" else s 
  def resetVariablegenerator() = { maxindex = 0 }
  def getFreshVariable() : VariableSymbolA = { maxindex += 1; VariableStringSymbol(constant_prefix+potbrak(maxindex,"{")+maxindex+potbrak(maxindex,"}")) }

  def unify(function: ConstantSymbolA, term1 : FOLTerm, term2 : FOLTerm) : Option[List[Substitution[FOLTerm]]] = {
    val mgus = unify(function, List((term1, term2)), List(Substitution[FOLTerm]()) )
    mgus match {
      case Nil => debug(1,"Found no unifier!"); None;
      case _   => for (mgu<-mgus) debug(2,"found unifier: "+mgu); Some(mgus)}
  }

  def unify(function: ConstantSymbolA,
            terms : List[(FOLTerm,FOLTerm)],
            substs : List[Substitution[FOLTerm]]) : List[Substitution[FOLTerm]] = {
    debug(3,"unifying "+terms+" substitutions are: "+substs)
    terms match {
      case (term1,term2) :: rest =>
        term1 match {
          // comparing constant to sthg else
          case FOLConst(c1) =>
            term2 match {
               // if the two constants are equal, the substitution is not changed, else not unifiable 
              case FOLConst(c2) =>
                if (c1==c2) collect(substs, ((s:Substitution[FOLTerm]) => unify(function, rest, List(s))))
                else Nil
              // second one is a var => flip & variable elimination
              case FOLVar(v) =>
                val ve = Substitution[FOLTerm](term2.asInstanceOf[FOLVar],term1)
                val newterms = rest map makesubstitute_pair(ve)
                collect(substs, (s:Substitution[FOLTerm]) => unify(function, newterms, List(ve compose s))) //TODO:check, ok
              // anything else is not unifiable
              case _ =>
                Nil
            }
          // comparing function symbol to sthg else
          case Function(f1,args1)  =>
            term2 match {
              // decomposition or ac unification, if the function symbols are the same, else not unifiable 
              case Function(f2,args2) =>
                if (f1 != f2) {
                  Nil
                } else if (args1.length != args2.length) {
                  throw new Exception("function symbols both named "+ f1 + " but with different arity "
                          + args1.length + " and "+args2.length+ "encountered!")
                } else if (f1 == function) {
                  //ac unification
                  val acunivs = ac_unify(function, term1, term2)
                  collect(acunivs, ((acu:Substitution[FOLTerm]) =>
                    collect(substs, ((subst:Substitution[FOLTerm]) =>
                      unify(function, rest map makesubstitute_pair(subst), List((acu compose subst)))) //TODO:check, ok
                   )))
                } else  {
                  //non ac unification => decomposition
                  collect(substs , (s:Substitution[FOLTerm]) => unify(function, (args1 zip args2) ::: rest, List(s)))
                }
              // variable as second term: flip & variable elimination
              case FOLVar(v) =>
                //occurs check
                if (occurs(term2.asInstanceOf[FOLVar], term1)) {
                  Nil
                } else {
                  val ve = Substitution[FOLTerm](term2.asInstanceOf[FOLVar],term1)
                  val newterms = rest map makesubstitute_pair(ve)
                  collect(substs, (s:Substitution[FOLTerm]) => unify(function, newterms, List((ve compose s))))//TODO:check, ok
                }
              // anything else is not unifiable
              case _ =>
                Nil
            }

          //variable elimination
          case FOLVar(v) =>
            term2 match {
              case FOLVar(w) =>
                if (v==w) {
                  collect(substs,(s:Substitution[FOLTerm]) => unify(function, rest, List(s)))
                } else {
                  val ve = Substitution[FOLTerm](term1.asInstanceOf[FOLVar],term2)
                  val newterms = rest map makesubstitute_pair(ve)
                  collect(substs,(s:Substitution[FOLTerm]) => unify(function, newterms, List((ve compose s).asInstanceOf[Substitution[FOLTerm]]))) //TODO:check, ok
                }

              case _ =>
                //occurs check
                if (occurs(term1.asInstanceOf[FOLVar], term2)) {
                  Nil
                } else {
                  val ve = Substitution[FOLTerm](term1.asInstanceOf[FOLVar],term2)
                  val newterms = rest map makesubstitute_pair(ve)
                  collect(substs, (s:Substitution[FOLTerm]) => unify(function, newterms, List[Substitution[FOLTerm]]((ve compose s)))) //TODO:check, ok
                }
          }

          //this should be empty in the end
          case _ =>
            throw new Exception("there should be only variables, constants and functions in first order terms!")
        }

      case Nil =>
        substs
    }
  }
  

  def ac_unify(function: ConstantSymbolA, term1 : FOLTerm, term2 : FOLTerm) : List[Substitution[FOLTerm]] = {
    debug(1,"=== unifying "+flatten(function,term1)+" with "+flatten(function,term2)+ "===")
    val counted_symbols = countSymbols(nestedFunctions_toList(function,term1), nestedFunctions_toList(function,term2))
    val (ts1,count1) = List unzip counted_symbols

    val (lhs,rhs) = (counted_symbols partition (_._2 >0)) // this works because countSymbols only returns values != 0
    val vlhs = Vector(lhs map (_._2))
    val vrhs = Vector(rhs map (_._2 * -1))


    val (unifiable_invariant,unifiable_condition) = createConstantFilter((lhs map (_._1)) ::: (rhs map (_._1)))

    val vlhs_length = vlhs.length
    val vrhs_length = vrhs.length

    if ((lhs == Nil) || (rhs == Nil)) {
      Nil
    }
    else {
      val basis = LankfordSolver solve (vlhs,vrhs) sort Vector.lex_< 
      val sums = calculateSums_new(basis, vlhs, vrhs, unifiable_invariant)


      var results : List[Vector] = Nil
      if (is_ac1) {
        results = sums.keySet.toList.filter(unifiable_condition) //AC1 Unification does not filter out
      } else {
        // ac unification filters
        for (v <- sums.toList ) {
          if (gzero(v._1))
            results = v._1 ::results
        }

        results = results.filter(unifiable_condition) 
      }

      // remove vectors which are subsumed by smaller vectors
      results = removeSubsumedVectors_new(results, Vector(vlhs.vector ::: vrhs.vector))
      //debug(1,"number of solutions: "+results.size)

      // associate every base vector to a fresh logical variable
      val varmap = new HashMap[Vector,VariableSymbolA]

      debug(1,"basis:")
      for (b<-basis) {
        val v : VariableSymbolA = getFreshVariable()
        debug(1,"$"+v+"<-"+b+"$")
        varmap(b) = v
      }

      for (s<-sums.toList.sort((x:(Vector,List[(Int,List[Vector])]),y:(Vector,List[(Int,List[Vector])])) => Vector.lex_<(x._1,y._1)))
        debug(1,"whole sums "+s)


      for (s<-results)
        debug(1,"sum $"+s+"$ with representative $"+sums(s).map(_._2.map(varmap(_))) )
//      debug(1,"sum $"+s+"$ with representative $"+sums(s).head._2.map(varmap(_))+"$ sum in map=$"+sums(s).head._1+"$")

      //some helper functions, could be factored out
      def extract(pair:(Int,List[Vector])) : List[Vector] = pair._2

      def ntimes[A](x:A,n:Int) : List[A] = if (n<=0) Nil else x::ntimes(x,n-1) 
      
      def nfilter[A](l:List[A], count : (A=>Int)) : List[A] = {
        l match {
          case x::xs => ntimes(x,count(x)) ::: nfilter(xs,count)
          case Nil => Nil
        }
      }

      def createVectors(mapping : HashMap[Vector, VariableSymbolA], v:List[Vector]) : List[FOLTerm]= {
        //val len = v.length
        val len = if (v == Nil) 0 else v(0).length-1

        //println("create vectors length="+len+" v="+v)
        val expanded : List[(Int,List[Vector])] = ((0 to len) map ((_,v))).toList //pair vector with every index of a component
        val filtered : List[List[VariableSymbolA]] =
              expanded map (x=>
                  (nfilter (x._2, ((v:Vector)=>v.vector(x._1))))  //take the vector the number of times of the actual component
                            map (mapping(_))          //and convert them to VariableSymbols
              )
        val ltt : List[VariableSymbolA] => FOLTerm = listToTerm(function,_)
        filtered map ltt
      }

      debug(2,""+results.length + " ac unification preresults:"+results)
      //convert results to list of terms
      var converted : List[List[FOLTerm]] = Nil
      for (r <- results) {
        for (i <- sums(r).map(extract))
        //val i = sums(r).map(extract).head //one representative is enough
          converted = createVectors(varmap, i) :: converted
      }


      debug(1,"$"+converted.length + "$ ac unification results: $"+converted+"$")

      var unified_terms : List[List[FOLTerm]] = Nil
      var unifiers : List[Substitution[FOLTerm]] = Nil
      for (c<-converted) {
        val zc = ts1 zip c
        //println("finding unifier for: "+zc)
        val us = unify(function, zc, List(Substitution[FOLTerm]()) )
        for (unifier <- us) {
            val uterm : List[FOLTerm] = ts1 map ((x:FOLTerm)=>unifier.apply(x))
            //println("yay found one:" + uterm)
            //unifiers = subst :: unifiers
            unifiers = unifier :: unifiers
            unified_terms = uterm :: unified_terms 
        }
      }

      val term_context = (ts1 map ((x:FOLTerm) => getVariableContext(x))) reduceLeft (_++_)

      //remove variables not in the original term from the substitution
      debug(2,"and the unifiers are:")
      var reduced_unifiers : List[Substitution[FOLTerm]] = Nil
      for (u<-unifiers) {
        debug(2,"$"+u+"$")
        //val splitted : Tuple2[List[(FOLVar,FOLTerm)], List[(FOLVar,FOLTerm)]] = (u.mapFOL.partition(term_context contains _._1)).asInstanceOf[Tuple2[List[(FOLVar,FOLTerm)], List[(FOLVar,FOLTerm)]]]
        val umap = (u.map.elements.toList).asInstanceOf[List[(FOLVar,FOLTerm)]]
        
        val in_term = umap.filter((x:(FOLVar,FOLTerm)) => (term_context contains x._1))
        debug(3,"variables in term: "+in_term)
        val not_in_term = Substitution[FOLTerm](umap.filter((x:(FOLVar,FOLTerm)) => !(term_context contains x._1)))
        val in_term_reduced = in_term map ((x:(FOLVar,FOLTerm))=>(x._1,not_in_term.apply(x._2)))
        //reduced_unifiers = (Substitution(not_in_term).composeFOL(Substitution(in_term))) :: reduced_unifiers
        reduced_unifiers = Substitution[FOLTerm](in_term_reduced) :: reduced_unifiers
      }

      reduced_unifiers
    }
  }


  def calculateSums(basis:List[Vector], vlhs : Vector, vrhs : Vector, invariant : (Vector=>Boolean)) = {
    val sums = new HashMap[Vector,List[(Int, List[Vector])]]
    var oldnewest : List[(Int, Vector,List[Vector])] = Nil
    var newest : List[(Int, Vector, List[Vector])] = Nil

    for (b<-basis) {
      val weight = vector_weight(vlhs,b)
      sums(b) = List((weight,List(b)))
      newest = (weight,b,List(b)) :: newest
    }

    val maxweight = calculateMaxWeight(vlhs,vrhs)
    debug(1,"upper bound to sum of vectors: "+maxweight)

    while (newest.size > 0) {
      oldnewest = newest
      newest = Nil

      for (v <- oldnewest) {
        val candidates = basis map (x => (vector_weight(vlhs,x) + v._1 , x + v._2, x :: v._3  ))

        for (candidate <- candidates) {
          val (weight,sum,vectors) = candidate
          val entry : (Int, List[Vector]) = (weight, vectors sort Vector.lex_<)
          val newest_entry : (Int, Vector, List[Vector]) = (weight, sum, entry._2)

          if (weight<=maxweight) { //drop any sum that is too large
            if (sums.contains(sum)) {
              // if the linear combination was already generated, add it to the list
              val l : List[(Int,List[Vector])] = sums(sum)
              if (! l.contains(entry))
                sums(sum) = entry :: l
            } else {
              // else create a new entry and calculate possible new linear combinations
              sums(sum) = List(entry)
              //if (weight < maxweight && sum.anyeqzero && invariant)
              if (invariant(sum)) //TODO: check if the anyeqzero is correct, the invariant has to be true anyway
                newest = newest_entry :: newest
            }
          }
        }
      }
    }

    sums
  }

  /* this is rather inefficient, but generates fewer solutions */
  def calculateSums_new(basis:List[Vector], vlhs : Vector, vrhs : Vector, invariant : (Vector=>Boolean)) = {
    val sums = new HashMap[Vector,List[(Int, List[Vector])]]
    val maxweight = calculateMaxWeight(vlhs,vrhs)
    debug(1,"upper bound to sum of vectors: "+maxweight)
    val zero = basis(0).zero
    val ps = powerset(basis)
    val pswithsums = ps map ((x:List[Vector])=>{val sum = vectorSum(x,zero); (sum,x,vector_weight(vlhs,sum))})
    var solutions=0
    for (i<-pswithsums){
      debug(1,"fullsum  "+i._1+" weight="+i._3+" list="+i._2)
      solutions += i._2.length
    }
    debug(1,"# of solutions "+solutions)
    val ps_inv = pswithsums filter ((x:(Vector,List[Vector],Int))=>invariant(x._1) && (x._3<=maxweight) && (x._3>0))

    for (p <- ps_inv) {
      val (sum,vs,weight) = p
      if (sums contains sum) {
        val list = sums(sum)
        sums(sum) = (weight,vs) :: list
      } else {
        sums(sum) = List((weight,vs)) 
      }
    }
    sums
  }

    def removeSubsumedVectors_new(arg:List[Vector], weight : Vector) : List[Vector] = {
      var removed :List[Vector] = Nil
      val sortedarg = arg sort (_ * weight < _ * weight)
      debug(1,"sorted list by "+ weight +" is "+sortedarg)
      for (v<- sortedarg) {
        if (! linearlydependent_on(v,removed)) {
          removed = v :: removed
          debug(1,"adding "+v+" to result list")
        } else {
          debug(1,"throwing away "+v)
        }

      }
      removed
    }

    def linearlydependent_on(v:Vector, list:List[Vector]) : Boolean = {
      var changed = true
      var vs : List[Vector] = List(v)
      while (changed) {
        changed = false
        var newones : List[Vector] = Nil
        for (i <- vs)
          newones = newones ::: (list map (i - _))
        debug(4,"newones="+newones)
        if (newones contains v.zero) {
          debug(4,""+v+" is linearly dependent on "+list)
          return true
        }

        val newonesgz = newones filter geqzero
        if (newonesgz.length > 0) {
          changed = true
          vs = newonesgz
          debug(3,("v="+v+" vs="+vs))
        }
      }

      return false
    }


  /* convert list of variable symbols to a term f(x_1,f(x_2, ...)) */
  def listToTerm(function: ConstantSymbolA, terms:List[VariableSymbolA]) : FOLTerm = {
    terms match {
      case x::Nil => FOLVar(x)
      case x::xs => Function(function, List(FOLVar(x),listToTerm(function,xs)))
      case Nil =>
        if (is_ac1) {
          unit_constant
        } else {
          throw new Exception("cannot convert empty list to term, there is no unit element!")
        }
    }
  }

  def composable_by(v:Vector, vs:List[Vector]) : Boolean = {
    vs match {
      case Nil => false
      case _ =>
        val reduced = (vs map (_ - v))
        if (reduced contains v.zero)
          true
        else {
          composable_by(v, reduced filter gzero)
        }
    }

  }

  def vector_weight(vlhs:Vector, v:Vector ) : Int = vlhs * Vector(v.vector slice(0, vlhs.length))

  def product(l:List[Int]) = l.foldLeft (1) (_*_)
  def min(x:Int,y:Int) = if (x<y) x else y
  def max(x:Int,y:Int) = if (x>y) x else y

  def calculateMaxWeight(l : Vector, r : Vector) : Int = {
    var maxab = 0
    var lcm_act = 0
    for (i<-l.vector)
      for (j<-r.vector) {
        lcm_act = lcm(i,j)
        if (lcm_act>maxab)
          maxab = lcm_act
      }
    return max(l.length,r.length) * maxab
  }
  
  def calculateMaxWeight_new(l : Vector, r : Vector) : Int = {

    return max(l.length,r.length) * max(lcm(l.vector),lcm(r.vector))
  }

  def gcd(x :Int, y:Int) = {
    //Euclidian Algorithm
    var m = if (x<y) x else y
    var n = if (x<y) y else x
    var temp = 0
    while (n != 0) {
      temp = m % n
      m = n
      n = temp
    }
    m
  }

  def lcm(x:Int,y:Int) = x*y/gcd(x,y)
  def lcm(xs : List[Int]) = xs.reduceLeft((x,y)=>x*y/gcd(x,y))
  
  
  def insertIntoSortedList[A](lt_pred: (A,A) => Boolean, v:A,l:List[A] ) : List[A] = {
    l match {
      case Nil => List(v)
      case x :: xs =>
        if (lt_pred(v,x))
          v :: (x :: xs)
        else
          x :: insertIntoSortedList(lt_pred, v,xs)
    }
  }

  def nestedFunctions_toList(function: ConstantSymbolA, term : FOLTerm) : List[FOLTerm] = {
    term match {
      case v : FOLVar => List(v)
      //case c : FOLConst => List(c)
      case Function(name,args) =>
        if (name == function) {
          val join = ((x:List[FOLTerm], y:List[FOLTerm]) => x ++ y)
          args.map(nestedFunctions_toList(function,_)) reduceLeft join
        } else {
          List(Function(name,args))
        }
      case _ =>
        Nil
    }
  }

  def getVariableContext(term:FOLTerm) : List[FOLVar] = {
    term match {
      case FOLVar(_) => List(term.asInstanceOf[FOLVar])
      case FOLConst(_) => Nil
      case Function(_, args) => (args map ((x:FOLTerm) =>getVariableContext(x))) reduceLeft (_++_)
    }
  }

  def countSymbols(terms1:List[FOLTerm], terms2 : List[FOLTerm]) : List[TermCount] = {
    var result : List[TermCount] = Nil
    for(t <- terms1) {
      result = insertTerm(t,result)
    }
    for(t <- terms2) {
      result = removeTerm(t,result)
    }
    result filter (_._2 != 0)
  }

  def insertTerm(term: FOLTerm, list : List[TermCount]) : List[TermCount]= {
    list match {
      case Nil => List((term,1))
      case (lterm,count) :: rest =>
        if (term == lterm)
          (lterm,count+1) :: rest
        else
          (lterm,count) :: insertTerm(term,rest)
    }
  }

  def removeTerm(term: FOLTerm, list : List[TermCount]) : List[TermCount]= {
    list match {
      case Nil => List((term,-1))
      case (lterm,count) :: rest =>
        if (term == lterm)
          (lterm,count-1) :: rest
        else
          (lterm,count) :: removeTerm(term,rest)
    }
  }


  /* creates a function that applies a given substitution to a pair of terms */
  def makesubstitute_pair(subst:Substitution[FOLTerm]) : ( ((FOLTerm,FOLTerm)) => (FOLTerm, FOLTerm)) =
    (x : (FOLTerm, FOLTerm)) => (subst.apply(x._1), subst.apply(x._2))

  def collect(substitutions : List[Substitution[FOLTerm]], fun : (Substitution[FOLTerm]=>List[Substitution[FOLTerm]])) : List[Substitution[FOLTerm]] =
    (substitutions map fun).flatten

  def occurs(v:FOLVar, term:FOLTerm) : Boolean = {
    //println("occurs "+v+" in "+term+"?")
    term match {
      case FOLVar(w) => v==term
      case FOLConst(_) => false
      case Function(_, args) => args.foldLeft(false)(_ || occurs(v,_)) 
    }
  }

  def gzero(v : Vector) : Boolean = v.allgreaterzero
  def geqzero(v : Vector) : Boolean = v.allgreatereqzero

  /* zip for three lists */
  def zip3[A,B,C](l1:List[A], l2:List[B], l3:List[C]) : List[(A,B,C)] = {
    (l1,l2,l3) match {
      case (Nil,Nil,Nil) => Nil
      case (x::xs,y::ys,z::zs) => (x,y,z) :: zip3(xs,ys,zs)
      case _ => throw new Exception("zip3: lists not of equal length")
    }
  }

  /* creates a function, which checks if a vector is <= 1 at the given indices */
  def makeLTEQ1Filters(ns:List[Int]) : (Vector=>Boolean) = (v:Vector) =>
    (ns map (v.vector(_)<=1)).foldLeft(true)(_&&_)

  /* creates a function, which checks if a vector is <= 1 at the given indices */
  def makeEQ1Filters(ns:List[Int]) : (Vector=>Boolean) = (v:Vector) =>
    (ns map (v.vector(_)==1)).foldLeft(true)(_&&_)


  /* creates two filters that checks if the number of terms that later has to be unified with a constant or
  * function term does not exceed 1. the first function is true as long as the corresponding components are <= 1,
  * the second is true as long the corresponding components are exactly 1.
  * the first function is intended to be checked while generating solutions, the second is to be checked after
  * all solutions have been generated */
  def createConstantFilter(symbols : List[FOLTerm]) : ((Vector=>Boolean),(Vector=>Boolean)) = {
    var i : Int = 0
    var indices : List[Int] = Nil
    for (s<-symbols) {
      s match {
        case FOLVar(_) => ; //do nothing
        case FOLConst(_) => indices = i :: indices
        case Function(_,_) => indices = i :: indices
        case _ => throw new Exception("unhandled term type "+ s.getClass  +" of term "+s)
      }
      i += 1
    }
    (makeLTEQ1Filters(indices), makeEQ1Filters(indices))
  }

  def flatten(f: ConstantSymbolA, term : FOLTerm) : FOLTerm = {
    term match {
      case FOLVar(_) => term
      case FOLConst(_) => term
      case Function(fun,args) =>
        if (f==fun) {
          Function(fun, (args map ((x:FOLTerm)=>stripFunctionSymbol(f,x))).reduceRight(_:::_) map ((x:FOLTerm)=>flatten(f,x)))
        } else {
          Function(fun, args map  ((x:FOLTerm) => flatten(f,x)))
        }
    }
  }

  def stripFunctionSymbol(f: ConstantSymbolA, term : FOLTerm) : List[FOLTerm] = {
    term match {
      case Function(fun, args) =>
        if (f == fun)
          (args map ((x:FOLTerm)=>stripFunctionSymbol(f,x))).reduceRight(_:::_)
        else
          List(term)
      case _ => List(term)
    }
  }

  def powerset[A](l:List[A]) : List[List[A]] = {
    l match {
      case x::xs =>
        val pxs = powerset(xs)
        pxs ::: (pxs map (x::_))
      case Nil => List(Nil)
    }
  }

  def vectorSum(l:List[Vector], zero:Vector) : Vector = l.foldLeft(zero)(_+_)

  
  
}