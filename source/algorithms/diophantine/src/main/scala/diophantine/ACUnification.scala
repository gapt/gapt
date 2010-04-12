package diophantine

import at.logic.language.hol.logicSymbols.{ConstantStringSymbol, ConstantSymbolA}
import at.logic.language.fol._
import at.logic.algorithms.diophantine.{Vector, LankfordSolver}
import at.logic.language.lambda.symbols.{VariableSymbolA, VariableStringSymbol}
import substitutions.Substitution
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

  def debug(level:Int, msg:String) = if (debuglevel>=level) println("DEBUG: "+msg)

  def getFreshVariable() : VariableSymbolA = { maxindex += 1; VariableStringSymbol(constant_prefix+maxindex) }

  def unify(function: ConstantSymbolA, term1 : FOLTerm, term2 : FOLTerm) : Option[List[Substitution]] = {
    val mgus = unify(function, List((term1, term2)), List(Substitution()) )
    mgus match {
      case Nil => debug(1,"Found no unifier!"); None;
      case _   => for (mgu<-mgus) debug(1,"found unifier: "+mgu); Some(mgus)}
  }

  def unify(function: ConstantSymbolA,
            terms : List[(FOLTerm,FOLTerm)],
            substs : List[Substitution]) : List[Substitution] = {
    debug(3,"unifying "+terms+" substitutions are: "+substs)
    terms match {
      case (term1,term2) :: rest =>
        term1 match {
          // comparing constant to sthg else
          case FOLConst(c1) =>
            term2 match {
               // if the two constants are equal, the substitution is not changed, else not unifiable 
              case FOLConst(c2) =>
                if (c1==c2) collect(substs, ((s:Substitution) => unify(function, rest, List(s))))
                else Nil
              // second one is a var => flip & variable elimination
              case FOLVar(v) =>
                val ve = Substitution(term2.asInstanceOf[FOLVar],term1)
                val newterms = rest map makesubstitute_pair(ve)
                collect(substs, (s:Substitution) => unify(function, newterms, List(ve concatFOL s)))
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
                  collect(acunivs, ((acu:Substitution) =>
                    collect(substs, ((subst:Substitution) =>
                      unify(function, rest map makesubstitute_pair(subst), List((acu concatFOL subst))))
                   )))
                } else  {
                  //non ac unification => decomposition
                  collect(substs , (s:Substitution) => unify(function, (args1 zip args2):::rest, List(s)))
                }
              // variable as second term: flip & variable elimination
              case FOLVar(v) =>
                //occurs check
                if (occurs(term2.asInstanceOf[FOLVar], term1)) {
                  Nil
                } else {
                  val ve = Substitution(term2.asInstanceOf[FOLVar],term1)
                  val newterms = rest map makesubstitute_pair(ve)
                  collect(substs, (s:Substitution) => unify(function, newterms, List((ve concatFOL s))))
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
                  collect(substs,(s:Substitution) => unify(function, rest, List(s)))
                } else {
                  val ve = Substitution(term1.asInstanceOf[FOLVar],term2)
                  val newterms = rest map makesubstitute_pair(ve)
                  collect(substs,(s:Substitution) => unify(function, newterms, List((ve concatFOL s).asInstanceOf[Substitution])))
                }

              case _ =>
                //occurs check
                if (occurs(term1.asInstanceOf[FOLVar], term2)) {
                  Nil
                } else {
                  val ve = Substitution(term1.asInstanceOf[FOLVar],term2)
                  val newterms = rest map makesubstitute_pair(ve)
                  collect(substs, (s:Substitution) => unify(function, newterms, List((ve concatFOL s).asInstanceOf[Substitution])))
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
  

  def ac_unify(function: ConstantSymbolA, term1 : FOLTerm, term2 : FOLTerm) : List[Substitution] = {
    val counted_symbols = countSymbols(nestedFunctions_toList(function,term1), nestedFunctions_toList(function,term2))
    val (ts1,count1) = List unzip counted_symbols
    //println("term symbols: "+ts1)
    //println(count1)

    val (lhs,rhs) = (counted_symbols partition (_._2 >0)) // this works because countSymbols olny returns values != 0
    val vlhs = Vector(lhs map (_._2))
    val vrhs = Vector(rhs map (_._2 * -1))

    val vlhs_length = vlhs.length
    val vrhs_length = vrhs.length

    if ((lhs == Nil) || (rhs == Nil)) {
      Nil
    }
    else {
      val basis = LankfordSolver solve (vlhs,vrhs)
      val sums = calculateSums(basis, vlhs, vrhs)


      var results : List[Vector] = Nil
      if (is_ac1) {
        results = sums.keySet.toList //AC1 Unification does not filter out
      } else {
        // ac unification filters
        for (v <- sums.toList ) {
          if (gzero(v._1))
            results = v._1 ::results
        }
      }

      // remove vectors which are subsumed by smaller vectors
      results = removeSubsumedVectors(results)

      // associate every base vector to a fresh logical variable
      val varmap = new HashMap[Vector,VariableSymbolA]

      for (b<-basis) {
        val v : VariableSymbolA = getFreshVariable()
        debug(3,""+b+"->"+v)
        varmap(b) = v 
      }

      //some helper functions, could be factored out
      def extract(pair:(Int,List[Vector])) : List[Vector] = pair._2

      //def ntimes[A](n:Int,p:(List[A],List[A])=>List[A],l:List[A]) : List[A] =
      //  if (n <= 0) Nil else l ::: ntimes(n-1,l)
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

      debug(2,"ac unification preresults:"+results)
      //convert results to list of terms
      var converted : List[List[FOLTerm]] = Nil
      for (r <- results)
        for (i <- sums(r).map(extract))
          converted = createVectors(varmap, i) :: converted
      


      debug(1,"ac unification results: "+converted)
      def zip3[A,B,C](l1:List[A], l2:List[B], l3:List[C]) : List[(A,B,C)] = {
        (l1,l2,l3) match {
          case (Nil,Nil,Nil) => Nil
          case (x::xs,y::ys,z::zs) => (x,y,z) :: zip3(xs,ys,zs)
          case _ => throw new Exception("zip3: lists not of equal length")
        }
      }

      var unified_terms : List[List[FOLTerm]] = Nil
      var unifiers : List[Substitution] = Nil
      for (c<-converted) {
        val zc = ts1 zip c
        //println("finding unifier for: "+zc)
        val us = unify(function, zc, List(Substitution()) )
        for (unifier <- us) {
            val uterm : List[FOLTerm] = ts1 map ((x:FOLTerm)=>unifier.applyFOL(x).asInstanceOf[FOLTerm])
            //println("yay found one:" + uterm)
            //unifiers = subst :: unifiers
            unifiers = unifier :: unifiers
            unified_terms = uterm :: unified_terms 
        }
      }

      val term_context = (ts1 map ((x:FOLTerm) => getVariableContext(x))) reduceLeft (_++_)

      //remove variables not in the original term from the substitution
      debug(1,"and the unifiers are:")
      var reduced_unifiers : List[Substitution] = Nil
      for (u<-unifiers) {
        debug(1,""+u)
        //val splitted : Tuple2[List[(FOLVar,FOLTerm)], List[(FOLVar,FOLTerm)]] = (u.mapFOL.partition(term_context contains _._1)).asInstanceOf[Tuple2[List[(FOLVar,FOLTerm)], List[(FOLVar,FOLTerm)]]]
        val umap = (u.mapFOL.elements.toList).asInstanceOf[List[(FOLVar,FOLTerm)]]
        
        val in_term = umap.filter((x:(FOLVar,FOLTerm)) => (term_context contains x._1))
        println(in_term)
        val not_in_term = Substitution(umap.filter((x:(FOLVar,FOLTerm)) => !(term_context contains x._1)))
        val in_term_reduced = in_term map ((x:(FOLVar,FOLTerm))=>(x._1,not_in_term.applyFOL(x._2)))
        //reduced_unifiers = (Substitution(not_in_term).composeFOL(Substitution(in_term))) :: reduced_unifiers
        reduced_unifiers = Substitution(in_term_reduced) :: reduced_unifiers
      }

      reduced_unifiers
    }
  }


  def calculateSums(basis:List[Vector], vlhs : Vector, vrhs : Vector) = {
    val sums = new HashMap[Vector,List[(Int, List[Vector])]]
    var oldnewest : List[(Int, Vector,List[Vector])] = Nil
    var newest : List[(Int, Vector, List[Vector])] = Nil

    for (b<-basis) {
      val weight = vector_weight(vlhs,b)
      sums(b) = List((weight,List(b)))
      newest = (weight,b,List(b)) :: newest
    }

    val maxweight = calculateMaxWeight(vlhs,vrhs)
    //println(maxweight)

    while (newest.size > 0) {
      oldnewest = newest
      newest = Nil

      for (v <- oldnewest) {
        val candidates = basis map (x => (vector_weight(vlhs,x) + v._1 , x + v._2, x :: v._3  ))

        for (candidate <- candidates) {
          val (weight,sum,vectors) = candidate
          val entry : (Int, List[Vector]) = (weight, vectors sort Vector.lex_<)
          val newest_entry : (Int, Vector, List[Vector]) = (weight, sum, entry._2)


          if (sums.contains(sum)) {
            val l : List[(Int,List[Vector])] = sums(sum)
            if (! l.contains(entry))
              sums(sum) = entry :: l
          } else {
            sums(sum) = List(entry)
            if (weight < maxweight && sum.anyeqzero)
              newest = newest_entry :: newest
          }
        }
      }
    }

    sums
  }

  def removeSubsumedVectors(arg:List[Vector]) : List[Vector] = {
    var temp = arg sort Vector.lex_<
    var results : List[Vector] = Nil
    while (temp != Nil) {
      temp match {
        case x::xs =>
          results = x :: results
          temp = xs filter (y=> !(y>=x))
        case Nil =>
          throw new Exception("Error in AC Unification algorithm: list is empty even if it may not be")
      }
    }
    results
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
          def gzero(v:Vector) = v.allgreaterzero
          composable_by(v, reduced filter gzero)
        }
    }

  }

  def vector_weight(vlhs:Vector, v:Vector ) : Int = vlhs * Vector(v.vector slice(0, vlhs.length))

  def calculateMaxWeight(l : Vector, r : Vector) : Int = {
    def product(l:List[Int]) = l.foldLeft (1) (_*_)

    def min(x:Int,y:Int) = if (x<y) x else y
    def max(x:Int,y:Int) = if (x>y) x else y
    
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

  def substitute_pair(subst : Substitution, x : (FOLTerm,FOLTerm)) : (FOLTerm,FOLTerm) = (subst.applyFOL(x._1).asInstanceOf[FOLTerm], subst.applyFOL(x._2).asInstanceOf[FOLTerm])
  def makesubstitute_pair(subst:Substitution) : ( ((FOLTerm,FOLTerm)) => (FOLTerm, FOLTerm)) = substitute_pair(subst,_)

  def collect(substitutions : List[Substitution], fun : (Substitution=>List[Substitution])) : List[Substitution] =
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
  
}