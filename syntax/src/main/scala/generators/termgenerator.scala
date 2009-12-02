/* Generator for First Order Terms
 * function symbols with the same name but different arity will not be constructed */

package at.logic.utils.generators

import scala.util.Random
import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.hol.logicSymbols._


case class Language(val vs:List[(VariableSymbolA,Int)], val cs:List[(ConstantSymbolA,Int)], val fs:List[(ConstantSymbolA,Int)]) {
   override def equals(arg : Any) = {
        arg match {
            case Language(vs_, cs_, fs_) =>
                (vs_ == vs) && (cs_ == cs) && (fs_ == fs)
            case _ => false
        }
   }
}

object Language {
    def tupleFromStrings( tuple : (List[String],List[String],List[String]) ) = {
        val vs = tuple._1.map((x:String)=> (new VariableStringSymbol(x),1)  )
        val cs = tuple._2.map((x:String)=> (new ConstantStringSymbol(x),1)  )
        val fs = tuple._3.map((x:String)=> (new ConstantStringSymbol(x),1)  )
        (vs,cs,fs)
   }
       
   implicit def languageFromTuple( tuple : (List[(VariableSymbolA,Int)], List[(ConstantSymbolA,Int)],List[(ConstantSymbolA,Int)]) ) =
       new Language(tuple._1,tuple._2, tuple._3)
   implicit def tupleFromLanguage( lang : Language ) = (lang.vs, lang.cs, lang.fs)


    def flattenTerm(t:FOLTerm) : List[FOLTerm]= {
        t match {
            case x : FOLVar => List(x)
            case x : FOLConst => List(x)
            case Function(x,params) =>
                val fun = ((f : List[FOLTerm], list : List[FOLTerm]) => {f ++ list}) // list concatenation
                val l1 = params.map(flattenTerm)       // flatten the subterms
                l1.foldRight[List[FOLTerm]](List(FOLConst(x)))(fun)  // concatenate the function symbol and the lists
        }
    }
    /*
   def prefixFoldLeftTerm[A,B] : (FOLTerm, (FOLTerm => B),((B, FOLTerm) => B),(B) => List[B]) =
     ((t:FOLTerm, f:(FOLTerm => B),g: ((B, FOLTerm) => B), h:(B)) => {
        t match {
                            case x : FOLVar => List(f(x))
                            case x : FOLConst => List(f(x))
                            case Function(x,params) =>
                                val l = (f(FOLConst(x))::Nil)
                                val r = (params.foldLeft(h)(g))
                                l :: List(r)
                        }
         })
     */

   def printTerm[A,B] : (FOLTerm => String) =
     ((t:FOLTerm) => {
        t match {
            case x : FOLVar => x.name.toString
            case x : FOLConst => x.name.toString
            case Function(x,params) =>
                                var s = x.toString+"("
                                var count = params.length-1
                                for (p<-params) {
                                    s += printTerm(p)
                                    if (count>0)
                                        s += ", "
                                    count -= 1
                                }
                                s +=")"
                                s
            }
         })
}


class FOLtermGenerator {
    

    var random : Random = null
    var count = 0 // every generated variable, constant symbol

    def apply(seed : Int) = new FOLtermGenerator(seed)

    def this(seed : Int) = {
        this()
        random = new Random(seed);
    }

    /* generates a given number of different variable symbols
        returns a triple of variable, constant and function symbols with
        corresponding arity*/
    def generateSymbols(vars : Int, consts :Int, functions : Int, maxArity : Int) :
        (List[(VariableSymbolA,Int)], List[(ConstantSymbolA,Int)],List[(ConstantSymbolA,Int)]) = {
        var vs : List[(VariableSymbolA,Int)] = Nil
        var cs : List[(ConstantSymbolA,Int)] = Nil
        var fs : List[(ConstantSymbolA,Int)] = Nil
        for (i <- 0 until vars) {
             vs = (new VariableStringSymbol(generateVariableName),0) :: vs
        }
        for (i <- 0 until consts) {
             cs = (new ConstantStringSymbol(generateConstantName),0) :: cs
        }
        for (i <- 0 until functions) {
            fs = (new ConstantStringSymbol(generateFunctionName),1+random.nextInt(maxArity)) :: fs
        }
        
        (vs,cs,fs)
    }


    def generateVariableName() = {
        count += 1
        "x_" + count
    }

    def generateConstantName() = {
        count += 1
        "c_" + count
    }
    def generateFunctionName() = {
        count += 1
        "f_" + count
    }


    def generateVariable(lang : Language) : FOLTerm = {
        val position = random.nextInt(lang.vs.length)
        FOLVar(lang.vs(position)._1 )
    }

    def generateConstant(lang : Language) : FOLTerm =
    {
        val position = random.nextInt(lang.cs.length)
        FOLConst(lang.cs(position)._1)
    }

    /* generates a new function term from a given language, with a chance of
        nestedFunProb / 100 of having a nested function as parameter term,
        nestedConst /100 of having a constant term and
        a variable else
        maxdepth is the maximum term depth */
    def generateFunction(lang : Language, pNestedFun : Int, pNestedConst : Int, maxdepth : Int) : FOLTerm = {
        val position = random.nextInt(lang.fs.length)
        val symbol = lang.fs(position)
        var args : List[FOLTerm] = Nil
        for (j<-0 until symbol._2) {
            var p = random.nextInt(100)
            if ((p< pNestedFun) && (maxdepth>0)) {
                args = generateFunction(lang,pNestedFun,pNestedConst, maxdepth-1) :: args
            } else if (p< pNestedConst+pNestedFun) {
                args = generateConstant(lang) :: args
            } else /* variable */ {
                args = generateVariable(lang) :: args
            }
        }

        Function(symbol._1.asInstanceOf[ConstantSymbolA], args);

    }




}