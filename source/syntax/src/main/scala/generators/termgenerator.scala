/* Generator for First Order Terms
 * function symbols with the same name but different arity will not be constructed */

package at.logic.utils.generators

import scala.util.Random
import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.hol.logicSymbols._


case class Language(val vs:List[SymbolA], val cs:List[SymbolA], val fs:List[SymbolA]) {
   override def equals(arg : Any) = {
        arg match {
            case Language(vs_, cs_, fs_) => (vs_ == vs) && (cs_ == cs) && (fs_ == fs)
            case _ => false
        }
   }
}

object Language {
   implicit def languageFromTuple( tuple : (List[SymbolA],List[SymbolA],List[SymbolA]) ) =
       new Language(tuple._1,tuple._2,tuple._3)
   implicit def tupleFromLanguage( lang : Language ) = (lang.vs, lang.cs, lang.fs)
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
        returns a triple of constants, functions and functions */
    def generateSymbols(vars : Int, consts :Int, functions : Int) :
        (List[SymbolA], List[SymbolA], List[SymbolA]) = {
        var vs : List[SymbolA] = Nil
        var cs : List[SymbolA] = Nil
        var fs : List[SymbolA] = Nil
        for (i <- 0 until vars) {
             vs = new VariableStringSymbol(generateVariableName) :: vs
        }
        for (i <- 0 until consts) {
             cs = new VariableStringSymbol(generateConstantName) :: cs
        }
        for (i <- 0 until functions) {
             fs = new VariableStringSymbol(generateVariableName) :: fs
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


    def generateVariable() = {
        var x = new VariableStringSymbol(generateVariableName) ;
        FOLFactory.createVar(x, i)
    }

    def generateConstant() =
    {
        count += 1;
        var P = new ConstantStringSymbol( "c_"+count);
        FOLFactory.createVar(P, Definitions.i);        
    }


}