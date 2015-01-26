package at.logic.parsing.language.tptp

import at.logic.language.hol._
import at.logic.language.lambda.types._
import at.logic.calculi.lk.base.{FSequent, LKProof}
import at.logic.language.hol.logicSymbols.{EqSymbol, LogicalSymbolA}

/**
 * Created by marty on 12/10/13.
 */
object TPTPHOLExporter extends TPTPHOLExporter
class TPTPHOLExporter {
  def apply(l : List[FSequent]) : String = {
    require(l.nonEmpty, "Cannot export an empty sequent list!")
    val (vs, vnames, cs, cnames) = createNamesFromSequent(l)

    printStatistics(vnames,cnames)

    var index = 0
    val vdecs_ = for(v <- vs) yield {
      index = index +1
      thf_type_dec(index, v, vnames) + "\n"
    }

    val vdecs = vdecs_.foldLeft("")(_ ++ _)

    val cdecs_ = for (c <- cs if c.sym != EqSymbol) yield {  //need to exclude the predefined constant =
      index = index +1
      thf_type_dec(index, c, cnames) + "\n"
    }
    val cdecs = cdecs_.foldLeft("")(_ ++ _)

//    val sdecs_ = for (fs <- l) yield {
//      index = index +1
//      thf_sequent_dec(index, fs, vnames, cnames) + "\n"
//    }
//    val sdecs = sdecs_.foldLeft("")(_ ++ _)
    val negClauses = Neg(conj(l.map(closedFormula)))
    index = index +1
//    val sdecs = List(thf_formula_dec(index, negClauses, vnames, cnames))
    /* we cannot export negated conjectures, since leo 2 needs at least one positive conjecture -
       therefore we put the negation in manually */
    val sdecs = l.map(x => {
        index = index + 1
        thf_formula_dec(index, Neg(closedFormula(x)), vnames, cnames)
    } )



    //"% variable type declarations\n" + vdecs +
      "% constant type declarations\n" + cdecs +
      "% sequents\n" + sdecs.foldLeft("")((s,x) => s + x + "\n")
  }

  def printStatistics(vnames : NameMap, cnames : CNameMap) : Unit = {
    if (cnames.isEmpty && vnames.isEmpty) {
      println("% No symbol translation necessary!")
      return ()
    };
    println("% Symbol translation table for THF export:")
    val csyms = cnames.keySet.toList.map({ case HOLConst(s,_) => s})
    val vsyms = vnames.keySet.toList.map({ case HOLVar(s,_) => s})

    val width = (vsyms++csyms).sortWith((x,y) => y.size < x.size).head.size

    for ((c,s) <- cnames) {
      val sym = c.sym.toString
      if (sym != s) {
        print("%   ")
        print(sym)
        for (i <- sym.size to (width + 1)) print(" ")
        print(" -> ")
        print(s)
        println()
      }
    }

    val cunchanged = for ((c,s) <- cnames; if (c.sym.toString == s)) yield { s }
    if (cunchanged.nonEmpty) println("% Unchanged constants: "+cunchanged.mkString(","))

    println("% ")

    for ((c,s) <- vnames) {
      val sym = c.sym.toString
      if (sym != s) {
        print("%   ")
        print(sym)
        for (i <- sym.size to (width + 1)) print(" ")
        print(" -> ")
        print(s)
        println()
      }
    }

    val vunchanged = for ((c,s) <- vnames; if (c.sym.toString == s)) yield { s }
    if (vunchanged.nonEmpty) println("% Unchanged variables: "+vunchanged.mkString(","))

  }


  type NameMap = Map[HOLVar, String]
  val emptyNameMap = Map[HOLVar, String]()
  type CNameMap = Map[HOLConst, String]
  val emptyCNameMap = Map[HOLConst, String]()

  def createFormula(f:HOLExpression, map : Map[HOLVar,String]) = f match {
    case HOLVar(_,_) => map(f.asInstanceOf[HOLVar])
  }

  def createNamesFromSequent(l: List[FSequent]) : (List[HOLVar], NameMap, List[HOLConst], CNameMap) = {
    val vs = l.foldLeft(Set[HOLVar]())((set, fs) =>  getVars(fs.toFormula, set)  ).toList
    val cs = l.foldLeft(Set[HOLConst]())((set, fs) =>  getConsts(fs.toFormula, set)  ).toList
    (vs, createNamesFromVar(vs), cs, createNamesFromConst(cs))
  }

  def createNamesFromVar(l : List[HOLVar]) : NameMap = l.foldLeft(emptyNameMap)( (map, v) => {
    if (map contains v)
      map
    else {
      val name =  mkVarName(v.name.toString(), map)
      map + ((v,name))
    }
  }
  )

  def closedFormula(fs : FSequent) : HOLFormula = {
    val f = fs.toFormula
    freeVariables(f).foldRight(f)( (v,g) => AllVar(v,g) )
  }

  def conj(l:List[HOLFormula]) : HOLFormula = l match {
    case Nil =>
      throw new Exception("Empty sequent list given to export!")
    case x::Nil =>
      x
    case x::xs =>
      And(x, conj(xs))
  }

  def createNamesFromConst(l : List[HOLConst]) : CNameMap = l.foldLeft(emptyCNameMap)( (map, v) => {
    if (map contains v)
      map
    else {
      val name = mkConstName(v.name.toString(), map)
      map + ((v,name))
    }
  }
  )

  def thf_sequent_dec(i:Int, f:FSequent, vmap : NameMap, cmap : CNameMap) = {
    "thf("+i+", conjecture, ["+
      (f.antecedent.map(f => thf_formula(f,vmap,cmap)).mkString(",")) +
     "] --> [" +
      (f.succedent.map(f => thf_formula(f,vmap,cmap)).mkString(",")) +
    "] )."
  }

  def thf_formula_dec(i:Int, f:HOLFormula, vmap : NameMap, cmap : CNameMap) = {
    "thf("+i+", conjecture, "+ thf_formula(f,vmap,cmap, true) +" )."
  }

  def thf_negformula_dec(i:Int, f:HOLFormula, vmap : NameMap, cmap : CNameMap) = {
    "thf("+i+", negated_conjecture, "+ thf_formula(f,vmap,cmap,true) +" )."
  }


  private def addparens(str:String, cond : Boolean) = if (cond) "("+str+")" else str
  def thf_formula(f:HOLExpression, vmap : NameMap, cmap : CNameMap, outermost : Boolean = false) : String = {
    f match {
      case Neg(x) => addparens(" ~"+thf_formula(x, vmap, cmap), !outermost)
      case And(x,y) => addparens(thf_formula(x, vmap, cmap) +" & " +thf_formula(y, vmap, cmap), !outermost)
      case Or(x,y) => addparens(thf_formula(x, vmap, cmap) +" | " +thf_formula(y, vmap, cmap), !outermost)
      case Imp(x,y) => addparens(thf_formula(x, vmap, cmap) +" => " +thf_formula(y, vmap, cmap), !outermost)
      case AllVar(x,t) => addparens("!["+ vmap(x) +" : "+getTypeString(x.exptype)+"] : ("+ thf_formula(t,vmap,cmap)+")", !outermost)
      case ExVar(x,t) => addparens("?["+ vmap(x) +" : "+getTypeString(x.exptype)+"] : ("+ thf_formula(t,vmap,cmap)+")", !outermost)
      case Equation(x,y) => addparens(thf_formula(x, vmap,cmap) +" = " + thf_formula(y, vmap,cmap), !outermost)
      case HOLAbs(x,t) => addparens( "^["+ vmap(x) +" : "+getTypeString(x.exptype)+"] : ("+ thf_formula(t,vmap,cmap)+")", !outermost)
      case HOLApp(s,t) => addparens(thf_formula(s, vmap, cmap) + " @ " +thf_formula(t, vmap,cmap), !outermost)
      case HOLVar(_,_) => vmap(f.asInstanceOf[HOLVar])
      case HOLConst(_,_) => cmap(f.asInstanceOf[HOLConst])
      case _ => throw new Exception("TPTP export does not support outermost connective of "+f)
    }
  }

  def thf_type_dec(i:Int, v : HOLVar, vmap : NameMap) : String = {
    require(vmap.contains(v), "Did not generate an export name for "+v+"!")
    "thf("+i+", type, "+vmap(v) + ": "+getTypeString(v.exptype) +" )."
  }

  def thf_type_dec(i:Int, c : HOLConst, cmap : CNameMap) : String = {
    require(cmap.contains(c), "Did not generate an export name for "+c+"!")
    "thf("+i+", type, "+cmap(c) + ": "+ getTypeString(c.exptype) +" )."
  }


  def getTypeString(t : TA) : String = getTypeString(t,true)
  def getTypeString(t : TA, outer : Boolean) : String = t match {
    case Ti => "$i"
    case To => "$o"
    case t1 -> t2 if outer => getTypeString(t1, false) + " > " + getTypeString(t2, false)
    case t1 -> t2 => "(" + getTypeString(t1, false) + " > " + getTypeString(t2, false) +")"
    case _ => throw new Exception("TPTP type export for "+t+" not implemented!")
  }

  def mkVarName(str:String, map : Map[HOLVar,String]) = {
    val fstr_ = str.filter(_.toString.matches("[a-zA-Z0-9]"))
    val fstr = if (fstr_.isEmpty) {
      println("Warning: "+str+" needs to be completely replaced by a fresh variable!")
      "V"
    } else fstr_
    val prefix = if (fstr.head.isDigit) "X"+fstr
                 else fstr.head.toUpper + fstr.tail
    val values = map.toList.map(_._2)
    if (values contains prefix)
      appendPostfix(prefix,values)
    else
      prefix
  }

  def mkConstName(str:String, map : CNameMap) = {
    val fstr_ = str match {
      case "=" => "=" //equality is handled explicitly
      case "+" => "plus"
      case "-" => "minus"
      case "*" => "times"
      case "/" => "div"
      case "<" => "lt"
      case ">" => "gt"
      case _ => str.filter(_.toString.matches("[a-zA-Z0-9]"))
    }
    val fstr = if (fstr_.isEmpty) {
      println("Warning: "+str+" needs to be completely replaced by a fresh constant!")
      "c"
    } else fstr_
    val prefix = if (fstr.head.isDigit) "c"+fstr
                 else fstr.head.toLower + fstr.tail
    val values = map.toList.map(_._2)
    if (values contains prefix)
      appendPostfix(prefix,values)
    else
      prefix
  }

  def appendPostfix(str:String, l : List[String]) = {
    var i = 100
    while (l contains (str+i)) {
      i = i+1
    }
    str+i
  }

  def getVars(t:HOLExpression, set : Set[HOLVar]) : Set[HOLVar] = t match {
    case HOLConst(_,_) => set
    case HOLVar(_,_) => set + t.asInstanceOf[HOLVar]
    case HOLApp(s,t) => getVars(s, getVars(t, set))
    case HOLAbs(x,t) => getVars(t, set + x)
  }

  def getConsts(t:HOLExpression, set : Set[HOLConst]) : Set[HOLConst] = t match {
    case HOLConst(_,_) =>
      val c = t.asInstanceOf[HOLConst]
      if (c.sym.isInstanceOf[LogicalSymbolA])
        set
      else
        set + c
    case HOLVar(_,_) => set
    case HOLApp(s,t) => getConsts(s, getConsts(t, set))
    case HOLAbs(x,t) => getConsts(t, set)
  }




}