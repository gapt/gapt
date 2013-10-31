package at.logic.algorithms.hlk

import at.logic.calculi.lk.base.LKProof
import at.logic.language.lambda.typedLambdaCalculus.{Abs, App, Var, LambdaExpression}
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.hol.logicSymbols.{LogicalSymbolsA, ConstantSymbolA}
import at.logic.language.hol._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.definitionRules.{DefinitionRightRule, DefinitionLeftRule}


object HybridLatexExporter {
  def nameToLatexString(s:String, escapebrack : Boolean = true) : String = {
    val s1 = at.logic.utils.latex.nameToLatexString(s)
    //val s2 = if (escapebrack) s1.replaceAll("\\[","(").replaceAll("\\]",")") else s1
    val s2 = if (s == "!=") "\\neq" else s1
    val s3 = if (s2 != "-") s2.replaceAll("-","") else s2
    s3
  }


  def apply(lkp : LKProof) = {
    val declarations = generateDeclarations(lkp)
    val proofs = generateProof(lkp, "")

    declarations + "\n\\CONSTDEC{THEPROOF}{o}\n\n" + proofs + "\\CONTINUEWITH{THEPROOF}"
  }

  def generateDeclarations(p: LKProof) : String= {
    val formulas = p.nodes.flatMap(_.asInstanceOf[LKProof].root.toFSequent.formulas)
    val types = formulas.foldLeft(Map[SymbolA,TA]())((map,f) => getTypes(f, map)).filterNot(_._1.isInstanceOf[LogicalSymbolsA])
    val (vars,   rest1) = types.partition( p => p._1.isInstanceOf[VariableSymbolA])
    //val (defs, rest2) = rest1.partition( p => p._1.isInstanceOf[ConstantSymbolA] && p._1.toString.contains("["))
    val (consts, rest3) = rest1.partition( p => p._1.isInstanceOf[ConstantSymbolA])
    require(rest3.isEmpty, "There are symbols which are neither variables nor constants in the formulas: "+rest3)

    val svars = vars.foldLeft(Map[String, String]())((map, p) => {
      val vname = nameToLatexString(p._1.toString)
      if (map contains vname) throw new Exception("Two different kinds of symbol share the same name!")
      map + ((vname, getTypeString(p._2)))
    })
    val sconsts = consts.foldLeft(Map[String, String]())((map, p) => {
      val vname = nameToLatexString(p._1.toString)
      if (map contains vname) throw new Exception("Two different kinds of symbol share the same name!")
      map + ((vname, getTypeString(p._2)))
    }).filterNot(_._1 == "=")
    /*
    val sdefs = defs.foldLeft(Map[String, String]())((map, p) => {
      val w = "[a-zA-Z0-9]+"
      val re= ("("+w+")\\[("+w+"(,"+w+")*"+")\\]").r
      val vname = nameToLatexString(p._1.toString, false)
      if (map contains vname) throw new Exception("Two different kinds of symbol share the same name!")
      map + ((vname, getTypeString(p._2)))
    })*/


    val rvmap = svars.foldLeft(Map[String,List[String]]())((map,p) => {
      val (name, expt) = p
      if (map contains expt)
        map + ((expt, name::map(expt)))
      else
        map + ((expt, name::Nil))
    })

    val rcmap = sconsts.foldLeft(Map[String,List[String]]())((map,p) => {
      val (name, expt) = p
      if (map contains expt)
        map + ((expt, name::map(expt)))
      else
        map + ((expt, name::Nil))
    })

    val sv = rvmap.map( x => "\\VARDEC{"+x._2.mkString(", ")+"}{"+x._1+"}")
    val sc = rcmap.map( x => "\\CONSTDEC{"+x._2.mkString(", ")+"}{"+x._1+"}")
    sv.mkString("\n") +"\n" + sc.mkString("\n")
  }

  def getTypes(exp : LambdaExpression, map : Map[SymbolA, TA]) : Map[SymbolA, TA] = exp match {
    case Var(name, exptype) =>
      if (map.contains(name)) {
        if (map(name) != exptype) throw new Exception("Symbol clash for "+name+" "+map(name)+" != "+exptype)
        map
      } else {
        map + ((name, exptype))
      }

    case App(s,t) =>
      getTypes(s, getTypes(t, map))

    case Abs(x,t) =>
      getTypes(x,getTypes(t,map))
  }

  def getTypeString(t:TA, outermost : Boolean = true) : String = t match {
    case Ti() => "i"
    case To() => "o"
    case Tindex() => "w"
    case t1 -> t2 =>
      val s = getTypeString(t1,false) + ">" + getTypeString(t2,false)
      if (outermost) s else "("+s+")"
  }

  def getFormulaString(f : HOLExpression, outermost : Boolean = true) : String = f match {
    case AllVar(x,t) =>
      "(all " + getFormulaString(x.asInstanceOf[HOLVar],false) +  " " + getFormulaString(t,false) + ")"
    case ExVar(x,t) =>
      "(exists " + getFormulaString(x.asInstanceOf[HOLVar],false) +  " " + getFormulaString(t,false) + ")"
    case Neg(t1) =>
      val str = " -" + getFormulaString(t1,false)
      if (outermost) str else "(" + str + ")"
    case And(t1,t2) =>
      val str = getFormulaString(t1,false) +  " & " + getFormulaString(t2,false)
      if (outermost) str else "(" + str + ")"
    case Or(t1,t2) =>
      val str = getFormulaString(t1,false) +  " | " + getFormulaString(t2,false)
      if (outermost) str else "(" + str + ")"
    case Imp(t1,t2) =>
      val str = getFormulaString(t1,false) +  " -> " + getFormulaString(t2,false)
      if (outermost) str else "(" + str + ")"

    case Atom(sym, args) =>
      val str : String =
        if (args.length == 2 && sym.toString.matches("""(<|>|\\leq|\\geq|=|>=|<=)"""))
          getFormulaString(args(0), false) +" "+nameToLatexString(sym.toString)+" "+getFormulaString(args(1))
        else
          nameToLatexString(sym.toString) + args.map(getFormulaString(_, false)).mkString("(",", ",")")
      if (outermost) str else "(" + str + ")"
    case Function(sym, args, _) =>
        if (args.length == 2 && sym.toString.matches("""[+\-*/]"""))
          "("+getFormulaString(args(0), false) +" "+sym.toString+" "+getFormulaString(args(1))+")"
        else {
          if (args.isEmpty)
            nameToLatexString(sym.toString)
          else
            nameToLatexString(sym.toString) + args.map(getFormulaString(_, false)).mkString("(",", ",")")
        }

    case HOLVar(v,_) => v.toString
    case HOLConst(c, _) => c.toString
    case HOLAbs(x,t) =>
      "(\\lambda " + getFormulaString(x.asInstanceOf[HOLVar],false) +  " " + getFormulaString(t,false) + ")"
    case HOLApp(s,t) =>
      "(@ " + getFormulaString(s,false) + " " + getFormulaString(t,false) + ")"

  }

  def fsequentString(fs: FSequent) : String =
    fs.antecedent.map(getFormulaString(_)).mkString("{",",","}") +fs.succedent.map(getFormulaString(_)).mkString("{",",","}")

  def generateProof(p: LKProof, s:String) : String= p match {
    case Axiom(root) =>
      "\\AX"+fsequentString(root.toFSequent)+"\n"+s
    // unary rules
    case NegLeftRule(p1,root, _,_) =>
      generateProof(p1, "\\NEGL"+fsequentString(root.toFSequent)+"\n"+s)
    case NegRightRule(p1,root, _,_) =>
      generateProof(p1, "\\NEGR"+fsequentString(root.toFSequent)+"\n"+s)
    case AndLeft1Rule(p1,root, _,_) =>
      generateProof(p1, "\\ANDL"+fsequentString(root.toFSequent)+"\n"+s)
    case AndLeft2Rule(p1,root, _,_) =>
      generateProof(p1, "\\ANDL"+fsequentString(root.toFSequent)+"\n"+s)
    case OrRight1Rule(p1,root, _,_) =>
      generateProof(p1, "\\ORR"+fsequentString(root.toFSequent)+"\n"+s)
    case OrRight2Rule(p1,root, _,_) =>
      generateProof(p1, "\\ORR"+fsequentString(root.toFSequent)+"\n"+s)
    case ImpRightRule(p1,root, _,_ , _) =>
      generateProof(p1, "\\IMPR"+fsequentString(root.toFSequent)+"\n"+s)
    //binary rules
    case AndRightRule(p1,p2, root, _,_,_) =>
      generateProof(p1, generateProof(p2, "\\ANDR"+fsequentString(root.toFSequent)+"\n"+s))
    case OrLeftRule(p1,p2, root, _,_,_) =>
      generateProof(p1, generateProof(p2, "\\ORL"+fsequentString(root.toFSequent)+"\n"+s))
    case ImpLeftRule(p1,p2, root, _,_,_) =>
      generateProof(p1, generateProof(p2, "\\IMPL"+fsequentString(root.toFSequent)+"\n"+s))
    //structural rules
    case CutRule(p1,p2, root, _,_) =>
      generateProof(p1, generateProof(p2, "\\CUT"+fsequentString(root.toFSequent)+"\n"+s))
    case WeakeningLeftRule(p1,root, _) =>
      generateProof(p1, "\\WEAKL"+fsequentString(root.toFSequent)+"\n"+s)
    case WeakeningRightRule(p1,root, _) =>
      generateProof(p1, "\\WEAKR"+fsequentString(root.toFSequent)+"\n"+s)
    case ContractionLeftRule(p1,root, _,_,_) =>
      generateProof(p1, "\\CONTRL"+fsequentString(root.toFSequent)+"\n"+s)
    case ContractionRightRule(p1,root, _,_,_) =>
      generateProof(p1, "\\CONTRR"+fsequentString(root.toFSequent)+"\n"+s)
    //quantifier rules
    case ForallLeftRule(p1,root, aux, main, term) =>
      generateProof(p1, "\\ALLL{"+ getFormulaString(term) + "}" +fsequentString(root.toFSequent)+"\n"+s)
    case ForallRightRule(p1,root, aux, main, term) =>
      generateProof(p1, "\\ALLR{"+ getFormulaString(term) + "}" +fsequentString(root.toFSequent)+"\n"+s)
    case ExistsLeftRule(p1,root, aux, main, term) =>
      generateProof(p1, "\\EXL{"+ getFormulaString(term) + "}" +fsequentString(root.toFSequent)+"\n"+s)
    case ExistsRightRule(p1,root, aux, main, term) =>
      generateProof(p1, "\\EXR{"+ getFormulaString(term) + "}" +fsequentString(root.toFSequent)+"\n"+s)
    //equality rules
    case EquationLeft1Rule(p1,p2, root, _,_,_) =>
      generateProof(p1, generateProof(p2, "\\EQL"+fsequentString(root.toFSequent)+"\n"+s))
    case EquationLeft2Rule(p1,p2, root, _,_,_) =>
      generateProof(p1, generateProof(p2, "\\EQL"+fsequentString(root.toFSequent)+"\n"+s))
    case EquationRight1Rule(p1,p2, root, _,_,_) =>
      generateProof(p1, generateProof(p2, "\\EQR"+fsequentString(root.toFSequent)+"\n"+s))
    case EquationRight2Rule(p1,p2, root, _,_,_) =>
      generateProof(p1, generateProof(p2, "\\EQR"+fsequentString(root.toFSequent)+"\n"+s))
    //definition rules
    case DefinitionLeftRule(p1,root, _,_ ) =>
      generateProof(p1, "\\DEF"+fsequentString(root.toFSequent)+"\n"+s)
    case DefinitionRightRule(p1,root, _,_ ) =>
      generateProof(p1, "\\DEF"+fsequentString(root.toFSequent)+"\n"+s)

  }

}
