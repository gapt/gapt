package at.logic.transformations.ceres.clauseSchema

import at.logic.algorithms.lk.getAncestors
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.calculi.resolution.robinson.Clause
import at.logic.calculi.slk._
import at.logic.calculi.slk.AndEquivalenceRule1._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.algorithms.shlk._
import at.logic.utils.ds.trees.LeafTree
import collection.immutable
import at.logic.language.hol._
import at.logic.language.schema._
import at.logic.language.hol.logicSymbols.{ConstantSymbolA, ConstantStringSymbol}
import at.logic.language.lambda.typedLambdaCalculus.{AppN, LambdaExpression, Var}
import at.logic.language.lambda.types.FunctionType._
import at.logic.language.lambda.types.To._
import at.logic.language.lambda.types._

  abstract class sClause {
    override def toString: String
  }

  class clauseSchema(val name: String, val args: List[Object]) extends sClause {
    override def toString:String = name+"("+printSchemaProof.formulaToString(args.head.asInstanceOf[HOLExpression])+ {args.tail.foldRight("")((x, rez) => ", "+x.toString+rez)} + ")"
  }
  object clauseSchema {
    def apply(sym: String, l: List[Object]): clauseSchema = {
      new clauseSchema(sym, l)
    }
    def unapply(c: sClause) = c match {
      case sc: clauseSchema => Some((sc.name, sc.args))
      case _ => None
    }
  }

  class sClauseVar(val name:String) extends sClause {
    override def toString = {this.name}
  }

  object sClauseVar {
    def apply(name:String): sClause = new sClauseVar(name)
    def unaply(s : sClause) = s match {
      case v:sClauseVar => Some(v.name)
      case _ => None
    }
  }

  class nonVarSclause(val ant: List[HOLFormula], val succ: List[HOLFormula]) extends sClause {
    override def toString = {
      printSchemaProof.sequentToString(Sequent(ant.map(f => defaultFormulaOccurrenceFactory.createFormulaOccurrence(f, List())), succ.map(f => defaultFormulaOccurrenceFactory.createFormulaOccurrence(f, List()))))
  //    ant + " |- " + succ
    }
  }

  object nonVarSclause {
    def apply(ant1: List[HOLFormula], succ1: List[HOLFormula]): nonVarSclause = {
      new nonVarSclause(ant1, succ1)
    }
    def unapply(c: sClause) = c match {
      case non:nonVarSclause => Some(non.ant, non.succ)
      case _ => None
    }
  }


  class sClauseComposition(val sclause1: sClause, val sclause2: sClause) extends sClause {
  //  override def toString = {sclause1 + " • " + sclause2}
    override def toString = {sclause1 + Console.BLUE+" ◦ " + Console.RESET+ sclause2}
  }

  //makes it with only one  "|-" sign, i.e. removes \circ
  object normalizeSClause {
    def apply(c: sClause): sClause = {
      val mergeNonVarSClauses = {
        val res = getNonVarSclauses(c)
        if(res.length < 2)
        res
        else
        res.tail.foldLeft(res.head)((acc, clause) => nonVarSclause(acc.asInstanceOf[nonVarSclause].ant ++ clause.asInstanceOf[nonVarSclause].ant, acc.asInstanceOf[nonVarSclause].succ ++ clause.asInstanceOf[nonVarSclause].succ)).asInstanceOf[sClause]
      }
      val sClauseVars = getSClausVars(c)
      if(sClauseVars.isEmpty)
        return mergeNonVarSClauses.asInstanceOf[nonVarSclause]
      sClauseVars.foldLeft(mergeNonVarSClauses.asInstanceOf[sClause])((acc, v) => sClauseComposition(acc, v)).asInstanceOf[sClauseComposition]
    }
    def getNonVarSclauses(c: sClause): List[sClause] = c match {
      case v:sClauseVar => List.empty[sClause]
      case non:nonVarSclause => non::Nil
      case comp:sClauseComposition =>
        getNonVarSclauses(comp.sclause1) ++ getNonVarSclauses(comp.sclause2)
    }

    def getSClausVars(c: sClause): List[sClause] = c match {
      case v:sClauseVar => v::Nil
      case non:nonVarSclause => List.empty[sClause]
      case comp:sClauseComposition =>
        getSClausVars(comp.sclause1) ++ getSClausVars(comp.sclause2)
    }
  }

  object sClauseComposition {
    def apply(scl1: sClause , scl2: sClause): sClause = new sClauseComposition(scl1, scl2)
    def unaply(s: sClause) = s match {
      case compos:sClauseComposition => Some(Pair(compos.sclause1, compos.sclause2))
      case _ => None
    }
  }


  //replace the clause variable "v" with the corresponging clause from the Map
  object replace {
    def apply(v: sClauseVar, pair: Pair[sClauseVar, sClause]): sClause = {
      if (v.name == pair._1.name)
        pair._2
      else
        v
    }
    def apply(c: sClause, varList: Map[sClauseVar, sClause]): sClause = c match {
      case v:sClauseVar if varList.keySet.contains(v) => varList.get(v).get
      case v:sClauseVar if !varList.keySet.contains(v) => throw new Exception("\nERROR 112\n!")
      case non:nonVarSclause => c
      case comp:sClauseComposition =>
        sClauseComposition(apply(comp.sclause1, varList), apply(comp.sclause2, varList))
    }
  }


  object applySubToSclause {
    def apply(sub: SchemaSubstitution3, c: sClause): sClause = {
  //    println("sub, c = "+c)
      c match {
        case v:sClauseVar => c
        case non:nonVarSclause => {
          val ant1 = non.ant.map(f => sub(f).asInstanceOf[HOLFormula])
          val succ1 = non.succ.map(f => sub(f).asInstanceOf[HOLFormula])
          nonVarSclause(ant1, succ1)
        }
        case compos:sClauseComposition => {
          sClauseComposition(apply(sub, compos.sclause1), apply(sub, compos.sclause2))
        }
        case cs:clauseSchema => {
          clauseSchema(cs.name, cs.args.map(x => {
            x match {
              case e:HOLExpression => sub(x.asInstanceOf[HOLExpression])
              case _ => x
            }
          }))
        }
        case _ => throw new Exception("\nERROR in applySubToSclause ! \n")
      }
    }
  }


  class ClauseSchemaPair(val base: sClause, val rec: sClause) {
    override def toString() = Console.GREEN+"( "+Console.RESET+base.toString +Console.GREEN+"  ;  "+Console.RESET +rec.toString+Console.GREEN+" )"+Console.RESET
    def apply(a: IntegerTerm, varListBase: Map[sClauseVar, sClause], varListRec: Map[sClauseVar, sClause], c: sClause): sClause = {
      a match {
        case IntZero() => replace(base, varListBase)
        case    _      => {
          println("\nClauseSchemaPair rec:")
          val k = IntVar(new VariableStringSymbol("k"))
          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(k, a)
          val new_subst = new SchemaSubstitution3(new_map)
          val ground_c = applySubToSclause(new_subst, c)
          val new_val = apply(Pred(a), varListBase, varListRec, c)
          val Xmap = Map[sClauseVar, sClause]() + Pair(varListBase.head._1.asInstanceOf[sClauseVar], new_val)
          replace(ground_c, Xmap)
        }
      }
    }
    def apply(k: IntegerTerm, varListBase: Map[sClauseVar, sClause]): sClause = {
      val varListRec = Map[sClauseVar, sClause]() + Pair(varListBase.head._1.asInstanceOf[sClauseVar], rec)
      apply(k, varListBase, varListRec, rec)
    }
  }
  object ClauseSchemaPair {
    def apply(b: sClause, r: sClause) = new ClauseSchemaPair(b, r)
  }


  //schematic term
  object sTermN {
    //the l.head should be of type Tindex() !
    def apply(f: String, l: List[HOLExpression]): HOLExpression = {
      require(l.head.exptype == Tindex())
      val typ = l.reverse.map(x => x.exptype).foldRight(Ti().asInstanceOf[TA])((x,t) => ->(x, t))
      val func = HOLConst(new ConstantStringSymbol(f), typ)
      return Function(func, l)
    }
    def apply(f: HOLConst, i: IntegerTerm, l: List[HOLExpression]): HOLExpression = {
      Function(f, l)
    }
    def unapply(s : HOLExpression) = s match {
      case Function(name, args, typ) if typ == Ti() && args.head.exptype == Tindex() => {
        val typ = args.map(x => x.exptype).foldLeft(Ti().asInstanceOf[TA])((x,t) => ->(x, t))
        val f = HOLConst(name.asInstanceOf[ConstantStringSymbol], typ)
        Some((f.name.toString(), args.head.asInstanceOf[HOLExpression], args.tail.asInstanceOf[List[HOLExpression]]))
      }
      case _ => None
    }
  }

  //indexed second-order variable of type: ind->i
  class fo2Var(override val name: VariableStringSymbol) extends HOLVar(name, ->(Tindex(),Ti()), None) {
    override def toString = name.toString+":"+this.exptype.toString
  }

  object fo2Var {
    def apply(name: VariableStringSymbol, i: IntegerTerm): HOLVar = {
      new fo2Var(name)
    }
    def unapply(s: HOLExpression) = s match {
      case v: fo2Var => Some(v.name)
      case _ => None
    }
  }


  class dbTRSsTermN(val map: scala.collection.mutable.Map[String, Tuple2[Tuple2[HOLExpression, HOLExpression], Tuple2[HOLExpression, HOLExpression]]])
  //the t.r.s. for the sTermN
  object dbTRSsTermN {
    def apply(term: String, base: Tuple2[HOLExpression, HOLExpression], step: Tuple2[HOLExpression, HOLExpression]): dbTRSsTermN = {
      val m = scala.collection.mutable.Map.empty[String, Tuple2[Tuple2[HOLExpression, HOLExpression], Tuple2[HOLExpression, HOLExpression]]] + Pair(term, Tuple2(base, step))
      new dbTRSsTermN(m)
    }
    def apply() = new dbTRSsTermN(scala.collection.mutable.Map.empty[String, Tuple2[Tuple2[HOLExpression, HOLExpression], Tuple2[HOLExpression, HOLExpression]]])
  }


  class dbTRSclauseSchema(val map: scala.collection.mutable.Map[String, Tuple2[Tuple2[sClause, sClause], Tuple2[sClause, sClause]]])
  //the t.r.s. for the clause schema
  object dbTRSclauseSchema {
    def apply(term: String, base: Tuple2[sClause, sClause], step: Tuple2[sClause, sClause]): dbTRSclauseSchema = {
      val m = scala.collection.mutable.Map.empty[String, Tuple2[Tuple2[sClause, sClause], Tuple2[sClause, sClause]]] + Pair(term, Tuple2(base, step))
      new dbTRSclauseSchema(m)
    }
    def apply() = new dbTRSclauseSchema(scala.collection.mutable.Map.empty[String, Tuple2[Tuple2[sClause, sClause], Tuple2[sClause, sClause]]])
  }

  object unfoldSTermN {
    def apply(t: HOLExpression, trs: dbTRSsTermN, subst: SchemaSubstitution3): HOLExpression = {
      val k = IntVar(new VariableStringSymbol("k"))
      t match {
        case sTermN(func, i, arg) if trs.map.contains(func) => {
          if (i == IntZero()) {
            println("\n\ni == 0")
            val base = trs.map.get(func).get._1._2
            base//subst(base)
          }
          else
          if (i == k)
            t
          else
            trs.map.get(func).get._2._2 match {
              case foTerm(name, arg1) => foTerm(name.asInstanceOf[HOLVar], apply(sTermN(func, Pred(i.asInstanceOf[IntegerTerm]) :: arg), trs, subst)::Nil)
            }
        }
        case sTermN(func, i, arg) => {
          println("\n\nwrong !")
          t
        }
        case foTerm(holvar, arg) => foTerm(holvar.asInstanceOf[HOLVar], apply(arg, trs, subst)::Nil)
        case _ => t//throw new Exception("\nno such case in schema/unfoldSTerm")
      }
    }
  }


//  object unfoldSchemaClause {
//    def apply(t: sClause, trsSclause: dbTRSclauseSchema, trsSterms: dbTRSsTermN, subst: SchemaSubstitution3): sClause = {
//      val k = IntVar(new VariableStringSymbol("k"))
//      t match {
//        case clauseSchema(func, i::arg) if trsSclause.map.contains(func) => {
//          if (i == IntZero()) {
//            println("\n\ni == 0")
//            val base = trsSclause.map.get(func).get._1._2
//            base//subst(base)
//          }
//          else
//          if (i == k)
//            t
//          else
//            trsSclause.map.get(func).get._2._2 match {
//              case foTerm(name, arg1) => foTerm(name.asInstanceOf[HOLVar], apply(sTermN(func, Pred(i.asInstanceOf[IntegerTerm]) :: arg), trs, subst)::Nil)
//            }
//        }
//        case sTermN(func, i, arg) => {
//          println("\n\nwrong !")
//          t
//        }
//        case foTerm(holvar, arg) => foTerm(holvar.asInstanceOf[HOLVar], apply(arg, trs, subst)::Nil)
//        case _ => t//throw new Exception("\nno such case in schema/unfoldSTerm")
//      }
//    }
//  }


  class SchemaSubstitution3(val map: scala.collection.immutable.Map[Var, HOLExpression])  {
    def apply(expression: HOLExpression): HOLExpression = {
      //    println("subst")
      expression match {
        case x:IntVar => {
          //      println("\nIntVar = "+x)
          map.get(x) match {
            case Some(t) => {
              //          println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
              t
            }
            case _ => {
              //          println(x + " Error in schema subst 1")
              x.asInstanceOf[HOLExpression]
            }
          }
        }
        case x:foVar => {
          //        println("\nfoVar = "+x)
          map.get(x) match {
            case Some(t) => {
              //          println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
              t
            }
            case _ => {
              //          println(x + " Error in schema subst 1")
              x.asInstanceOf[HOLExpression]
            }
          }
        }
  //      case IndexedPredicate(pointer @ f, l @ ts) => IndexedPredicate(pointer.name.asInstanceOf[ConstantSymbolA], apply(l.head.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[HOLExpression]
  //      case BigAnd(v, formula, init, end) => BigAnd(v, formula, apply(init.asInstanceOf[HOLExpression]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[HOLExpression]
  //      case BigOr(v, formula, init, end) =>   BigOr(v, formula, apply(init.asInstanceOf[HOLExpression]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[HOLExpression]
        case Succ(n) => Succ(apply(n).asInstanceOf[IntegerTerm]).asInstanceOf[HOLExpression]
  //      case Or(l @ left, r @ right) => Or(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
  //      case And(l @ left, r @ right) => And(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
  //      case Neg(l @ left) => Neg(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
  //      case Imp(l, r) => Imp(apply(l.asInstanceOf[T]).asInstanceOf[HOLFormula], apply(r.asInstanceOf[T]).asInstanceOf[HOLFormula]).asInstanceOf[T]
  //      case AllVar(v, f) => AllVar(v, apply(f.asInstanceOf[HOLExpression]).asInstanceOf[HOLFormula]).asInstanceOf[HOLExpression]
        case ifo: indexedFOVar => indexedFOVar(ifo.name, apply(ifo.index).asInstanceOf[IntegerTerm])
        case sTermN(name, i, args) => {
          println("sTermN = "+expression)
          sTermN(name, apply(i).asInstanceOf[IntegerTerm] :: args.map(x => apply(x)))
        }
        case foTerm(v, arg) => foTerm(v.asInstanceOf[HOLVar], apply(arg.asInstanceOf[HOLExpression])::Nil).asInstanceOf[HOLExpression]
        case Atom(name, args) => {
          val newAtomName = HOLConst(new ConstantStringSymbol(name.toString()), args.reverse.map(x => x.exptype).foldRight(To().asInstanceOf[TA])((x,t) => ->(x, t)))
  //        val newAtomName = HOLConst(new ConstantStringSymbol(name.toString()), FunctionType( To(), args.map( a => a.exptype ) ))
            Atom(newAtomName, args.map(x => {
//              println("sub atom x = "+x)
              apply(x)
            }))
        }

//        the indexed variable
        case HOLApp(func, arg) if func.exptype == Tindex() -> Ti() && arg.exptype == Tindex() => {
          println("HOLApp(func, arg) = "+expression)
//          indexedFOVar(new VariableStringSymbol(func.asInstanceOf[HOLVar].name.toString()), IntZero()).asInstanceOf[HOLExpression]
          indexedFOVar(new VariableStringSymbol("x"), IntZero()).asInstanceOf[HOLExpression]
        }
        case _ => {
//                println("\ncase _ =>")
//                println(expression)
          expression
        }
      }
    }
  }


  class dbTRSsClause(val map: scala.collection.mutable.Map[String, Tuple2[Tuple2[sClause, sClause], Tuple2[sClause, sClause]]])
  //the t.r.s. for the sTermN
  object dbTRSsClause {
    def apply(name: String, base: Tuple2[sClause, sClause], step: Tuple2[sClause, sClause]): dbTRSsClause = {
      val m = scala.collection.mutable.Map.empty[String, Tuple2[Tuple2[sClause, sClause], Tuple2[sClause, sClause]]] + Pair("c", Tuple2(base, step))
      new dbTRSsClause(m)
    }
    def apply() = new dbTRSsClause(scala.collection.mutable.Map.empty[String, Tuple2[Tuple2[sClause, sClause], Tuple2[sClause, sClause]]])
  }


