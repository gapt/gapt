package at.logic.transformations.ceres.clauseSchema

import at.logic.algorithms.lk.getAncestors
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
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

  abstract class sResolutionTerm {}
  abstract class sClauseTerm extends sResolutionTerm {}
  abstract class sClause extends sClauseTerm {
    override def toString: String
  }

  // c(k+1, x, X)
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


  //  X
  class sClauseVar(val name:String) extends sClause {
    override def toString = Console.BOLD+this.name+Console.RESET
  }
  object sClauseVar {
    def apply(name:String): sClause = new sClauseVar(name)
    def unaply(s : sClause) = s match {
      case v:sClauseVar => Some(v.name)
      case _ => None
    }
  }


  //usual clause : no schematic symbols and no schematic variables
  class nonVarSclause(val ant: List[HOLFormula], val succ: List[HOLFormula]) extends sClause {
    override def toString = {
      printSchemaProof.sequentToString(Sequent(ant.map(f => defaultFormulaOccurrenceFactory.createFormulaOccurrence(f, List())), succ.map(f => defaultFormulaOccurrenceFactory.createFormulaOccurrence(f, List()))))
  //    ant + " |- " + succ
    }
    override def equals(a: Any) = a match {
      case non: nonVarSclause => this.ant.toSet == non.ant.toSet && this.succ.toSet == non.succ.toSet
      case _ => false
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

  // sClause1 ◦ sClause2
  class sClauseComposition(val sclause1: sClause, val sclause2: sClause) extends sClause {
    override def toString = {sclause1 + Console.BOLD+Console.BLUE+" ◦ " + Console.RESET+ sclause2}
  }
  object sClauseComposition {
    def apply(scl1: sClause , scl2: sClause): sClause = new sClauseComposition(scl1, scl2)
    def unaply(s: sClause) = s match {
      case compos:sClauseComposition => Some(Pair(compos.sclause1, compos.sclause2))
      case _ => None
    }
  }

  //makes it with only one  "⊢" sign, i.e. removes ◦ as possible
  object deComposeSClause {
    def apply(c: sClause): sClause = {
      val mergeNonVarSClauses = {
        val res = getNonVarSclauses(c)
        if(res.length == 1)
          res.head
        else
          res.tail.foldLeft(res.head)((acc, clause) => nonVarSclause(acc.asInstanceOf[nonVarSclause].ant ++ clause.asInstanceOf[nonVarSclause].ant, acc.asInstanceOf[nonVarSclause].succ ++ clause.asInstanceOf[nonVarSclause].succ)).asInstanceOf[sClause]
      }
//      println("mergeNonVarSClauses = "+mergeNonVarSClauses)
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
      case _ => {
//        println("case _ => "+c)
        throw new Exception("Error in getNonVarSclauses!")
      }
    }
    private def getSClausVars(c: sClause): List[sClause] = c match {
      case v:sClauseVar => v::Nil
      case non:nonVarSclause => List.empty[sClause]
      case comp:sClauseComposition =>
        getSClausVars(comp.sclause1) ++ getSClausVars(comp.sclause2)
    }
  }


  //replace "v" with the sClause from the Map
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

  //applies sub to a sClauseTerm or sClause
  //the sub is of type Var -> HOLExpression
  object applySubToSclauseOrSclauseTerm {
    def apply(sub: SchemaSubstitution3, c: sClauseTerm): sClauseTerm = {
  //    println("sub, c = "+c)
      c match {
        case v:sClauseVar => c
        case cs:clauseSetTerm => {
          clauseSetTerm(cs.name, cs.args.map(x => {
            x match {
              case e:HOLExpression => sub(x.asInstanceOf[HOLExpression])
              case _ => x
            }
          }))
        }
        case non:nonVarSclause => {
          val ant1 = non.ant.map(f => sub(f).asInstanceOf[HOLFormula])
          val succ1 = non.succ.map(f => sub(f).asInstanceOf[HOLFormula])
          nonVarSclause(ant1, succ1)
        }
        case compos:sClauseComposition => {
          sClauseComposition(apply(sub, compos.sclause1).asInstanceOf[sClause], apply(sub, compos.sclause2).asInstanceOf[sClause])
        }
        case cs:clauseSchema => {
          clauseSchema(cs.name, cs.args.map(x => {
            x match {
              case e:HOLExpression => sub(x.asInstanceOf[HOLExpression])
              case _ => x
            }
          }))
        }
        case t: sclTimes => sclTimes(apply(sub, t.left), apply(sub, t.right))
        case t: sclPlus => sclPlus(apply(sub, t.left), apply(sub, t.right))
        case t: sclTermVar => t
        case _ => throw new Exception("\nERROR in applySubToSclauseOrSclauseTerm ! \n")
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
          val new_map = Map[Var, HOLExpression]() + Pair(k, a)
          val new_subst = new SchemaSubstitution3(new_map)
          val ground_c = applySubToSclauseOrSclauseTerm(new_subst, c).asInstanceOf[sClause]
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



  // σ(k+1, x, l)
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
      case Function(name, args, typ) if typ == Ti() && args.length != 0 && args.head.exptype == Tindex() => {
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
    def apply(name: VariableStringSymbol): HOLVar = {
      new fo2Var(name)
    }
    def unapply(s: HOLExpression) = s match {
      case v: fo2Var => Some(v.name)
      case _ => None
    }
  }


  // dbTRS for σ(k+1, x, l), i.e. sTermN
  class dbTRSsTermN(val map: Map[String, Tuple2[Tuple2[HOLExpression, HOLExpression], Tuple2[HOLExpression, HOLExpression]]]) {
    def add(term: String, base: Tuple2[HOLExpression, HOLExpression], step: Tuple2[HOLExpression, HOLExpression]): dbTRSsTermN = {
      val newMap = map + Pair(term, Tuple2(base, step))
      return new dbTRSsTermN(newMap)
    }
  }
  object dbTRSsTermN {
    def apply(term: String, base: Tuple2[HOLExpression, HOLExpression], step: Tuple2[HOLExpression, HOLExpression]): dbTRSsTermN = {
      val m = Map.empty[String, Tuple2[Tuple2[HOLExpression, HOLExpression], Tuple2[HOLExpression, HOLExpression]]] + Pair(term, Tuple2(base, step))
      new dbTRSsTermN(m)
    }
    def apply() = new dbTRSsTermN(Map.empty[String, Tuple2[Tuple2[HOLExpression, HOLExpression], Tuple2[HOLExpression, HOLExpression]]])
  }

  // dbTRS for c(k+1, x, X)clauseSchema
  class dbTRSclauseSchema(val map: Map[String, Tuple2[Tuple2[sClause, sClause], Tuple2[sClause, sClause]]])
  object dbTRSclauseSchema {
    def apply(term: String, base: Tuple2[sClause, sClause], step: Tuple2[sClause, sClause]): dbTRSclauseSchema = {
      val m = Map.empty[String, Tuple2[Tuple2[sClause, sClause], Tuple2[sClause, sClause]]] + Pair(term, Tuple2(base, step))
      new dbTRSclauseSchema(m)
    }
    def apply() = new dbTRSclauseSchema(Map.empty[String, Tuple2[Tuple2[sClause, sClause], Tuple2[sClause, sClause]]])
  }


  // unfolds terms of the form : σ(k+1, x, l)
  //k : IntVar, x: HOLVar of type ind->i, l: IntVar
  object unfoldSTermN {
    //for ground term
    def apply(t: HOLExpression, trs: dbTRSsTermN): HOLExpression = {
      val k = IntVar(new VariableStringSymbol("k"))
      val l = IntVar(new VariableStringSymbol("l"))
      t match {
        case sTermN(func, i, arg) if trs.map.contains(func) => {
          if (i == IntZero()) {
      //            println("\n\ni == 0")
            val map = if(arg.size != 0)
                        Map[Var, HOLExpression]() + Pair(k, i) + Pair(l, arg.last)
                      else
                        Map[Var, HOLExpression]() + Pair(k, i)
            val subst = new SchemaSubstitution3(map)
            val base = trs.map.get(func).get._1._2
            subst(base)
          }
          else
            if (i == k)
              t
            else  {
              val map = if(arg.size != 0)
                          Map[Var, HOLExpression]() + Pair(k, i) + Pair(l, arg.last)
                        else
                          Map[Var, HOLExpression]() + Pair(k, i)
              val subst = new SchemaSubstitution3(map)
              trs.map.get(func).get._2._2 match {
                case foTerm(name, arg1) => foTerm(name.asInstanceOf[HOLVar], apply(sTermN(func, Pred(i.asInstanceOf[IntegerTerm]) :: (arg.map(x => subst(x)))), trs)::Nil)
              }
            }
        }
        case _ => t//throw new Exception("\nno such case in schema/unfoldSTerm")
      }
    }

    ///for non-ground term
    def apply(t: HOLExpression, trs: dbTRSsTermN, subst: SchemaSubstitution3): HOLExpression = {
      val k = IntVar(new VariableStringSymbol("k"))
      t match {
        case sTermN(func, i, arg) if trs.map.contains(func) => {
          if (i == IntZero()) {
//            println("\n\ni == 0")
            val base = trs.map.get(func).get._1._2
            subst(subst(base))
          }
          else
          if (i == k)
            t
          else
            trs.map.get(func).get._2._2 match {
              case foTerm(name, arg1) => foTerm(name.asInstanceOf[HOLVar], apply(sTermN(func, Pred(i.asInstanceOf[IntegerTerm]) :: (arg.map(x => subst(x)))), trs, subst)::Nil)
            }
        }
        case foTerm(holvar, arg) => foTerm(holvar.asInstanceOf[HOLVar], apply(arg, trs, subst)::Nil)
        case _ => t//throw new Exception("\nno such case in schema/unfoldSTerm")
      }
    }
  }

  // rewrites  σ(k+1, x, k)  in  P(σ(k+1, x, k))
  object unfoldGroundAtom {
    def apply(f: HOLFormula, trs: dbTRSsTermN, subst: SchemaSubstitution3): HOLFormula = {
      f match {
        case Atom(name, args) => Atom(name, args.map(x => unfoldSTermN(x, trs)))
        case _ => f
      }
    }
  }

  //c(3, x, X) is unfolded
  object unfoldSchemaClause {
    def apply(t: sClause, trsSclause: dbTRSclauseSchema, trsSterms: dbTRSsTermN, subst: SchemaSubstitution3): sClause = {
      val k = IntVar(new VariableStringSymbol("k"))
      t match {
        case clauseSchema(func, i::arg) if trsSclause.map.contains(func) => {
//          println("\ncase clauseSchema(...)")
          if (i == IntZero()) {
//            println("\n\ni == 0")
            val base = trsSclause.map.get(func).get._1._2
            unfoldSchemaClause(base, trsSclause, trsSterms, subst)//subst(base)
          }
          else
          if (i == k)
            t
          else {
//            println("\nelse")
            apply(trsSclause.map.get(func).get._2._2, trsSclause, trsSterms, subst)
          }
        }
        case nonVarSclause(ant, succ) => {
//          println("\n\nnonVarSclause !")
          val newant = ant.map(x => subst(x).asInstanceOf[HOLFormula])
          val newsucc = succ.map(x => subst(x).asInstanceOf[HOLFormula])
          nonVarSclause(newant.map(x => unfoldGroundAtom(x, trsSterms, subst)), newsucc.map(x => unfoldGroundAtom(x, trsSterms, subst)))
//          nonVarSclause(newant, newsucc)
        }
        case co:sClauseComposition => {
//          println("\nco : "+subst.map.head._2.asInstanceOf[IntegerTerm])
          val k = IntVar(new VariableStringSymbol("k"))
//          println("map = "+subst.map)
          val map =
            if (subst.map.get(k).get.asInstanceOf[IntegerTerm] == IntZero())
              subst.map
            else {
              (subst.map - k) + Pair(k.asInstanceOf[Var], Pred(subst.map.get(k).get.asInstanceOf[IntegerTerm]))
            }
          val new_subst = new SchemaSubstitution3(map)
          val l = apply(applySubToSclauseOrSclauseTerm(subst, co.sclause1).asInstanceOf[sClause], trsSclause, trsSterms, new_subst)
          val r = apply(applySubToSclauseOrSclauseTerm(subst, co.sclause2).asInstanceOf[sClause], trsSclause, trsSterms, new_subst)
          sClauseComposition(l, r)
        }
        case _ => t//throw new Exception("\nno such case in schema/unfoldSTerm")
      }
    }
  }


  class SchemaSubstitution3(val map: Map[Var, HOLExpression])  {
    def apply(expression: HOLExpression): HOLExpression = {
//      println("subst :    "+expression)
      expression match {
        case x:IntVar => {
//                println("\nIntVar = "+x)
          map.get(x) match {
            case Some(t) => {
//                        println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
              t
            }
            case _ => {
//                        println(x + " Error in schema subst 1")
              x.asInstanceOf[HOLExpression]
            }
          }
        }
        case x:foVar => {
//                  println("\nfoVar = "+x)
          map.get(x) match {
            case Some(t) => {
              //          println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
              t
            }
            case _ => {
//                        println(x + " Error in schema subst 1")
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
        case ifo: indexedFOVar => {
//          println("indexedFOVar")
          indexedFOVar(ifo.name, apply(ifo.index).asInstanceOf[IntegerTerm])
        }
        case Atom(name, args) => {
//          println("Atom")
          val newAtomName = HOLConst(new ConstantStringSymbol(name.toString()), args.reverse.map(x => x.exptype).foldRight(To().asInstanceOf[TA])((x,t) => ->(x, t)))
//        val newAtomName = HOLConst(new ConstantStringSymbol(name.toString()), FunctionType( To(), args.map( a => a.exptype ) ))
          Atom(newAtomName, args.map(x => {
//              println("sub atom x = "+x)
            apply(x)
          }))
        }

//        the indexed variable
        case HOLApp(fo2Var(name), index) if index.exptype == Tindex() => {
//          println("HOLApp(func, arg) = "+expression)
//          indexedFOVar(new VariableStringSymbol(func.asInstanceOf[HOLVar].name.toString()), IntZero()).asInstanceOf[HOLExpression]
          indexedFOVar(new VariableStringSymbol("x"), IntZero()).asInstanceOf[HOLExpression]
        }
        case sTermN(name, i, args) => {
//          println("sTermN = "+expression)
          sTermN(name, apply(i).asInstanceOf[IntegerTerm] :: args.map(x => apply(x)))
        }
        case foTerm(v, arg) => {
//          println("foTerm")
          foTerm(v.asInstanceOf[HOLVar], apply(arg.asInstanceOf[HOLExpression])::Nil).asInstanceOf[HOLExpression]
        }
        case _ => {
//                println("\ncase _ => " + expression)
          expression
        }
      }
    }
  }

  // d(k+1, x, X) -> sClauseTerm ⊗/⊕ sClauseTerm
  class clauseSetTerm(val name: String, val args: List[Object]) extends sClauseTerm {
    override def toString:String = name+"("+printSchemaProof.formulaToString(args.head.asInstanceOf[HOLExpression])+ {args.tail.foldRight("")((x, rez) => ", "+x.toString+rez)} + ")"
  }
  object clauseSetTerm {
    def apply(sym: String, l: List[Object]): clauseSetTerm = {
      new clauseSetTerm(sym, l)
    }
    def unapply(c: sClause) = c match {
      case sc: clauseSetTerm => Some((sc.name, sc.args))
      case _ => None
    }
  }

  //clause schema term ⊕
  class sclPlus(val left: sClauseTerm, val right:sClauseTerm) extends sClauseTerm {
    override def toString() = Console.RED+"("+Console.RESET+left.toString + Console.RED+" ⊕ "+Console.RESET+right.toString+Console.RED+")"+Console.RESET
  }
  object sclPlus {
    def apply(l: sClauseTerm, r: sClauseTerm): sclPlus = {
      new sclPlus(l,r)
    }
    def unapply(t: sClauseTerm) = t match {
      case s:sclPlus => Some((s.left, s.right))
      case _ => None
    }
  }

  //clause schema term ⊗
  class sclTimes(val left: sClauseTerm, var right:sClauseTerm) extends sClauseTerm {
    override def toString() = Console.BLUE+" ( "+Console.RESET+left.toString + Console.BLUE+" ⊗ "+Console.RESET+right.toString+Console.BLUE+" ) "+Console.RESET
  }
  object sclTimes {
    def apply(l: sClauseTerm, r: sClauseTerm): sclTimes = {
      new sclTimes(l,r)
    }
    def unapply(t: sClauseTerm) = t match {
      case s:sclTimes => Some((s.left, s.right))
      case _ => None
    }
  }

  //clause schema term variable ξ
  class sclTermVar(val name: String) extends sClauseTerm {
    override def toString() = Console.BOLD+name+Console.RESET
  }
  object sclTermVar {
    def apply(name: String): sclTermVar = {
      new sclTermVar(name)
    }
    def unapply(t: sClauseTerm) = t match {
      case s:sclTermVar => Some((s.name))
      case _ => None
    }
  }

  //unfolds a ground schema clause term
  object unfoldSclauseTerm {
    def apply(t: sClauseTerm, trsSclause: dbTRSclauseSchema, trsSterms: dbTRSsTermN, subst: SchemaSubstitution3) : sClauseTerm = {
      t match {
        case x:sclTermVar => t
        case s:sClause => unfoldSchemaClause(s, trsSclause, trsSterms, subst)
        case x:sclTimes => sclTimes(apply(x.left, trsSclause, trsSterms, subst), apply(x.right, trsSclause, trsSterms, subst))
        case x:sclPlus => sclPlus(apply(x.left, trsSclause, trsSterms, subst), apply(x.right, trsSclause, trsSterms, subst))
        case _ => throw new Exception("case _ => in object unfoldSclauseTerm")
      }
    }
  }

  //substitution for X in the clause schema c(k+1, x, X)
  class sClauseVarSubstitution(val map: Map[sClauseVar, nonVarSclause]) {
    def apply(c: sClause): sClause = {
      c match {
        case v: sClauseVar if map.contains(v) => map.get(v).get
        case non: nonVarSclause => non
        case cls:clauseSchema => clauseSchema(cls.name, cls.args.map(x => {
          if (x.isInstanceOf[sClauseVar])
            apply(x.asInstanceOf[sClause])
          else
            x
        }))
        case _ => c
      }
    }
  }

  // substitution for ξ
  class sclTermVarSubstitution(val map: Map[sclTermVar, clauseSchema]) {
    def apply(sclTerm: sClauseTerm): sClauseTerm = {
      sclTerm match {
        case t: sclTermVar if map.contains(t) => map.get(t).get
        case t: sclTimes => sclTimes(apply(t.left), apply(t.right))
        case t: sclPlus => sclPlus(apply(t.left), apply(t.right))
        case _ => sclTerm
      }
    }
  }


  class dbTRSclauseSetTerm(var map: Map[String, Tuple2[Tuple2[sClauseTerm, sClauseTerm], Tuple2[sClauseTerm, sClauseTerm]]]) {
    def add(term: String, base: Tuple2[sClauseTerm, sClauseTerm], step: Tuple2[sClauseTerm, sClauseTerm]): Unit = {
      val newMap = map + Pair(term, Tuple2(base, step))
      map = newMap
    }
  }
  //the t.r.s. for the clause schema
  object dbTRSclauseSetTerm {
    def apply(term: String, base: Tuple2[sClauseTerm, sClauseTerm], step: Tuple2[sClauseTerm, sClauseTerm]): dbTRSclauseSetTerm = {
      val m =  Map.empty[String, Tuple2[Tuple2[sClauseTerm, sClauseTerm], Tuple2[sClauseTerm, sClauseTerm]]] + Pair(term, Tuple2(base, step))
      new dbTRSclauseSetTerm(m)
    }
    def apply() = new dbTRSclauseSetTerm( Map.empty[String, Tuple2[Tuple2[sClauseTerm, sClauseTerm], Tuple2[sClauseTerm, sClauseTerm]]])
  }


  //TODO: find a way to store the first rewriting application ! Remove b1, b2
  //unfolds a ground schema clause term
  object unfoldClauseSetTerm {
    def apply(t: sClauseTerm, trsSCLterm: dbTRSclauseSetTerm, trsSclause: dbTRSclauseSchema, trsSterms: dbTRSsTermN, subst: SchemaSubstitution3, b1:Boolean, b2:Boolean): sClauseTerm = {
      val k = IntVar(new VariableStringSymbol("k"))
      t match {
        case x:sclTermVar => x
        case pl:sclPlus => {
          sclPlus(apply(pl.left, trsSCLterm, trsSclause, trsSterms, subst, b1, b2), apply(pl.right, trsSCLterm, trsSclause, trsSterms, subst, b1, b2))
        }
        case ti:sclTimes => sclTimes(apply(ti.left, trsSCLterm, trsSclause, trsSterms, subst, b1, b2), apply(ti.right, trsSCLterm, trsSclause, trsSterms, subst, b1, b2))
        case cl:clauseSetTerm if trsSCLterm.map.contains(cl.name) => {
          if (cl.args.head == IntZero()) {
            //            println("\n\ni == 0")
            val base = trsSCLterm.map.get(cl.name).get._1._2
            unfoldClauseSetTerm(base, trsSCLterm, trsSclause, trsSterms, subst, b1, b2)//subst(base)
          }
          else
            if (cl.args.head == k)
              t
            else {
              val map =
                if (subst.map.get(k).get.asInstanceOf[IntegerTerm] == IntZero())
                  subst.map
                else {
                  (subst.map - k) + Pair(k.asInstanceOf[Var], Pred(subst.map.get(k).get.asInstanceOf[IntegerTerm]))
                }
              var new_subst = new SchemaSubstitution3(map)
              if (!b1 && cl.name == "d1") {
                new_subst = subst
                return apply(applySubToSclauseOrSclauseTerm(subst, trsSCLterm.map.get(cl.name).get._2._2), trsSCLterm, trsSclause, trsSterms, subst, true, b2)
              }
              if (!b2 && cl.name == "d2") {
                new_subst = subst
                return apply(applySubToSclauseOrSclauseTerm(subst, trsSCLterm.map.get(cl.name).get._2._2), trsSCLterm, trsSclause, trsSterms, subst, b1, true)
              }
              apply(applySubToSclauseOrSclauseTerm(new_subst, trsSCLterm.map.get(cl.name).get._2._2), trsSCLterm, trsSclause, trsSterms, new_subst, b1, b2)
            }
        }
        case _ => {
//          println("\ncase _ => "+t)
          t
        }
      }
    }
  }

// ---------    resolution schemata ------------------

  //r(c(k+1, x, X); P(x(k))⊢; P(x(k)))
  class rTerm(val left: sResolutionTerm, val right: sResolutionTerm, val atom: HOLFormula) extends sResolutionTerm {
    override def toString() = Console.GREEN+"r( "+Console.RESET+ left.toString + Console.GREEN+" ; "+Console.RESET+ right.toString + Console.GREEN+" ; "+Console.RESET+printSchemaProof.formulaToString(atom) + Console.GREEN+" )"+Console.RESET
  }
  object rTerm {
    def apply(l: sResolutionTerm, r: sResolutionTerm, at: HOLFormula): rTerm = {
      require(at match {
        case Atom(_,_) => true
        case _ => false
      })
      new rTerm(l, r, at)
    }
    def unapply(r: sResolutionTerm) = r match {
      case rt: rTerm => Some((rt.left, rt.right, rt.atom))
      case _ => None
    }
  }

  //grounded rTerm
  object resolutionDeduction {
    def apply(t: sResolutionTerm, trsSclause: dbTRSclauseSchema, trsSterms: dbTRSsTermN, subst: SchemaSubstitution3, mapX: Map[sClauseVar, sClause]): sResolutionTerm = {
      t match {
        case non:nonVarSclause => non
        case r:rTerm => {
          if (r.left.isInstanceOf[nonVarSclause]
            && r.right.isInstanceOf[nonVarSclause]
            && r.left.asInstanceOf[nonVarSclause].succ.contains(r.atom)
            && r.right.asInstanceOf[nonVarSclause].ant.contains(r.atom)
          ) {
            val non2Ant = r.right.asInstanceOf[nonVarSclause].ant.filter(f => f != r.atom)
            val non1Succ = r.left.asInstanceOf[nonVarSclause].succ.filter(f => f != r.atom)
            return nonVarSclause(r.left.asInstanceOf[nonVarSclause].ant ::: non2Ant, r.right.asInstanceOf[nonVarSclause].succ ::: non1Succ)
          }
          else
            return {
              val left = apply(r.left, trsSclause, trsSterms, subst, mapX)
              val right = apply(r.right, trsSclause, trsSterms, subst, mapX)
              apply(rTerm(left, right, r.atom), trsSclause, trsSterms, subst, mapX)
            }
        }
        case c: clauseSchema => deComposeSClause(replace(unfoldSchemaClause(c, trsSclause, trsSterms, subst), mapX))
        case _ => {
          println("\n case _ => in resolutionDeduction 2 : "+t)
          t
        }
      }
    }
  }


  //ρ(k+1, x, X) , where X is a sClauseVar ; x is a fo2Var
  class ResolutionProofSchema(val name:String,  val args: List[Object]) extends sResolutionTerm {
    override def toString() = name+"("+printSchemaProof.formulaToString(args.head.asInstanceOf[HOLExpression])+ {args.tail.foldRight("")((x, rez) => ", "+x.toString+rez)} + ")"
  }
  object ResolutionProofSchema {
    def apply(name:String,  args: List[Object]) : ResolutionProofSchema = {
      new ResolutionProofSchema(name, args)
    } 
    def unapply(rs: sResolutionTerm) = rs match {
      case r:ResolutionProofSchema => Some((r.name, r.args))
      case _ => None
    }
  }


  class dbTRSresolutionSchema(var map: Map[String, Tuple2[Tuple2[sResolutionTerm, sResolutionTerm], Tuple2[sResolutionTerm, sResolutionTerm]]]) {
    def add(term: String, base: Tuple2[sResolutionTerm, sResolutionTerm], step: Tuple2[sResolutionTerm, sResolutionTerm]): Unit = {
      val newMap = map + Pair(term, Tuple2(base, step))
      map = newMap
    }
  }
  //the t.r.s. for the clause schema
  object dbTRSresolutionSchema {
    def apply(term: String, base: Tuple2[sResolutionTerm, sResolutionTerm], step: Tuple2[sResolutionTerm, sResolutionTerm]): dbTRSresolutionSchema = {
      val m = Map.empty[String, Tuple2[Tuple2[sResolutionTerm, sResolutionTerm], Tuple2[sResolutionTerm, sResolutionTerm]]] + Pair(term, Tuple2(base, step))
      new dbTRSresolutionSchema(m)
    }
    def apply() = new dbTRSresolutionSchema( Map.empty[String, Tuple2[Tuple2[sResolutionTerm, sResolutionTerm], Tuple2[sResolutionTerm, sResolutionTerm]]])
  }


  object RewriteClauseSchemaInSclauseTerm {
    def apply(cst: sClauseTerm, trsSclause: dbTRSclauseSchema, trsSterms: dbTRSsTermN, subst: SchemaSubstitution3, mapX: Map[sClauseVar, sClause]) : sClauseTerm = {
      cst match {
        case c:clauseSchema => {
          deComposeSClause(replace(unfoldSchemaClause(c, trsSclause, trsSterms, subst), mapX))
        }
        case t: sclTimes => sclTimes(apply(t.left, trsSclause, trsSterms, subst, mapX), apply(t.right, trsSclause, trsSterms, subst, mapX))
        case t: sclPlus => sclPlus(apply(t.left, trsSclause, trsSterms, subst, mapX), apply(t.right, trsSclause, trsSterms, subst, mapX))
        case _ => {
//          println("case _ => "+cst)
          cst
        }
      }
    }
  }

  //transforms ground clause-set term to a set
  object clauseSetTermToSet {
    def apply(t: sClauseTerm): Set[nonVarSclause] = {
      t match {
        case non:nonVarSclause => Set.empty[nonVarSclause]+non//non.asInstanceOf[clauseSchemaTerm]
        case t:sclTimes => CartesianProduct(apply(t.left), apply(t.right))
        case t:sclPlus => Union(apply(t.left), apply(t.right))
        case _ => throw new Exception("Error in clauseSetTermToSet")
      }
    }
    def CartesianProduct(s1: Set[nonVarSclause], s2: Set[nonVarSclause]): Set[nonVarSclause] = {
      //TODO
      Set.empty[nonVarSclause]
    }
    def Union(s1: Set[nonVarSclause], s2: Set[nonVarSclause]): Set[nonVarSclause] = {
       (s1 ++ s2).foldLeft(Set.empty[nonVarSclause])((rez, el) => rez + el)
    }
  }

