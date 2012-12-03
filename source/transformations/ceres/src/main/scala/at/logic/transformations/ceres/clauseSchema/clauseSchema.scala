package at.logic.transformations.ceres.clauseSchema

import at.logic.algorithms.lk.getAncestors
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.calculi.slk._
import at.logic.calculi.slk.AndEquivalenceRule1._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.algorithms.shlk._
import at.logic.utils.ds.trees.LeafTree
import collection.immutable
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols.{ConstantSymbolA, ConstantStringSymbol}
import at.logic.language.lambda.typedLambdaCalculus.{AppN, LambdaExpression, Var}
import at.logic.language.lambda.types.FunctionType._
import at.logic.language.lambda.types.To._
import at.logic.language.lambda.types._
import at.logic.language.hol.Atom._
import at.logic.language.schema.foTerm._
import at.logic.language.lambda.BetaReduction
import at.logic.language.schema._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._

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
    override def equals(a: Any): Boolean = a match {
      case v:sClauseVar if this.name == v.name => true
      case _ => false
    }
  }
  object sClauseVar {
    def apply(name:String): sClauseVar = new sClauseVar(name)
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
      val typ = l.map(x => x.exptype).foldRight(Ti().asInstanceOf[TA])((x,t) => ->(x, t))
      val func = HOLConst(new ConstantStringSymbol(f), typ)
//      println("func = "+func)
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
    override def equals(a: Any): Boolean = {
      a match {
        case v:fo2Var if v.name.toString == this.name.toString => true
        case _ => false
      }
    }
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
    override def toString() = map.keySet.foldLeft("\n\n")((acc, s) => map.get(s).get._1._1+"  →  "+map.get(s).get._1._2+"\n"+map.get(s).get._2._1+"  →  "+map.get(s).get._2._2+"\n\n"+acc)
  }
  object dbTRSsTermN {
    def apply(term: String, base: Tuple2[HOLExpression, HOLExpression], step: Tuple2[HOLExpression, HOLExpression]): dbTRSsTermN = {
      val m = Map.empty[String, Tuple2[Tuple2[HOLExpression, HOLExpression], Tuple2[HOLExpression, HOLExpression]]] + Pair(term, Tuple2(base, step))
      new dbTRSsTermN(m)
    }
    def apply() = new dbTRSsTermN(Map.empty[String, Tuple2[Tuple2[HOLExpression, HOLExpression], Tuple2[HOLExpression, HOLExpression]]])
  }

  // dbTRS for c(k+1, x, X)clauseSchema
  class dbTRSclauseSchema(val map: Map[String, Tuple2[Tuple2[sClause, sClause], Tuple2[sClause, sClause]]]) {
    override def toString() = map.keySet.foldLeft("")((acc, s) => map.get(s).get._1._1+"  →  "+map.get(s).get._1._2+"\n"+map.get(s).get._2._1+"  →  "+map.get(s).get._2._2+acc)
  }
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
    def apply(f: HOLFormula, trs: dbTRSsTermN): HOLFormula = {
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
          nonVarSclause(newant.map(x => unfoldGroundAtom(x, trsSterms)), newsucc.map(x => unfoldGroundAtom(x, trsSterms)))
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
        case at.logic.language.hol.Imp(l, r) => at.logic.language.hol.Imp(apply(l.asInstanceOf[HOLExpression]).asInstanceOf[HOLFormula], apply(r.asInstanceOf[HOLExpression]).asInstanceOf[HOLFormula]).asInstanceOf[HOLExpression]
        case AllVar(v, f) => AllVar(v, apply(f.asInstanceOf[HOLExpression]).asInstanceOf[HOLFormula]).asInstanceOf[HOLExpression]
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
            val rez = apply(x)
//            println("rez sub atom = "+rez)
            rez
          }))
        }

//        the indexed variable
        case HOLApp(fo2Var(name), index) if index.exptype == Tindex() => {
//          println("HOLApp(func, arg) = "+expression)
//          indexedFOVar(new VariableStringSymbol("x"), IntZero()).asInstanceOf[HOLExpression]
          HOLApp(fo2Var(name), apply(index))
        }
        case sTermN(name, i, args) => {
//          println("sTermN = "+expression)
          sTermN(name, apply(i).asInstanceOf[IntegerTerm] :: args.map(x => apply(x)))
        }
        case foTerm(v, arg) => {
//          println("foTerm")
          foTerm(v.asInstanceOf[HOLVar], apply(arg.asInstanceOf[HOLExpression])::Nil).asInstanceOf[HOLExpression]
        }
        case sIndTerm(func, i) => {
//          println("subst sIndTerm")
          sIndTerm(func.name.toString(), apply(i).asInstanceOf[IntegerTerm])
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
    override def toString() = map.keySet.foldLeft("")((acc, s) => map.get(s).get._1._1+"  →  "+map.get(s).get._1._2+"\n"+map.get(s).get._2._1+"  →  "+map.get(s).get._2._2+acc)
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
//      println("resolutionDeduction")
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
          else {
//            println("else")
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

  //the t.r.s. for the resolution schema (global object)
  object resolutionProofSchemaDB extends Iterable[(String, Tuple2[Tuple2[sResolutionTerm, sResolutionTerm], Tuple2[sResolutionTerm, sResolutionTerm]])] with TraversableOnce[(String, Tuple2[Tuple2[sResolutionTerm, sResolutionTerm], Tuple2[sResolutionTerm, sResolutionTerm]])] {
    val map = new scala.collection.mutable.HashMap[String, Tuple2[Tuple2[sResolutionTerm, sResolutionTerm], Tuple2[sResolutionTerm, sResolutionTerm]]]
    def get(name: String) = map(name)
    def clear = map.clear
    def add(term: String, base: Tuple2[sResolutionTerm, sResolutionTerm], step: Tuple2[sResolutionTerm, sResolutionTerm]) = {
      map.put(term, Tuple2(base, step))
    }
    override def toString() = map.keySet.foldLeft("")((acc, s) => map.get(s).get._1._1+"  →  "+map.get(s).get._1._2+"\n"+map.get(s).get._2._1+"  →  "+map.get(s).get._2._2+acc)
    def iterator = map.iterator
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

  //unfolds a resolution term schema
  object unfoldResolutionProofSchema {
    def apply(rho: sResolutionTerm, trsSclause: dbTRSclauseSchema, trsSterms: dbTRSsTermN, subst: SchemaSubstitution3, mapX: Map[sClauseVar, sClause]): sResolutionTerm = {
      val k = IntVar(new VariableStringSymbol("k"))
      val l = IntVar(new VariableStringSymbol("l"))
      val X = sClauseVar("X")
      rho match {
        case rho1: ResolutionProofSchema if resolutionProofSchemaDB.map.contains(rho1.name) => {
          if (rho1.args.head == IntZero()) {
//            println("i == 0")
            val base = resolutionProofSchemaDB.map.get(rho1.name).get._1._2
            val new_mapX = Map[sClauseVar, sClause]() + Pair(X.asInstanceOf[sClauseVar], rho1.args.last.asInstanceOf[sClause])
            val delX = sClauseVarSubstitution(base, new_mapX)
            val ground = unfoldingAtomsInResTerm(delX, trsSterms, subst)
            ground
          }
          else {
            val map =
              if (subst.map.get(k).get.asInstanceOf[IntegerTerm] == IntZero())
                subst.map
              else {
                ((subst.map - k) - l) + Pair(k.asInstanceOf[Var], Pred(subst.map.get(k).get.asInstanceOf[IntegerTerm]))// + Pair(l.asInstanceOf[Var], Pred(subst.map.get(l).get.asInstanceOf[IntegerTerm]))
              }
            val step = resolutionProofSchemaDB.map.get(rho1.name).get._2._2
            var new_subst = new SchemaSubstitution3(map)
//            println("new_subst = "+new_subst.map)
            val new_mapX = Map[sClauseVar, sClause]() + Pair(X.asInstanceOf[sClauseVar], rho1.args.last.asInstanceOf[sClause])
//            println("new_mapX = "+new_mapX)
            val rho_new = IntVarSubstitution(step, subst)
//            println("rho_new = "+rho_new)
            val delX = sClauseVarSubstitution(rho_new, new_mapX)
//            println("delX = "+delX)

            apply(delX, trsSclause, trsSterms, new_subst, new_mapX)
          }
        }
        case r:rTerm => {
//          println("r = "+r)
          var left = apply(r.left, trsSclause, trsSterms, subst, mapX)
          if (left.isInstanceOf[nonVarSclause]) {
            left = nonVarSclause(left.asInstanceOf[nonVarSclause].ant.map(f => unfoldGroundAtom(f, trsSterms)) , left.asInstanceOf[nonVarSclause].succ.map(f => unfoldGroundAtom(f, trsSterms)))
          }
//          println("left = "+left)
          var right = apply(r.right, trsSclause, trsSterms, subst, mapX)
          if (right.isInstanceOf[nonVarSclause]) {
            right = nonVarSclause(right.asInstanceOf[nonVarSclause].ant.map(f => unfoldGroundAtom(f, trsSterms)) , right.asInstanceOf[nonVarSclause].succ.map(f => unfoldGroundAtom(f, trsSterms)))
          }
//          println("right = "+right)
          rTerm(left, right, unfoldGroundAtom(r.atom, trsSterms))
        }
//        case c:clauseSchema => TODO
//        case comp:sClauseComposition => TODO
//        case v:sClauseVar => TODO
        case _ => rho
      }
    }
  }

  //substitute a variable of type ω in a resolution term
  object IntVarSubstitution {
    def apply(r:sResolutionTerm, subst: SchemaSubstitution3): sResolutionTerm = {
      r match {
        case rps: ResolutionProofSchema => {
          ResolutionProofSchema(rps.name, rps.args.map(x => 
            if (x.isInstanceOf[IntegerTerm]) 
              subst(x.asInstanceOf[IntegerTerm]) 
            else
              if (x.isInstanceOf[nonVarSclause]) {
                nonVarSclause(x.asInstanceOf[nonVarSclause].ant.map(f => subst(f).asInstanceOf[HOLFormula]), x.asInstanceOf[nonVarSclause].succ.map(f => subst(f).asInstanceOf[HOLFormula]))
              }
              else
                if (x.isInstanceOf[sClauseComposition]) {
                  sClauseComposition(apply(x.asInstanceOf[sClauseComposition].sclause1, subst).asInstanceOf[sClause], apply(x.asInstanceOf[sClauseComposition].sclause2, subst).asInstanceOf[sClause])
                }
                else x))
        }
        case t:rTerm => rTerm(apply(t.left, subst), apply(t.right, subst), subst(t.atom).asInstanceOf[HOLFormula])
        case non:nonVarSclause => nonVarSclause(non.ant.map(f => subst(f).asInstanceOf[HOLFormula]), non.succ.map(f => subst(f).asInstanceOf[HOLFormula]))
        case c:sClauseComposition => sClauseComposition(apply(c.sclause1, subst).asInstanceOf[sClause], apply(c.sclause2, subst).asInstanceOf[sClause])
        case _ => r
      }
    }
  }


  //substitution for the  sClauseVar X in a resolution term
  object sClauseVarSubstitution {
    def apply(rho : sResolutionTerm, mapX: Map[sClauseVar, sClause]) : sResolutionTerm = {
//      println("sClauseVarSubstitution : "+rho+"    "+mapX)
      rho match {
        case x:sClauseVar if mapX.contains(x) => mapX.get(x).get
        case r:rTerm => {
          rTerm(apply(r.left, mapX), apply(r.right, mapX), r.atom)
        }
        case comp:sClauseComposition => deComposeSClause(sClauseComposition(apply(comp.sclause1, mapX).asInstanceOf[sClause], apply(comp.sclause2, mapX).asInstanceOf[sClause]))
//        case c:clauseSchema => TODO
        case rps:ResolutionProofSchema => ResolutionProofSchema(rps.name, rps.args.map(x =>
          if (x.isInstanceOf[sResolutionTerm]) {
//            println("x = "+x)
            sClauseVarSubstitution(x.asInstanceOf[sResolutionTerm], mapX)
          }
          else x) )
        case _ => {
//          println("case _ => "+rho)
          rho
        }
      }
    }
  }

  //substitution for all variables of type ω and unfolding the sTerms
  //it has to be applied after  sClauseVarSubstitution !!!
  object unfoldingAtomsInResTerm {
    def apply(rho : sResolutionTerm, trs: dbTRSsTermN, subst: SchemaSubstitution3) : sResolutionTerm = {
      rho match {
        case x:sClauseVar => throw new Exception("Res.term "+rho+ "contains X vars !")
        case non:nonVarSclause => {
          val ground = nonVarSclause(non.ant.map(f => subst(f).asInstanceOf[HOLFormula]), non.succ.map(f => subst(f).asInstanceOf[HOLFormula]))
          nonVarSclause(ground.ant.map(f => unfoldGroundAtom(f, trs)), ground.succ.map(f => unfoldGroundAtom(f, trs)))
        }
        case r:rTerm => {
          rTerm(apply(r.left, trs, subst), apply(r.right, trs, subst), unfoldGroundAtom(subst(r.atom).asInstanceOf[HOLFormula], trs))
        }
        case comp:sClauseComposition => sClauseComposition(apply(comp.sclause1, trs, subst).asInstanceOf[sClause], apply(comp.sclause2, trs, subst).asInstanceOf[sClause])
        //        case c:clauseSchema => TODO
        case _ => rho
      }
    }
  }

  object fo2SubstDB extends Iterable[(fo2Var, LambdaExpression)] {
    val map = new scala.collection.mutable.HashMap[fo2Var, LambdaExpression]
    def get(name: fo2Var) = map(name)
    def clear = map.clear
    def add(v: fo2Var, term: LambdaExpression): Unit = {
      map.put(v, term)
    }
    def iterator = map.iterator
  }

  // a substitution for the second-order variables of type : ω->ι
  // it is applied after unfoldingAtomsInResTerm, i.e. after the substitution of all ω and X variables
  object fo2VarSubstitution {
    def apply(o: Object, mapfo2: Map[fo2Var, LambdaExpression]): Object = {
//      println("\no = "+o)
//      println("o.getClass = "+o.getClass)
      o match {
        case r:rTerm => {
          rTerm(apply(r.left, mapfo2).asInstanceOf[sResolutionTerm], apply(r.right, mapfo2).asInstanceOf[sResolutionTerm], apply(r.atom, mapfo2).asInstanceOf[HOLFormula])
        }
        case Atom(name, args) => {
//          println("Atom")
          val newAtomName = HOLConst(new ConstantStringSymbol(name.toString()), args.reverse.map(x => x.exptype).foldRight(To().asInstanceOf[TA])((x,t) => ->(x, t)))
          val unfAtom = unfoldGroundAtom2(Atom(newAtomName, args.map(x => {
            val rez = apply(apply(x, mapfo2), mapfo2)
            rez.asInstanceOf[HOLExpression]
          })) )
//          println("unfAtom = "+unfAtom)
          unfAtom
        }
        case at.logic.language.hol.Imp(f1, f2) => at.logic.language.hol.Imp(apply(f1, mapfo2).asInstanceOf[HOLFormula], apply(f2, mapfo2).asInstanceOf[HOLFormula])
        case at.logic.language.hol.And(f1, f2) => at.logic.language.hol.And(apply(f1, mapfo2).asInstanceOf[HOLFormula], apply(f2, mapfo2).asInstanceOf[HOLFormula])
        case at.logic.language.hol.Or(f1, f2) =>  at.logic.language.hol.Or(apply(f1, mapfo2).asInstanceOf[HOLFormula], apply(f2, mapfo2).asInstanceOf[HOLFormula])
        case HOLApp(v , index) if index.exptype == Tindex()  => {
//          println("HOLApp(v , index) = "+o)
          val exp = HOLApp(mapfo2.get(v.asInstanceOf[fo2Var]).get, index)
//          println("exp = "+exp)
          val beta = BetaReduction.betaReduce(exp)(BetaReduction.StrategyOuterInner.Innermost, BetaReduction.StrategyLeftRight.Leftmost)
//          println("beta = "+unfoldSTerm(beta.asInstanceOf[HOLExpression]))
          unfoldSTerm(beta.asInstanceOf[HOLExpression])
        }
        case foTerm(v, arg) if v.exptype == ->(Ti(),Ti()) => {
//          println("foTerm = "+o)
//          println("v.getClass = "+v.getClass)
//          println("v = "+v)
//          println("arg = "+arg)
          val t = foTerm(v.asInstanceOf[HOLVar], apply(arg.asInstanceOf[HOLExpression], mapfo2).asInstanceOf[HOLExpression]::Nil).asInstanceOf[HOLExpression]
          //          println("t = "+t)
          t
        }
        case sTerm(v, i, args) => {
//          println("sTerm = "+o)
//          val t = foTerm(v.asInstanceOf[HOLVar], apply(args.asInstanceOf[HOLExpression], mapfo2).asInstanceOf[HOLExpression]::Nil).asInstanceOf[HOLExpression]
//          //          println("t = "+t)
//          t
          unfoldSTerm(o.asInstanceOf[HOLExpression])
        }
        case non: nonVarSclause => nonVarSclause(non.ant.map(f => apply(f, mapfo2).asInstanceOf[HOLFormula]), non.succ.map(f => apply(f, mapfo2).asInstanceOf[HOLFormula]))
        case indFOvar: indexedFOVar => {
//          println("indexedFOVar = "+o)
          val z = fo2Var(new VariableStringSymbol(indFOvar.name.toString()))
          apply(HOLApp(z, indFOvar.index), mapfo2)
        }
//        case v: foVar =>
        case _ => {
//          println("case _ => " + o +" : "+o.getClass)
          o
        }
      }
    }
  }

  object ResDeductionToLKTree {
    def apply(r: sResolutionTerm): LKProof = {
      r match {
        case non:nonVarSclause =>
          Axiom(non.ant, non.succ)
        case t:rTerm => {
          val up1 = apply(t.left)
          val up2 = apply(t.right)
          if(!up1.root.succedent.map(fo => fo.formula).filter(x=>x.syntaxEquals(t.atom)).isEmpty && !up2.root.antecedent.map(fo => fo.formula).filter(x=>x.syntaxEquals(t.atom)).isEmpty) {
            val left = up1.root.succedent.filter(fo => fo.formula.syntaxEquals(t.atom)).tail.foldLeft(up1)((acc, fo) => ContractionRightRule(acc, fo.formula))
            val right = up2.root.antecedent.filter(fo => fo.formula.syntaxEquals(t.atom)).tail.foldLeft(up2)((acc, fo) => ContractionLeftRule(acc, fo.formula))
            if(! left.root.succedent.map(fo=>fo.formula).filter(x => x.syntaxEquals(t.atom)).isEmpty) {
//              println("\nleft1")
//              printSchemaProof(left)
//              println("\nright1")
//              printSchemaProof(right)
//              println("\nt.atom = "+t.atom)
              return CutRule(left, right, t.atom)
            }
            else {
//              println("\nleft2")
//              printSchemaProof(left)
//              println("\nright2")
//              printSchemaProof(right)
//              println("\nt.atom = "+t.atom)
              return CutRule(right, left, t.atom)
            }
          }
          val right = if(up1.root.antecedent.filter(fo => fo.formula.syntaxEquals(t.atom)).isEmpty)
                        up1
                      else
                        up1.root.antecedent.filter(fo => fo.formula.syntaxEquals(t.atom)).tail.foldLeft(up1)((acc, fo) => ContractionLeftRule(acc, fo.formula))
          val left =  if(up2.root.succedent.filter(fo => fo.formula.syntaxEquals(t.atom)).isEmpty)
                        up2
                      else
                        up2.root.succedent.filter(fo => fo.formula.syntaxEquals(t.atom)).tail.foldLeft(up2)((acc, fo) => ContractionRightRule(acc, fo.formula))
          if(! left.root.succedent.map(fo=>fo.formula).filter(x => x.syntaxEquals(t.atom)).isEmpty ) {
//            println("\nleft3")
//            printSchemaProof(left)
//            println("\nright3")
//            printSchemaProof(right)
//            println("\nt.atom = "+t.atom)
            return CutRule(left, right, t.atom)
          }
          else {
            println("\nleft4")
            printSchemaProof(right)
            println("\nright4")
            printSchemaProof(left)
            println("\nt.atom = "+t.atom)
            if(right.root.succedent.map(fo=>fo.formula).contains(t.atom))
              println("YES")
            if(left.root.antecedent.map(fo=>fo.formula).contains(t.atom))
              println("NO")
            if(left.root.antecedent.map(fo=>fo.formula).head == t.atom)
              println("NO 2")
            if(left.root.antecedent.map(fo=>fo.formula).head.syntaxEquals(t.atom))
              println("NO 3")
            println(left.root.antecedent.map(fo=>fo.formula).head)
            println(right.root.succedent.map(fo=>fo.formula).head)
            println(t.atom)

            val cut = CutRule(right, left, t.atom)
            return cut
          }
        }
        case _ => throw new Exception("\nError in ResDeductionToLKTree !\n")
      }
    }
  }

















//--------------------------------------------------

  object unfoldGroundAtom2 {
    def apply(f: HOLFormula): HOLFormula = {
//      println("unfoldGroundAtom2 = "+f)
      f match {
        case Atom(name, args) => Atom(name, args.map(x => unfoldSTerm(x)))
        case _ => f
      }
    }
  }


  //unfolds a ground resolution proof schema
  object unfoldResolutionProofSchema2 {
    def apply(rho: sResolutionTerm): sResolutionTerm = {
      val k = IntVar(new VariableStringSymbol("k"))
      rho match {
        case rho1: ResolutionProofSchema if resolutionProofSchemaDB.map.contains(rho1.name) => {
          if (rho1.args.head == IntZero()) {
            val base = resolutionProofSchemaDB.map.get(rho1.name).get._1._2
            base
          }
          else {
            val step2 = resolutionProofSchemaDB.map.get(rho1.name).get._2._2
            val map = Map.empty[Var, HOLExpression] + Pair(k.asInstanceOf[Var], Pred(rho1.args.head.asInstanceOf[IntegerTerm]))
            val subst = new SchemaSubstitution3(map)
            val rho_subst = IntVarSubstitution(step2, subst)
            apply(rho_subst)
          }
        }
        case r:rTerm => {
          var left = apply(r.left)
          var right = apply(r.right)
          if (left.isInstanceOf[nonVarSclause])
            left = nonVarSclause(left.asInstanceOf[nonVarSclause].ant.map(f => unfoldGroundAtom2(f)) , left.asInstanceOf[nonVarSclause].succ.map(f => unfoldGroundAtom2(f)))
          if (right.isInstanceOf[nonVarSclause]) {
            right = nonVarSclause(right.asInstanceOf[nonVarSclause].ant.map(f => unfoldGroundAtom2(f)) , right.asInstanceOf[nonVarSclause].succ.map(f => unfoldGroundAtom2(f)))
          }
          rTerm(left, right, unfoldGroundAtom2(r.atom))
        }
        case _ => rho
      }
    }
  }

  // It seems that this object is only used for ProofTool,
  // so it was renamed to a proper name and removed from tests!
  object InstantiateResSchema {
    def getCorrectTermAndSubst(term_name:String, inst: Int): (sResolutionTerm, SchemaSubstitution3) = {
      val k = IntVar(new VariableStringSymbol("k"))
      if(inst == 0) {
        val map = Map[Var, HOLExpression]() + Pair(k.asInstanceOf[Var], IntZero())
        val subst = new SchemaSubstitution3(map)
        val rho1 = resolutionProofSchemaDB.map.get(term_name).get._1._1
        (rho1, subst)
      }
      else {
        val i = applySchemaSubstitution.toIntegerTerm(inst-1)
        val map = Map[Var, HOLExpression]() + Pair(k.asInstanceOf[Var], i)
        val subst = new SchemaSubstitution3(map)
        val rho1 = resolutionProofSchemaDB.map.get(term_name).get._2._1
        (rho1, subst)
      }
    }

    def apply(term_name:String, inst: Int): (String,LKProof) = {
      val pair = getCorrectTermAndSubst(term_name,inst)
      val rho1step1 = IntVarSubstitution(pair._1, pair._2)
      val r = unfoldResolutionProofSchema2(rho1step1)
      val mapfo2 = Map[fo2Var, LambdaExpression]() + fo2SubstDB.map.head
      val fo2sub = fo2VarSubstitution(r, mapfo2).asInstanceOf[sResolutionTerm]
      val proof = ResDeductionToLKTree(fo2sub)
      val name = term_name + "↓" + inst
      (name,proof)
    }
  }

  //grounds a LKS-proof with respect to the variables of type: ω->ι
  object GroundingProjections {
    def apply(p: LKProof, mapfo2: Map[fo2Var, LambdaExpression]): LKProof = {
//      println("p.rule = "+p.rule)
      p match {
        case Axiom(seq) => Axiom(Sequent(seq.antecedent.map(fo => fo.factory.createFormulaOccurrence(fo2VarSubstitution(fo.formula, mapfo2).asInstanceOf[HOLFormula], Nil)), seq.succedent.map(fo => fo.factory.createFormulaOccurrence(fo2VarSubstitution(fo.formula, mapfo2).asInstanceOf[HOLFormula], Nil)) ))
        case WeakeningLeftRule(up, _, p1) => WeakeningLeftRule(apply(up,mapfo2), fo2VarSubstitution(p1.formula, mapfo2).asInstanceOf[HOLFormula])
        case WeakeningRightRule(up, _, p1) => WeakeningRightRule(apply(up,mapfo2), fo2VarSubstitution(p1.formula, mapfo2).asInstanceOf[HOLFormula])
        case ContractionLeftRule(up, _, a1, a2, _) => ContractionLeftRule(apply(up,mapfo2), fo2VarSubstitution(a1.formula, mapfo2).asInstanceOf[HOLFormula])
        case ContractionRightRule(up, _, a1, a2, _) => ContractionRightRule(apply(up,mapfo2), fo2VarSubstitution(a1.formula, mapfo2).asInstanceOf[HOLFormula])
        case AndLeft1Rule(up, _, a, p) => AndLeft1Rule(apply(up,mapfo2), fo2VarSubstitution(a.formula, mapfo2).asInstanceOf[HOLFormula], fo2VarSubstitution(p.formula, mapfo2).asInstanceOf[HOLFormula])
        case AndLeft2Rule(up, _, a, p) => AndLeft2Rule(apply(up,mapfo2), fo2VarSubstitution(a.formula, mapfo2).asInstanceOf[HOLFormula], fo2VarSubstitution(p.formula, mapfo2).asInstanceOf[HOLFormula])
        case AndRightRule(up1, up2, _, a1, a2, _) => AndRightRule(apply(up1,mapfo2), apply(up2,mapfo2), fo2VarSubstitution(a1.formula, mapfo2).asInstanceOf[HOLFormula], fo2VarSubstitution(a2.formula, mapfo2).asInstanceOf[HOLFormula])
        case OrLeftRule(up1, up2, _, a1, a2, _) => OrLeftRule(apply(up1,mapfo2), apply(up2,mapfo2), fo2VarSubstitution(a1.formula, mapfo2).asInstanceOf[HOLFormula], fo2VarSubstitution(a2.formula, mapfo2).asInstanceOf[HOLFormula])
        case OrRight1Rule(up, _, a, p) => OrRight1Rule(apply(up,mapfo2), fo2VarSubstitution(a.formula, mapfo2).asInstanceOf[HOLFormula], fo2VarSubstitution(p.formula, mapfo2).asInstanceOf[HOLFormula])
        case OrRight2Rule(up, _, a, p) => OrRight2Rule(apply(up,mapfo2), fo2VarSubstitution(a.formula, mapfo2).asInstanceOf[HOLFormula], fo2VarSubstitution(p.formula, mapfo2).asInstanceOf[HOLFormula])
        case ImpRightRule(up, _, a1, a2, _) => ImpRightRule(apply(up,mapfo2), fo2VarSubstitution(a1.formula, mapfo2).asInstanceOf[HOLFormula], fo2VarSubstitution(a2.formula, mapfo2).asInstanceOf[HOLFormula])
        case ImpLeftRule(up1, up2, _, a1, a2, _) => ImpLeftRule(apply(up1,mapfo2), apply(up2,mapfo2), fo2VarSubstitution(a1.formula, mapfo2).asInstanceOf[HOLFormula], fo2VarSubstitution(a2.formula, mapfo2).asInstanceOf[HOLFormula])
        case NegLeftRule(up, _, a, p) => NegLeftRule(apply(up,mapfo2), fo2VarSubstitution(a.formula, mapfo2).asInstanceOf[HOLFormula])
        case NegRightRule(up, _, a, p) => NegRightRule(apply(up,mapfo2), fo2VarSubstitution(a.formula, mapfo2).asInstanceOf[HOLFormula])
        case ForallLeftRule(up, _, a, p, t) => ForallLeftRule(apply(up,mapfo2), fo2VarSubstitution(a.formula, mapfo2).asInstanceOf[HOLFormula], fo2VarSubstitution(p.formula, mapfo2).asInstanceOf[HOLFormula],  unfoldSTerm(fo2VarSubstitution(t, mapfo2).asInstanceOf[HOLExpression]))
        case ExistsRightRule(up, _, a, p, t) => ExistsRightRule(apply(up,mapfo2), fo2VarSubstitution(a.formula, mapfo2).asInstanceOf[HOLFormula], fo2VarSubstitution(p.formula, mapfo2).asInstanceOf[HOLFormula], unfoldSTerm(fo2VarSubstitution(t, mapfo2).asInstanceOf[HOLExpression]))
        case _ => throw new Exception("\nMissing case in GroundingProjections !\n"+p.rule)
      }
    }
  }

  object getAxioms {
    def apply(p: LKProof): List[Sequent] = {
      p match {
        case Axiom(seq) => seq::Nil
        case UnaryLKProof(_, up, _, _, _) => apply(up)
        case BinaryLKProof(_, up1, up2, _, _, _, _) => apply(up1) ::: apply(up2)
        case SchemaProofLinkRule(_,_,_) => Nil
        case _ => throw new Exception("\nMissing case in getAxioms !\n"+p.rule)
      }
    }
  }