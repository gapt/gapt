package at.logic.algorithms.fol.hol2fol

import at.logic.calculi.lk.base.FSequent
import at.logic.language.fol.{Substitution => FOLSubstitution, _}
import at.logic.language.hol
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.replacements.{Replacement, getAllPositions2}
import at.logic.language.hol.{AllVar => HOLAllVar, And => HOLAnd, Atom => HOLAtom, ExVar => HOLExVar, Function => HOLFunction, Imp => HOLImp, Neg => HOLNeg, Or => HOLOr, Substitution => HOLSubstitution, _}
import at.logic.language.lambda.symbols.{StringSymbol, SymbolA}
import at.logic.language.lambda.types.{FunctionType, TA, Ti, To}
import at.logic.language.schema.{IntZero, IntegerTerm, Succ, foConst, foVar, indexedFOVar}

import scala.collection.mutable


object reduceHolToFol extends reduceHolToFol
/**
 * Creates a FOL formula from a HOL formula, but applies transformations which do _not_ preserve validity!
 * Transformations applied:
 *
 *  - Replace all subterms (\x.t) by a constant. The scope parameter is needed to pass existing term-constant mappings.
 *  - Change the type of constants and variables s.t. they are first order (i.e. HOLConst("c", To->Ti) is mapped to FOLConst("c",Ti)
 *  - Logical operators inside the term structure are replaced by first order terms
 *
 * @note Make sure you need all of these tricks. If you have a HOL formula which actually is a FOL formula, use
 *       [[convertHolToFol]]. To replace abstraction subterms, use [[replaceAbstractions]]. Both have clear and easily
 *       revertible semantics.
 *
 */
class reduceHolToFol {

  private def folexp2term(exp:FOLExpression) = exp match {
    case e:FOLTerm => exp.asInstanceOf[FOLTerm]
    case _ => throw new Exception("Cannot cast "+exp+" to a fol term!"+exp.getClass)
  }


  /**
   * Convenience method when only a single expression is converted. Multiple expressions need to pass a scope which
   * holds the replacements which happened so far.
   * @param term a HOL expression to convert
   * @return the reduced FOL expression
   */
  def apply(term: HOLExpression) : FOLExpression = {
    val counter = new {private var state = 0; def nextId = { state = state +1; state}}
    val emptymap = Map[HOLExpression, StringSymbol]()
    apply( term, emptymap, counter )._1
  }

  /**
   * Convenience method when only a single formula is converted. Multiple expressions need to pass a scope which
   * holds the replacements which happened so far.
   * @param formula a HOL formula to convert
   * @return the reduced FOL formula
   */
  def apply(formula: HOLFormula) : FOLFormula =
  //inner cast needed to call the correct apply method
    reduceHolToFol(formula.asInstanceOf[HOLExpression]).asInstanceOf[FOLFormula]

  /**
   * Convenience method when only a single fsequent is converted. Multiple expressions need to pass a scope which
   * holds the replacements which happened so far.
   * @param fs an fsequent to convert
   * @return the reduced fsequent
   */
  def apply(fs: FSequent) : FSequent = {
    val counter = new {private var state = 0; def nextId = { state = state +1; state}}
    val emptymap = Map[HOLExpression, StringSymbol]()
    apply(fs, emptymap, counter)._1
  }

  /**
   * Convenience method when a single  list of fsequents is converted. Multiple expressions need to pass a scope which
   * holds the replacements which happened so far.
   * @param fs an fsequent to convert
   * @return the reduced fsequent
   */
  def apply(fs: List[FSequent]) : List[FSequent] = {
    val counter = new {private var state = 0; def nextId = { state = state +1; state}}
    val emptymap = Map[HOLExpression, StringSymbol]()
    apply(fs, emptymap, counter)._1
  }


  /**
   * Apply method for a formula when scope needs to passed on in a recursion.
   * @param formula the formula to convert
   * @param scope a mapping of replaced subterms to the constant names which replaced them. you need this for chained applications, like
   *              sequents or lists of formulas.
   * @param id an object with a function which nextId, which provides new numbers.
   * @return a pair of the reduced formula and the updated scope
   */
  def apply(formula: HOLFormula, scope: Map[HOLExpression, StringSymbol], id: {def nextId: Int}): (FOLFormula, Map[HOLExpression,StringSymbol]) = {
    val (scope_, qterm) = replaceAbstractions(formula, scope, id)
    (apply_( qterm).asInstanceOf[FOLFormula], scope_)
  }

  /**
   * Apply method for a an expression when scope needs to passed on in a recursion.
   * @param term the expression to convert
   * @param scope a mapping of replaced subterms to the constant names which replaced them. you need this for chained applications, like
   *              sequents or lists of formulas.
   * @param id an object with a function which nextId, which provides new numbers.
   * @return a pair of the reduced expression and the updated scope
   */
  def apply(term: HOLExpression, scope: Map[HOLExpression, StringSymbol], id: {def nextId: Int}) = {
    val (scope_, qterm) = replaceAbstractions(term, scope, id)
    (apply_( qterm), scope_)
  }

  /**
   * Apply method for a an FSequent when scope needs to passed on in a recursion.
   * @param s the fsequent to convert
   * @param scope a mapping of replaced subterms to the constant names which replaced them. you need this for chained applications, like
   *              sequents or lists of formulas.
   * @param id an object with a function which nextId, which provides new numbers.
   * @return a pair of the reduced expression and the updated scope
   */
  def apply(s: FSequent, scope: Map[HOLExpression, StringSymbol], id: {def nextId: Int}): (FSequent, Map[HOLExpression,StringSymbol]) = {
    val (scope1, ant) = s.antecedent.foldLeft((scope, List[HOLFormula]()))((r, formula) => {
      val (scope_, f_) = replaceAbstractions(formula, r._1, id)
      (scope_, f_.asInstanceOf[HOLFormula] :: r._2)
    })
    val (scope2, succ) = s.succedent.foldLeft((scope1, List[HOLFormula]()))((r, formula) => {
      val (scope_, f_) = replaceAbstractions(formula, r._1, id)
      (scope_, f_.asInstanceOf[HOLFormula] :: r._2)
    })

    (FSequent( ant.reverse map apply_, succ.reverse map apply_  ), scope ++ scope2)
  }


  /**
   * Apply method for a an FSequent when scope needs to passed on in a recursion.
   * @param fss the fsequent to convert
   * @param scope a mapping of replaced subterms to the constant names which replaced them. you need this for chained applications, like
   *              sequents or lists of formulas.
   * @param id an object with a function which nextId, which provides new numbers.
   * @return a pair of the reduced expression and the updated scope
   */
  def apply(fss: List[FSequent], scope: Map[HOLExpression, StringSymbol], id: {def nextId: Int}): (List[FSequent], Map[HOLExpression,StringSymbol]) = {
    fss.foldRight((List[FSequent](), scope))((fs, pair) => {
      val (list, scope) = pair
      val (fs_, scope_) = apply(fs, scope, id)
      (fs_ :: list, scope_)
    })

  }


  private def apply_(f:HOLFormula) : FOLFormula =
    apply_(f.asInstanceOf[HOLExpression]).asInstanceOf[FOLFormula]

  //assumes we are on the logical level of the hol formula - all types are mapped to i, i>o or i>i>o respectively
  private def apply_(term: HOLExpression): FOLExpression = {
    term match {
      case e : FOLExpression => e // if it's already FOL - great, we are done.
      case z:indexedFOVar => FOLVar(z.name.toString ++ intTermLength(z.index.asInstanceOf[IntegerTerm]).toString)
      case fov: foVar => FOLVar(fov.name)
      case foc: foConst => FOLConst(foc.name)
      case HOLVar(n, _) => FOLVar(n)
      case HOLConst(n, _) => FOLConst(n)
      case HOLNeg(n) => Neg(apply_(n))
      case HOLAnd(n1,n2) => And(apply_(n1), apply_(n2))
      case HOLOr(n1,n2) => Or(apply_(n1), apply_(n2))
      case HOLImp(n1,n2) => Imp(apply_(n1), apply_(n2))
      case HOLAllVar(v: HOLVar,n) => AllVar(apply_(v).asInstanceOf[FOLVar], apply_(n))
      case HOLExVar(v: HOLVar,n) => ExVar(apply_(v).asInstanceOf[FOLVar], apply_(n))
      case HOLAtom(HOLConst(n,_), ls) =>
        Atom(n, ls.map(x => folexp2term(apply_termlevel(x))))
      case HOLAtom(HOLVar(n,_), ls) =>
        Atom(n, ls.map(x => folexp2term(apply_termlevel(x))))
      case HOLFunction(HOLConst(n,_), ls, _) =>
        Function(n, ls.map(x => folexp2term(apply_(x))))
      case HOLFunction(HOLVar(n,_), ls, _) =>
        Function(n, ls.map(x => folexp2term(apply_(x))))

      //this case is added for schema
      case HOLApp(func,arg) => {
        func match {
          case HOLVar(sym,_) =>
            val new_arg = apply_(arg).asInstanceOf[FOLTerm]
            return Function(sym, new_arg::Nil)

          case _ =>
            println("WARNING: FO schema term: "+term)
            throw new Exception("Probably unrecognized object from schema!")
        }
      }
      case _ => throw new IllegalArgumentException("Cannot reduce hol term: " + term.toString + " to fol as it is a higher order variable function or atom") // for cases of higher order atoms and functions
    }
  }

  //if we encountered an atom, we need to convert logical formulas to the term level too
  private def apply_termlevel(term: HOLExpression): FOLTerm = {
    term match {
      case e : FOLTerm => e // if it's already FOL - great, we are done.
      case z:indexedFOVar => FOLVar(z.name.toString ++ intTermLength(z.index.asInstanceOf[IntegerTerm]).toString)
      case fov: foVar => FOLVar(fov.name.toString)
      case foc: foConst => FOLConst(foc.name.toString)
      case HOLVar(n, _) => FOLVar(n)
      case HOLConst(n, _) => FOLConst(n)
      //we cannot use the logical symbols directly because they are treated differently by the Function matcher
      case HOLNeg(n) => Function(NegSymbol.toString,  List(apply_termlevel(n)))
      case HOLAnd(n1,n2) => Function(AndSymbol.toString, List(apply_termlevel(n1), apply_termlevel(n2)))
      case HOLOr(n1,n2) => Function(OrSymbol.toString, List(apply_termlevel(n1), apply_termlevel(n2)))
      case HOLImp(n1,n2) => Function(ImpSymbol.toString, List(apply_termlevel(n1), apply_termlevel(n2)))
      case HOLAllVar(v: HOLVar,n) =>
        Function(ForallSymbol.toString, List(apply_termlevel(v).asInstanceOf[FOLVar], apply_termlevel(n)))
      case HOLExVar(v: HOLVar,n) =>
        Function(ExistsSymbol.toString, List(apply_termlevel(v).asInstanceOf[FOLVar], apply_termlevel(n)))
      case HOLAtom(n: SymbolA, ls) =>
        Function(n, ls.map(x => folexp2term(apply_termlevel(x))))
      case HOLFunction(HOLConst(name, _), ls, _) =>
        Function(name, ls.map(x => folexp2term(apply_termlevel(x))))

      //this case is added for schema
        /*
      case HOLApp(func,arg) => {
        func match {
          case HOLVar(sym,_) => {
            val new_arg = apply_(arg).asInstanceOf[FOLTerm]
            return at.logic.language.fol.Function(new ConstantStringSymbol(sym.toString), new_arg::Nil)
          }
          case _ => println("\nWARNING: FO schema term!\n")
        }
        throw new Exception("\nProbably unrecognized object from schema!\n")
      }
      */

      // This case replaces an abstraction by a function term.
      //
      // the scope we choose for the variant is the Abs itself as we want all abs identical up to variant use the same symbol
      //
      // TODO: at the moment, syntactic equality is used here... This means that alpha-equivalent terms may be replaced
      // by different constants, which is undesirable.
      /*
      case a @ Abs(v, exp) => {
        val sym = scope.getOrElseUpdate(a.variant(new VariantGenerator(new {var idd = 0; def nextId = {idd = idd+1; idd}}, "myVariantName")), ConstantStringSymbol("q_{" + id.nextId + "}"))
        val freeVarList = a.getFreeVariables.toList.sortWith((x,y) => x.toString < y.toString).map(x => apply(x.asInstanceOf[HOLExpression],scope,id))
        if (freeVarList.isEmpty) FOLConst(sym) else Function(sym, freeVarList.asInstanceOf[List[FOLTerm]])
      }
      */
      case _ => throw new IllegalArgumentException("Cannot reduce hol term: " + term.toString + " to fol as it is a higher order variable function or atom") // for cases of higher order atoms and functions
    }
  }


  //transforms a ground integer term to Int
  private def intTermLength(t: IntegerTerm): Int = t match {
    case c: IntZero => 0
    case Succ(t1) => 1 + intTermLength(t1)
    case _ => throw new Exception("\nError in reduceHolToFol.length(...) !\n")
  }
}


object replaceAbstractions extends replaceAbstractions

/**
 * Replace lambda-abstractions by constants.
 *
 * Each abstraction in an [[at.logic.calculi.lk.base.FSequent]] is replaced by a separate constant symbol; the used
 * constants are returned in a Map.
 */
class replaceAbstractions {
  type ConstantsMap = Map[HOLExpression,StringSymbol]

  def apply(l : List[FSequent]) : (ConstantsMap, List[FSequent]) = {
    val counter = new {private var state = 0; def nextId = { state = state +1; state}}
    l.foldLeft((Map[HOLExpression,StringSymbol](),List[FSequent]()))( (rec,el) => {
      val (scope_,f) = rec
      val (nscope, rfs) = replaceAbstractions(el, scope_,counter)
      (nscope, rfs::f)

    })
  }

  def apply(f:FSequent, scope : ConstantsMap, id: {def nextId: Int}) : (ConstantsMap,FSequent) = {
    val (scope1, ant) = f.antecedent.foldLeft((scope,List[HOLFormula]()))((rec,formula) => {
      val (scope_, f) = rec
      val (nscope, nformula) = replaceAbstractions(formula, scope_, id)
      (nscope, nformula.asInstanceOf[HOLFormula]::f)
    })
    val (scope2, succ) = f.succedent.foldLeft((scope1,List[HOLFormula]()))((rec,formula) => {
      val (scope_, f) = rec
      val (nscope, nformula) = replaceAbstractions(formula, scope_, id)
      (nscope, nformula.asInstanceOf[HOLFormula]::f)
    })

    (scope2, FSequent(ant.reverse, succ.reverse))
  }

  def apply(e : HOLExpression) : HOLExpression = {
    val counter = new {
      private var state = 0;

      def nextId = {
        state = state + 1; state
      }
    }
    apply(e, Map[HOLExpression, StringSymbol](), counter)._2
  }

  def apply(formula: HOLFormula) : HOLFormula =
    apply(formula.asInstanceOf[HOLExpression]).asInstanceOf[HOLFormula]

  // scope and id are used to give the same names for new functions and constants between different calls of this method
  def apply(e : HOLExpression, scope : ConstantsMap, id: {def nextId: Int})
  : (ConstantsMap, HOLExpression) = e match {
    case HOLVar(_,_) =>
      (scope,e)
    case HOLConst(_,_) =>
      (scope,e)
    //quantifiers should be kept
    case HOLAllVar(x,f) =>
      val (scope_, e_) = replaceAbstractions(f,scope,id)
      (scope_, HOLAllVar(x,e_.asInstanceOf[HOLFormula]))
    case HOLExVar(x,f) =>
      val (scope_, e_) = replaceAbstractions(f,scope,id)
      (scope_, HOLExVar(x,e_.asInstanceOf[HOLFormula]))
    case HOLApp(s,t) =>
      val (scope1,s1) = replaceAbstractions(s, scope, id)
      val (scope2,t1) = replaceAbstractions(t, scope1, id)
      (scope2, HOLApp(s1,t1))
    // This case replaces an abstraction by a function term.
    // the scope we choose for the variant is the Abs itself as we want all abs identical up to variant use the same symbol
    case HOLAbs(v, exp) =>
      //systematically rename free variables for the index
      //val normalizeda = e.variant(new VariantGenerator(new {var idd = 0; def nextId = {idd = idd+1; idd}}, "myVariantName"))
      //TODO: check if variable renaming is really what we want
      val (normalizeda, mapping) = normalizeFreeVariables(e)
      //println("e: "+e)
      //println("norm: "+normalizeda)
      //update scope with a new constant if neccessary
      //println(scope)
      val scope_ = if (scope contains normalizeda) scope else scope + ((normalizeda,StringSymbol("q_{" + id.nextId + "}")))
      //println(scope_)
      val sym = scope_(normalizeda)
      val freeVarList = hol.freeVariables(e).toList.sortBy(_.toString).asInstanceOf[List[HOLExpression]]
      if (freeVarList.isEmpty)
        (scope_, HOLConst( sym, e.exptype ))
      else {
        val c = HOLConst(sym, FunctionType(e.exptype, freeVarList.map(_.exptype)))
        (scope_, HOLFunction(c, freeVarList))
      }
    case _ =>
      throw new Exception("Unhandled case in abstraction replacement!"+e)

  }
}

object undoReplaceAbstractions extends undoReplaceAbstractions
/**
 * Replaces the constants introduced by [[replaceAbstractions]] with the original lambda-abstractions.
 */
class undoReplaceAbstractions {
  import replaceAbstractions.ConstantsMap

  def apply(fs : FSequent, map : ConstantsMap) : FSequent = FSequent(
                                                              fs.antecedent.map(apply(_,map)),
                                                              fs.succedent.map(apply(_,map))
                                                             )
  def apply(f : HOLFormula, map : ConstantsMap) : HOLFormula = apply(f.asInstanceOf[HOLExpression], map).asInstanceOf[HOLFormula]
  def apply(e : HOLExpression, map : ConstantsMap) : HOLExpression = {
    val stringsmap = map.map(x => (x._2.toString(), x._1)) //inverting the map works because the symbols are unique
    getAllPositions2(e).foldLeft(e)( (exp, position) =>
        //we check if the position is a constant with an abstraction symbol
        position._2 match {
          case HOLConst(name,_) if stringsmap.contains(name) =>
            //if yes, we replace it by the original expression
            Replacement(position._1, stringsmap(name))(exp)
          case _ => exp
    })
  }
}

object convertHolToFol extends convertHolToFol
/**
 * In contrast to [[reduceHolToFol]], we recreate the term via the fol constructors but
 * do not try to remove higher-order content.
 */
class convertHolToFol {
  def apply(e:HOLExpression) : FOLExpression = e match {
    case f : HOLFormula => convertFormula(f)
    case _ => convertTerm(e)
  }
  def apply(e:HOLFormula) : FOLFormula = convertFormula(e)
  def apply(fs:FSequent) : FSequent =
    FSequent(fs.antecedent.map(apply), fs.succedent.map(apply))

  def convertFormula(e:HOLFormula) : FOLFormula = e match {
    case HOLAtom(HOLConst(sym, exptype), args)
      if (args.filterNot(_.exptype == Ti).isEmpty) =>
      Atom(sym, args map convertTerm)

    case HOLNeg(x) => Neg(convertFormula(x))
    case HOLAnd(x,y) => And(convertFormula(x),convertFormula(y))
    case HOLOr(x,y) => Or(convertFormula(x),convertFormula(y))
    case HOLImp(x,y) => Imp(convertFormula(x),convertFormula(y))
    case HOLAllVar(x@HOLVar(_, Ti), t) => AllVar(convertTerm(x).asInstanceOf[FOLVar],convertFormula(t))
    case HOLExVar(x@HOLVar(_, Ti), t) => ExVar(convertTerm(x).asInstanceOf[FOLVar],convertFormula(t))
    case _ => throw new Exception("Could not convert term "+e+" to first order!")
  }

  def convertTerm(e:HOLExpression) : FOLTerm = e match {
    case HOLVar(x, Ti) => FOLVar(x)
    case HOLConst(x, Ti) => FOLConst(x)
    case HOLFunction(HOLConst(f, FunctionType(Ti,_)), args, Ti)
      if (args.filterNot(_.exptype == Ti).isEmpty) =>
      Function(f, args map convertTerm)
    case _ => throw new Exception("Could not convert term "+e+" to first order!")
  }

}

/**
 * Introducing abstractions and converting to fol changes more complex types to fol compatible ones. With changeTypeIn
 * you can change them back.
 */
object changeTypeIn {
  type TypeMap = Map[String, TA]

  /* TODO: this broken, since e.g. for (a b) q with type(q)=alpha, type(b)=beta then type(a)=beta > (alpha > gamma)
     we need to actually change the type of a when changing the type of q
    */
  /*
  def oldapply(e:LambdaExpression, tmap : TypeMap) : LambdaExpression = e match {
    case Var(name, ta) =>
      if (tmap.contains(name.toString()))
        e.factory.createVar(name, tmap(name.toString()))
      else
        e
    case App(s,t) => s.factory.createApp(oldapply(s,tmap), oldapply(t,tmap))
    case Abs(x,t) => t.factory.createAbs(oldapply(x,tmap).asInstanceOf[Var], oldapply(t,tmap))
  } */

  //Remark: this only works for changing the type of leaves in the term tree!
  def apply(e:HOLExpression, tmap : TypeMap) : HOLExpression = e match {
    case HOLVar(name, ta) => if (tmap contains name.toString()) HOLVar(name, tmap(name.toString())) else
                                                                HOLVar(name,ta)
    case HOLConst(name, ta) => if (tmap contains name.toString()) HOLConst(name, tmap(name.toString())) else
                                                                  HOLConst(name,ta)
    case HOLFunction(HOLConst(f,exptype), args, rv) =>
      val args_ = args.map(x => apply(x,tmap))
      val freturntype = exptype match { case FunctionType(r,_) => r }
      val f_ = HOLConst(f, FunctionType(freturntype, args.map(_.exptype)))
      HOLFunction(f_, args_)
    case HOLFunction(HOLVar(f,exptype), args, rv) =>
      val args_ = args.map(x => apply(x,tmap))
      val freturntype = exptype match { case FunctionType(r,_) => r }
      val f_ = HOLVar(f, FunctionType(freturntype, args.map(_.exptype)))
      HOLFunction(f_, args_)
    case HOLAtom(HOLConst(f,exptype), args) =>
      val args_ = args.map(x => apply(x,tmap))
      val f_ = HOLConst(f, FunctionType(To, args.map(_.exptype)))
      HOLAtom(f_, args_)
    case HOLAtom(HOLVar(f,exptype), args) =>
      val args_ = args.map(x => apply(x,tmap))
      val f_ = HOLVar(f, FunctionType(To, args.map(_.exptype)))
      HOLAtom(f_, args_)
    case HOLNeg(x) => HOLNeg(apply(x,tmap))
    case HOLAnd(s,t) => HOLAnd(apply(s,tmap), apply(t,tmap))
    case HOLOr(s,t) => HOLOr(apply(s,tmap), apply(t,tmap))
    case HOLImp(s,t) => HOLImp(apply(s,tmap), apply(t,tmap))
    case HOLAllVar(x,t) => HOLAllVar(apply(x.asInstanceOf[HOLVar],tmap).asInstanceOf[HOLVar], apply(t,tmap))
    case HOLExVar(x,t) => HOLExVar(apply(x.asInstanceOf[HOLVar],tmap).asInstanceOf[HOLVar], apply(t,tmap))
    case HOLAbs(x,t) => HOLAbs(apply(x.asInstanceOf[HOLVar],tmap).asInstanceOf[HOLVar], apply(t,tmap))
    case HOLApp(s,t) => HOLApp(apply(s,tmap), apply(t,tmap))
    case _ => throw new Exception("Unhandled case of a HOL Formula! "+e)

  }
  def apply(e:FOLExpression, tmap : TypeMap) : FOLExpression = apply(e.asInstanceOf[HOLExpression], tmap).asInstanceOf[FOLExpression]
  def apply(e:HOLFormula, tmap : TypeMap) : HOLFormula = apply(e.asInstanceOf[HOLExpression], tmap).asInstanceOf[HOLFormula]
  def apply(e:FOLFormula, tmap : TypeMap) : FOLFormula = apply(e.asInstanceOf[HOLExpression], tmap).asInstanceOf[FOLFormula]
  def apply(fs:FSequent, tmap:TypeMap) : FSequent = FSequent(fs.antecedent.map(x=> apply(x,tmap)),
                                                             fs.succedent.map(x=> apply(x,tmap)) )

  //different names bc of type erasure
  private def holsub(s:HOLSubstitution, tmap : TypeMap) : HOLSubstitution = HOLSubstitution(
    s.holmap.map(x =>
    (apply(x._1, tmap).asInstanceOf[HOLVar], apply(x._2, tmap) )
  ))

  private def folsub(s:FOLSubstitution, tmap : TypeMap) : FOLSubstitution = FOLSubstitution(s.folmap.map(x =>
    (apply(x._1, tmap).asInstanceOf[FOLVar], apply(x._2, tmap) )
  ))
}




