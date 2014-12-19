/*
 * The definition of Indexed proposition is taken from:
 * A Schemata Calculus for Propositional Logic by Vincent Aravantinos, Ricardo Caferra, and Nicolas Peltier
 *
 */

package at.logic.language.schema

import at.logic.language.lambda.types._
import at.logic.language.lambda.FactoryA
import at.logic.language.lambda.symbols._
import at.logic.language.hol.{HOLFormula, HOLExpression, isLogicalSymbol}
import at.logic.language.hol.logicSymbols._
import at.logic.language.schema.logicSymbols._

trait SchemaExpression extends HOLExpression {
  override def factory: FactoryA = SchemaFactory
}

trait SchemaFormula extends SchemaExpression with HOLFormula   {
}

/******************** SPECIAL INTEGERS ************************************/

trait IntegerTerm extends SchemaExpression { require( exptype == Tindex ) }

class IntVar (sym: SymbolA) extends SchemaVar(sym, Tindex) with IntegerTerm {
  override def toString = name.toString+":"+exptype.toString
}
object IntVar {
  def apply(name: String) = new IntVar(StringSymbol(name))
  def unapply(t: IntegerTerm) = t match {
    case i: IntVar => Some(i.name)
    case _ => None
  }
}

class IntConst(sym: SymbolA) extends SchemaConst(sym, Tindex) with IntegerTerm

case class IntZero() extends SchemaConst(StringSymbol("0"), Tindex) with IntegerTerm

/**************************************************************************/

object IndexedPredicate {
  def apply(name: String, indexTerms: List[SchemaExpression]): SchemaFormula = {
    val pred = SchemaConst( name, FunctionType( To, indexTerms.head.exptype::Nil ) )
    SchemaApp(pred, indexTerms.head::Nil).asInstanceOf[SchemaFormula]
  }
  def apply(sym: SymbolA, indexTerms: List[SchemaExpression]): SchemaFormula = {
    val pred = SchemaConst( sym, FunctionType( To, indexTerms.head.exptype::Nil ) )
    SchemaApp(pred, indexTerms.head::Nil).asInstanceOf[SchemaFormula]
  }
  def apply(name: String, indexTerm: IntegerTerm): SchemaFormula = apply(name, indexTerm::Nil)

  def unapply( expression: SchemaExpression ) = expression match {
    case SchemaApp(_,_) if expression.exptype == To => 
      val p = unapply_(expression)
      if (p._2.forall(t => t.exptype == Tindex) ) {
        Some( p )
      } else None
    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_(e: SchemaExpression) : (SchemaConst, List[SchemaExpression]) = e match {
    case c: SchemaConst => (c, Nil)
    case SchemaApp(e1, e2) => 
      val t = unapply_(e1)
      (t._1, t._2 :+ e2)
  }

}

class indexedFOVar(sym: SymbolA, val index: SchemaExpression) extends SchemaVar(sym, Ti) {
  override def toString = name.toString+"("+index+")"+":"+exptype.toString
  override def equals(a: Any): Boolean = a match {
    case v:indexedFOVar if v.name.toString == this.name.toString() && v.index == this.index => true
    case _ => false
  }
}
object indexedFOVar {
  def apply(name: String, i: SchemaExpression): SchemaVar = new indexedFOVar(StringSymbol(name), i)
  def unapply(s: SchemaExpression) = s match {
    case v: indexedFOVar => Some(v.name, v.index)
    case _ => None
  }
}

class indexedOmegaVar(sym: SymbolA, val index: SchemaExpression) extends SchemaVar(sym, Tindex) {
  override def toString = name.toString+"("+index+")"+":"+exptype.toString
  override def equals(a: Any): Boolean = a match {
    case v:indexedOmegaVar if v.name == this.name && v.index == this.index => true
    case _ => false
  }
}


object indexedOmegaVar {
  def apply(name: String, i: SchemaExpression): SchemaVar = {
    new indexedOmegaVar(StringSymbol(name), i)
  }
  def unapply(s: SchemaExpression) = s match {
    case v: indexedOmegaVar => Some(v.name, v.index)
    case _ => None
  }
}

class foVar(sym: SymbolA) extends SchemaVar(sym, Ti) {
  override def equals(a: Any): Boolean = a match {
    case v:foVar if v.name.toString == this.name.toString => true
    case _ => false
  }
}
object foVar {
  def apply(name: String) = new foVar(StringSymbol(name))
  def unapply(t: SchemaExpression) = t match {
    case v: foVar => Some(v.name)
    case _ => None
  }
}

//indexed second-order variable of type: ind->i
class fo2Var(sym: SymbolA) extends SchemaVar(sym, ->(Tindex,Ti)) {
  override def equals(a: Any): Boolean = a match {
    case v:fo2Var if v.sym.toString == this.sym.toString => true
    case _ => false
  }
}
object fo2Var {
  def apply(name: String) = new fo2Var(StringSymbol(name))
  def unapply(s: SchemaExpression) = s match {
    case v: fo2Var => Some(v.name)
    case _ => None
  }
}

//first-order constant
class foConst(sym: SymbolA) extends SchemaConst(sym, Ti) {
  override def equals(a: Any): Boolean = a match {
    case v:foConst if v.name.toString == this.name.toString => true
    case _ => false
  }
}
object foConst {
  def apply(name: String) = new foConst(StringSymbol(name))
  def unapply(t: SchemaExpression) = t match {
    case c: foConst => Some(c.name, c.exptype)
    case _ => None
  }
}

//first-order variable of type ω
class fowVar(sym: SymbolA) extends SchemaVar(sym, Tindex) {
  override def equals(a: Any): Boolean = a match {
    case v:fowVar if v.name.toString() == this.name.toString() => true
    case _ => false
  }
}
object fowVar {
  def apply(name: String) = new fowVar(StringSymbol(name))
  def unapply(t: SchemaExpression) = t match {
    case v: fowVar => Some(v.name, v.exptype)
    case _ => None
  }
}

object Function {
  /*
  def apply(head: SchemaVar, args: List[SchemaExpression]): SchemaExpression = apply_(head, args)
  def apply(head: SchemaConst, args: List[SchemaExpression]): SchemaExpression = apply_(head, args)
  */

  // I added the following method to replace the ones above to avoid case distinctions
  // in user code. Maybe better: Add a trait "AtomHead" or something, and add it to
  // both SchemaConst and SchemaVar. Then, use SchemaExpression with AtomHead instead
  // of SchemaExpression below.
  //
  // The above methods are not so good since the unapply method returns SchemaExpressions,
  // which cannot directly be fed to the above apply methods without casting/case distinction.
  //
  def apply(head: SchemaExpression, args: List[SchemaExpression]): SchemaExpression = {
    require(head.isInstanceOf[SchemaVar] || head.isInstanceOf[SchemaConst])
    apply_(head, args)
  }

  private def apply_(head: SchemaExpression, args: List[SchemaExpression]): SchemaExpression = args match {
    case Nil => head
    case t :: tl => apply_(SchemaApp(head, t), tl)
  }

  def unapply( expression: SchemaExpression ) = expression match {
    case SchemaApp(c: SchemaConst,_) if isLogicalSymbol(c) => None
    case SchemaApp(SchemaApp(c: SchemaConst,_),_) if isLogicalSymbol(c) => None
    case SchemaApp(_,_) if (expression.exptype != To) =>
      val t = unapply_(expression)
      Some( (t._1, t._2, expression.exptype) )
    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_(e: SchemaExpression) : (SchemaExpression, List[SchemaExpression]) = e match {
    case v: SchemaVar => (v, Nil)
    case c: SchemaConst => (c, Nil)
    case SchemaApp(e1, e2) =>
      val t = unapply_(e1)
      (t._1, t._2 :+ e2)
  }
}

/*************** OPERATORS *****************/

case object BottomC extends SchemaConst(BottomSymbol, To) with SchemaFormula
case object TopC extends SchemaConst(BottomSymbol, To) with SchemaFormula
case object NegC extends SchemaConst(NegSymbol, ->(To, To))
case object AndC extends SchemaConst(AndSymbol, ->(To, ->(To, To)))
case object OrC extends SchemaConst(OrSymbol, ->(To, ->(To, To)))
case object ImpC extends SchemaConst(ImpSymbol, ->(To, ->(To, To)))
class EqC(e:TA) extends SchemaConst(EqSymbol, e -> (e -> To))
class ExQ(e:TA) extends SchemaConst(ExistsSymbol, ->(e,"o"))
class AllQ(e:TA) extends SchemaConst(ForallSymbol, ->(e,"o"))

// Schema-specific objects
case object BigAndC extends SchemaConst(BigAndSymbol, ->(->(Tindex, To), ->(Tindex, ->(Tindex, To))))
case object BigOrC extends SchemaConst(BigOrSymbol, ->(->(Tindex, To), ->(Tindex, ->(Tindex, To))))
case object BiggerThanC extends SchemaConst(BiggerThanSymbol, ->(Tindex, ->(Tindex, To)))
case class LessThanC(e:TA) extends SchemaConst(LessThanSymbol, ->(Tindex, ->(Tindex, To)))
case class LeqC(e:TA) extends SchemaConst(LeqSymbol, ->(Tindex, ->(Tindex, To)))
case object SuccC extends SchemaConst(StringSymbol("s"), ->(Tindex, Tindex))

object Neg {
  def apply(sub: SchemaFormula) = {
    val neg = sub.factory.createConnective(NegSymbol).asInstanceOf[SchemaConst]
    SchemaApp(neg, sub).asInstanceOf[SchemaFormula]
  }
  def unapply(expression: SchemaExpression) = expression match {
    case SchemaApp(NegC,sub) => Some( sub.asInstanceOf[SchemaFormula] )
    case _ => None
  }
}

object And {
  def apply(left: SchemaFormula, right: SchemaFormula) = {
    val and = left.factory.createConnective(AndSymbol).asInstanceOf[SchemaConst]
    SchemaApp(SchemaApp(and, left), right).asInstanceOf[SchemaFormula]
  }
  def apply(fs: List[SchemaFormula]) : SchemaFormula = fs match {
    case Nil => TopC
    case f::fs => fs.foldLeft(f)( (d, f) => And(d, f) )
  }
  def unapply(expression: SchemaExpression) = expression match {
    case SchemaApp(SchemaApp(AndC,left),right) => Some( (left.asInstanceOf[SchemaFormula],right.asInstanceOf[SchemaFormula]) )
    case _ => None
  }
}

object Or {
  def apply(left: SchemaFormula, right: SchemaFormula) = {
    val or = left.factory.createConnective(OrSymbol).asInstanceOf[SchemaConst]
    SchemaApp(SchemaApp(or,left),right).asInstanceOf[SchemaFormula]
  }
  def apply(fs: List[SchemaFormula]) : SchemaFormula = fs match {
    case Nil => BottomC
    case f::fs => fs.foldLeft(f)( (d, f) => Or(d, f) )
  }
  def unapply(expression: SchemaExpression) = expression match {
    case SchemaApp(SchemaApp(OrC,left),right) => Some( (left.asInstanceOf[SchemaFormula],right.asInstanceOf[SchemaFormula]) )
    case _ => None
  }
}

object Imp {
  def apply(left: SchemaFormula, right: SchemaFormula) = {
    val imp = left.factory.createConnective(ImpSymbol).asInstanceOf[SchemaConst]
    SchemaApp(SchemaApp(imp, left), right).asInstanceOf[SchemaFormula]
  }
  def unapply(expression: SchemaExpression) = expression match {
      case SchemaApp(SchemaApp(ImpC,left),right) => Some( (left.asInstanceOf[SchemaFormula],right.asInstanceOf[SchemaFormula]) )
      case _ => None
  }
}

private object ExQ {
  def apply(tp: TA) = new ExQ(tp)
  def unapply(v: SchemaConst) = v match {
    case vo: ExQ => Some(vo.exptype)
    case _ => None
  }
}
private object AllQ {
  def apply(tp: TA) = new AllQ(tp)
  def unapply(v: SchemaConst) = v match {
    case vo: AllQ => Some(vo.exptype)
    case _ => None
  }
}

private object EqC {
  def apply(ep: TA) = new EqC(ep)
  def unapply(v: SchemaConst) = v match {
    case vo: EqC => Some(vo.exptype)
    case _ => None
  }
}


private object Ex {
  def apply(sub: SchemaExpression) = {
    val ex = sub.factory.createConnective(ExistsSymbol, sub.exptype).asInstanceOf[SchemaConst]
    SchemaApp(ex, sub).asInstanceOf[SchemaFormula]
  }
  def unapply(expression: SchemaExpression) = expression match {
    case SchemaApp(ExQ(t),sub) => Some( (sub, t) )
    case _ => None
  }
}

private object All {
  def apply(sub: SchemaExpression) = {
    val all = sub.factory.createConnective(ForallSymbol, sub.exptype).asInstanceOf[SchemaConst]
    SchemaApp(all, sub).asInstanceOf[SchemaFormula]
  }
  def unapply(expression: SchemaExpression) = expression match {
    case SchemaApp(AllQ(t),sub) => Some( (sub, t) )
    case _ => None
  }
}

object ExVar {
  def apply(variable: SchemaVar, sub: SchemaFormula) = Ex(SchemaAbs(variable, sub))
  def unapply(expression: SchemaExpression) = expression match {
    case Ex(SchemaAbs(variable, sub), _) => Some( (variable, sub.asInstanceOf[SchemaFormula]) )
    case _ => None
  }
}

object AllVar {
  def apply(variable: SchemaVar, sub: SchemaFormula) = All(SchemaAbs(variable, sub))
  def unapply(expression: SchemaExpression) = expression match {
    case All(SchemaAbs(variable, sub), _) => Some( (variable, sub.asInstanceOf[SchemaFormula]) )
    case _ => None
  }
}

object BigAnd {
  def apply(i: IntVar, iter: SchemaFormula, init: IntegerTerm, end: IntegerTerm) : SchemaFormula =
    apply(new SchemaAbs(i, iter), init, end)

  def apply(iter: SchemaAbs, init: IntegerTerm , end: IntegerTerm) : SchemaFormula =
    SchemaApp(BigAndC, iter::init::end::Nil).asInstanceOf[SchemaFormula]
  
  def unapply( expression: SchemaExpression ) = expression match {
    case SchemaApp(SchemaApp(SchemaApp(BigAndC, SchemaAbs(v, formula)), init: IntegerTerm), end: IntegerTerm) => 
      Some( v, formula.asInstanceOf[SchemaFormula], init, end )
    case _ => None
  }
}

object BigOr {
  def apply(i: IntVar, iter: SchemaFormula, init: IntegerTerm, end: IntegerTerm) : SchemaFormula =
    apply(new SchemaAbs(i, iter), init, end)

  def apply(iter: SchemaAbs, init: IntegerTerm, end: IntegerTerm) : SchemaFormula =
    SchemaApp(BigOrC, iter::init::end::Nil).asInstanceOf[SchemaFormula]

  def unapply( expression: SchemaExpression ) = expression match {
    case SchemaApp(SchemaApp(SchemaApp(BigOrC, SchemaAbs(v, formula)), init: IntegerTerm), end: IntegerTerm) => 
      Some( v, formula.asInstanceOf[SchemaFormula], init, end )
    case _ => None
  }
}

object BiggerThan {
  def apply(l: IntegerTerm, r: IntegerTerm) = SchemaApp(SchemaApp(BiggerThanC, l), r)
  def unapply(e: SchemaExpression) = e match {
    case SchemaApp(SchemaApp(BiggerThanC, l), r) => Some( (l, r) )
    case _ => None
  }
}

object Succ {
  def apply(t: IntegerTerm): IntegerTerm  = SchemaApp(SuccC, t).asInstanceOf[IntegerTerm]
  def apply(t: SchemaExpression): SchemaExpression  = SchemaApp(SuccC, t)
  def unapply(p: SchemaExpression) = p match {
    case SchemaApp(SuccC, t : IntegerTerm) => Some(t)
    case _ => None
  }
}

object Pred {
  def apply(t: IntegerTerm): IntegerTerm  =  t match {
    case Succ(t1) => t1
    case _ => throw new Exception("ERROR in Predecessor")
  }
}

//object representing a schematic atom: P(i:ω, args)
object Atom {
  /*
  def apply(head: SchemaVar, args: List[SchemaExpression]): SchemaFormula = apply_(head, args).asInstanceOf[SchemaFormula]

  def apply(head: SchemaConst, args: List[SchemaExpression]): SchemaFormula = apply_(head, args).asInstanceOf[SchemaFormula]
  */

  // I added the following method to replace the ones above to avoid case distinctions
  // in user code. Maybe better: Add a trait "AtomHead" or something, and add it to
  // both SchemaConst and SchemaVar. Then, use SchemaExpression with AtomHead instead
  // of SchemaExpression below.
  //
  // The above methods are not so good since the unapply method returns SchemaExpressions,
  // which cannot directly be fed to the above apply methods without casting/case distinction.
  //
  def apply(head: SchemaExpression, args: List[SchemaExpression]): SchemaFormula = {
    require(head.isInstanceOf[SchemaVar] || head.isInstanceOf[SchemaConst])
    apply_(head, args).asInstanceOf[SchemaFormula]
  }


  private def apply_(head: SchemaExpression, args: List[SchemaExpression]): SchemaExpression = args match {
    case Nil => head
    case t :: tl => apply_(SchemaApp(head, t), tl)
  }

  def unapply(expression: SchemaExpression) = expression match {
    case SchemaApp(c: SchemaConst, _) if isLogicalSymbol(c) => None
    case SchemaApp(SchemaApp(c: SchemaConst, _), _) if isLogicalSymbol(c) => None
    case SchemaApp(_, _) if (expression.exptype == To) => Some(unapply_(expression))
    case SchemaConst(_, _) if (expression.exptype == To) => Some((expression, Nil))
    case SchemaVar(_, _) if (expression.exptype == To) => Some((expression, Nil))
    case _ => None
  }

  // Recursive unapply to get the head and args
  private def unapply_(e: SchemaExpression): (SchemaExpression, List[SchemaExpression]) = e match {
    case v: SchemaVar => (v, Nil)
    case c: SchemaConst => (c, Nil)
    case SchemaApp(e1, e2) =>
      val t = unapply_(e1)
      (t._1, t._2 :+ e2)

  }
}

  object lessThan {
    def apply(left: SchemaExpression, right: SchemaExpression) = {
      require(left.exptype == right.exptype)
      SchemaApp(SchemaApp(LessThanC(left.exptype), left), right).asInstanceOf[SchemaFormula]
    }

    def unapply(expression: SchemaExpression) = expression match {
      case SchemaApp(SchemaApp(LessThanC(_), left), right) => Some(left, right)
      case _ => None
    }
  }

  object leq {
    def apply(left: SchemaExpression, right: SchemaExpression) = {
      require(left.exptype == right.exptype)
      SchemaApp(SchemaApp(LeqC(left.exptype), left), right).asInstanceOf[SchemaFormula]
    }

    def unapply(expression: SchemaExpression) = expression match {
      case SchemaApp(SchemaApp(LeqC(_), left), right) => Some(left, right)
      case _ => None
    }
  }

  object Equation {
    def apply(left: SchemaExpression, right: SchemaExpression) = {
      require(left.exptype == right.exptype)
      val eq = left.factory.createConnective(EqSymbol, left.exptype).asInstanceOf[SchemaConst]
      SchemaApp(SchemaApp(eq, left), right).asInstanceOf[SchemaFormula]
    }

    def unapply(expression: HOLExpression) = expression match {
      case SchemaApp(SchemaApp(EqC(_), left), right) => Some(left, right)
      case _ => None
    }
  }


  object aTerm {
    def apply(name: SchemaConst, ind: IntegerTerm): IntegerTerm = {
      SchemaApp(name, ind).asInstanceOf[IntegerTerm]
    }
  }




  // Create a var or const????
  object foTerm {
    def apply(name: String, args: List[SchemaExpression]): SchemaExpression = {
      val v = SchemaVar(name, args.head.exptype -> Ti)
      SchemaApp(v, args.head)
    }

    def apply(v: SchemaExpression, args: List[SchemaExpression]): SchemaExpression = {
      SchemaApp(v, args.head)
    }

    def unapply(s: SchemaExpression) = s match {
      case a: SchemaApp if a.arg.exptype == Ti && a.function.exptype == ->(Ti, Ti) => Some(a.function.asInstanceOf[SchemaExpression], a.arg.asInstanceOf[SchemaExpression])
      case _ => None
    }
  }

  // TODO: this seems to be hardcoded for a a single parameter
  // plus 0 or 1 arguments. Generalize to simplify the code!
  object sTerm {
    //the i should be of type Tindex !
    def apply(f: String, i: SchemaExpression, l: List[SchemaExpression]): SchemaExpression = {
      require(i.exptype == Tindex)
      if (l.isEmpty) {
        val func = SchemaConst(f, ->(Tindex, Ti))
        return SchemaApp(func, i)
      }
      else {
        val func = SchemaConst(f, ->(Tindex, ->(Ti, Ti)))
        return SchemaApp(SchemaApp(func, i), l.head)
      }
    }

    def apply(f: SchemaConst, i: SchemaExpression, l: List[SchemaExpression]): SchemaExpression = {
      require(i.exptype == Tindex)
      if (l.isEmpty) SchemaApp(f, i)
      else SchemaApp(SchemaApp(f, i), l.head)
    }

    def unapply(s: SchemaExpression) = s match {
      case SchemaApp(SchemaApp(func: SchemaConst, i), arg) if i.exptype == Tindex => Some((func, i, arg :: Nil))
      case SchemaApp(func: SchemaConst, i) if i.exptype == Tindex => Some((func, i, Nil))
      case _ => None
    }
  }

  //indexed s-term of type ω->ω
  object sIndTerm {
    //the i should be of type Tindex !
    def apply(f: String, i: IntegerTerm): SchemaExpression = {
      val func = SchemaConst(f, ->(Tindex, Tindex))
      return SchemaApp(func, i)
    }

    def unapply(s: SchemaExpression) = s match {
      case SchemaApp(func: SchemaConst, i) if i.exptype == Tindex => Some((func, i))
      case _ => None
    }
  }

  //This version of the function is used specifically to find the highest level subterms
  //within atoms and satoms. Terms within terms are not located within the set.
  object SchemaSubTerms {
    def apply(f: HOLExpression): Seq[HOLExpression] = f match {
      case SchemaVar(_, _) => List(f)
      case Atom(_, args) => args.map(a => apply(a.asInstanceOf[SchemaExpression])).flatten
      case Function(_, args, _) => {
        List(f).toSeq
      }
      case And(x, y) => (apply(x.asInstanceOf[SchemaExpression]) ++ apply(y.asInstanceOf[HOLExpression]))
      case Or(x, y) => (apply(x.asInstanceOf[SchemaExpression]) ++ apply(y.asInstanceOf[HOLExpression]))
      case Imp(x, y) => (apply(x.asInstanceOf[SchemaExpression]) ++ apply(y.asInstanceOf[HOLExpression]))
      case Neg(x) => apply(x.asInstanceOf[SchemaExpression])
      case Ex(x) => apply(x.asInstanceOf[SchemaExpression])
      case All(x) => apply(x.asInstanceOf[SchemaExpression])

      case SchemaAbs(_, x) => apply(x.asInstanceOf[SchemaExpression])
      case SchemaApp(x, y) => List(f).toSeq
    }
  }


  //object representing a schematic atom: P(i:ω, args)
  object sAtom {
    def apply(sym: SymbolA, args: List[SchemaExpression]): SchemaFormula = {
      val pred: SchemaVar = SchemaFactory.createVar(sym, FunctionType(To, args.map(a => a.exptype)))
      apply(pred, args)
    }

    def unapply(s: SchemaExpression) = s match {
      case SchemaApp(func: SchemaConst, i) if i.exptype == Tindex => Some((func, i))
    }

    def apply(head: SchemaVar, args: List[SchemaExpression]): SchemaFormula = {
      SchemaApp(head, args).asInstanceOf[SchemaFormula]
    }

  }


  //database for trs
  object dbTRS extends Iterable[(SchemaConst, ((SchemaExpression, SchemaExpression), (SchemaExpression, SchemaExpression)))] {
    val map = new scala.collection.mutable.HashMap[SchemaConst, ((SchemaExpression, SchemaExpression), (SchemaExpression, SchemaExpression))]

    def get(name: SchemaConst) = map(name)

    def getOption(name: SchemaConst) = map.get(name)

    def clear = map.clear

    def add(name: SchemaConst, base: (SchemaExpression, SchemaExpression), step: (SchemaExpression, SchemaExpression)): Unit = {
      map.put(name, (base, step))

    }

    def iterator = map.iterator
  }


  case class SimsC(e: TA) extends SchemaConst(simSymbol, Ti ->( Ti-> To) )


  class sTermRewriteSys(val func: SchemaConst, val base: SchemaExpression, val rec: SchemaExpression)

  object sTermRewriteSys {
    def apply(f: SchemaConst, base: SchemaExpression, step: SchemaExpression) = new sTermRewriteSys(f, base, step)
  }



  object sims {
    def apply(left: SchemaExpression, right: SchemaExpression) = {
      require(left.exptype == right.exptype)
      SchemaApp(SchemaApp(SimsC(left.exptype), left), right).asInstanceOf[SchemaFormula]
    }

    def unapply(expression: SchemaExpression) = expression match {
      case SchemaApp(SchemaApp(SimsC(_), left), right) => Some(left.asInstanceOf[SchemaExpression], right.asInstanceOf[SchemaExpression])
      case _ => None
    }
  }


  object sTermDB extends Iterable[(SchemaConst, sTermRewriteSys)] with TraversableOnce[(SchemaConst, sTermRewriteSys)] {
    val terms = new scala.collection.mutable.HashMap[SchemaConst, sTermRewriteSys]

    def clear = terms.clear

    def get(func: SchemaConst) = terms(func)

    def put(sterm: sTermRewriteSys) = terms.put(sterm.func, sterm)

    def iterator = terms.iterator
  }
