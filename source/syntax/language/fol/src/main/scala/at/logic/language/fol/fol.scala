/*
 * fol.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package at.logic.language.fol

import at.logic.language.hol.EqC._
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol.{Neg => HOLNeg, Or => HOLOr, And => HOLAnd, Imp => HOLImp, Atom => HOLAtom, Function => HOLFunction}
import at.logic.language.hol.{HOLExpression, HOL, HOLFormula, HOLVar, HOLConst, HOLApp, HOLAbs, HOLConstFormula, HOLFactory, HOLAppFormula}
import at.logic.language.hol.{AllQ => HOLAllQ, ExQ => HOLExQ, ExVar => HOLExVar, AllVar => HOLAllVar}
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types.ImplicitConverters._

object Definitions { def fol = FOLFactory }

trait FOL extends HOL
{
  override def factory : LambdaFactoryA = FOLFactory
}

/**
 *The following is a note about the construction of this trait. Right now FOLExpression refers to both valid FOL terms
 * and formulas and components of such valid terms and formulas, so for example, the head symbol of an atom is also a
 * fol expression although it has a complex type.
 * @author ?
 * @version ?
 */
/* TODO we need to separate fol expression into FOLExpression which refers  only to valid fol expressions and to
FOLComponent which contains the fol factory but refers to possibly invalid fol expressions.
 */
trait FOLExpression extends HOLExpression with FOL {
  /**
   * This function takes a FOL construction and converts it to a string version. The String version is made
   * by replacing the code construction for logic symbols by string   versions in the file language/hol/logicSymbols.scala.
   * Terms are also handled by the this function.
   *
   @param  this  The method has no parameters other then the object which is to be written as a string
   *
   @throws Exception This occurs when an unknown subformula is found when parsing the FOL construction
   *
   @return A String which contains the defined symbols in language/hol/logicSymbols.scala.
   *
   */
  override def toString = this match {
      case Var(x,_) => x.toString
      case Atom(x, args) => x + "(" +
        (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s,a) => s+", "+a.toString)
        else args.foldLeft("")((s,a) => s+a.toString)) + ")"
      case Function(x, args) => x + "(" +
        (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s,a) => s+", "+a.toString)
        else args.foldLeft("")((s,a) => s+a.toString)) + ")"
      case And(x,y) => "(" + x.toString + AndSymbol + y.toString + ")"
      case Or(x,y) => "(" + x.toString + OrSymbol + y.toString + ")"
      case Imp(x,y) => "(" + x.toString + ImpSymbol + y.toString + ")"
      case Neg(x) => NegSymbol + x.toString
      case ExVar(x,f) => ExistsSymbol + x.toString + "." + f.toString
      case AllVar(x,f) => ForallSymbol + x.toString + "." + f.toString
      /* TODO: this method usually fails if layers got mixed (a fol structure contains a hol structure). the cli
       *       throws this exception when it tries to print such a malformed structure, but this is hard to see.
       *       should we print a warning instead? */
      /* Current status: print a warning, since algorithms for typed lambda calculus may create partial lambda terms
         which are later completed. This only surfaces when one tries to print debug output. */
      case _ =>
        val r = super.toString
        println("WARNING: Trying to do a string conversion on a term which is not a (full) FOL expression: "+r)
        r
      //case _ => println("Unknown string found, returning # in its place"); " # "
    }

  /**
   * This is an identity function for FOL construction, in that this
   *function takes a FOL statement, and outputs the statement as it was written/coded. Old
   *comment for this function was written as follows:
   * this function outputs the string which creates
   * an object like this. can be used to create
   * tests based on bugs.
   *
   The method has no parameters other then the object which is to be written as a string
   @param  this  The method has no parameters other then the object which is to be written as a string
   *
   @return A String illustrating the construction of the given FOL expression
   *
   */
    def toCode : String = this match {
      case FOLVar(x) => "FOLVar( " + x.toCode + " )"
      case FOLConst(x) => "FOLConst( " + x.toCode + " )"
      case Atom(x, args) => "Atom( " + x.toCode + ", " + args.foldLeft( "Nil" )( (s, a) => a.toCode + "::" + s ) + ")"
      case Function(x, args) => "Function( " + x.toCode + ", " + args.foldLeft( "Nil" )( (s, a) => a.toCode + "::" + s ) + ")"
      case And(x,y) => "And(" + x.toCode + ", " + y.toCode + ")"
      case Or(x,y) => "Or(" + x.toCode + ", " + y.toCode + ")"
      case Imp(x,y) => "Imp(" + x.toCode + ", " + y.toCode + ")"
      case Neg(x) => "Neg(" + x.toCode + ")"
      case ExVar(x,f) => "ExVar(" + x.toCode + ", " + f.toCode + ")"
      case AllVar(x,f) => "AllVar(" + x.toCode + ", " + f.toCode + ")"
      //case HArray(f1, f2) => "HArray(" + f1.toCode + ", " + f2.toCode + ")"
    }
  }

//trait FOLFormula extends HOLFormula with FOL
trait FOLFormula extends FOLExpression with HOLFormula {

  // Instantiates a term in a quantified formula (using the first quantifier).
  def instantiate(t: FOLTerm) = this match {
    case AllVar(v, form) => FOLSubstitution(form, v, t)
    case ExVar(v, form) => FOLSubstitution(form, v, t)
    case _ => throw new Exception("ERROR: trying to replace variables in a formula without quantifier.") 
  }

  // Instantiates all quantifiers of the formula with the terms in lst.
  // OBS: the number of quantifiers in the formula must greater or equal than the
  // number of terms in lst.
  def instantiateAll(lst: List[FOLTerm]) : FOLFormula = {
  lst match {
    case Nil => this
    case h :: t => this.instantiate(h).instantiateAll(t)
    }
  }

  // TODO: some of the methods below should work for FOL and HOL...

  // Transforms a formula to negation normal form (transforming also
  // implications into disjunctions)
  def toNNF : FOLFormula = this match {
    case Atom(_,_) => this
    case Function(_,_) => this
    case Imp(f1,f2) => Or((Neg(f1)).toNNF, f2.toNNF)
    case And(f1,f2) => And(f1.toNNF, f2.toNNF)
    case Or(f1,f2) => Or(f1.toNNF, f2.toNNF)
    case ExVar(x,f) => ExVar(x, f.toNNF)
    case AllVar(x,f) => AllVar(x, f.toNNF)
    case Neg(f) => f match {
      case Atom(_,_) => Neg(f)
      case Function(_,_) => Neg(f)
      case Neg(f1) => f1.toNNF
      case Imp(f1,f2) => And(f1.toNNF, Neg(f2.toNNF))
      case And(f1,f2) => Or(Neg(f1).toNNF, Neg(f2).toNNF)
      case Or(f1,f2) => And(Neg(f1).toNNF, Neg(f2).toNNF)
      case ExVar(x,f) => AllVar(x, Neg(f).toNNF)
      case AllVar(x,f) => ExVar(x, Neg(f).toNNF)
      case _ => throw new Exception("ERROR: Unexpected case while transforming to negation normal form.")
    }
    case _ => throw new Exception("ERROR: Unexpected case while transforming to negation normal form.")
  }

  // Distribute Ors over Ands
  def distribute : FOLFormula = this match {
    case Atom(_,_) => this
    //case Function(_,_) => this
    // Negation has only atomic scope
    case Neg(Atom(_,_)) => this
    //case Neg(Function(_,_)) => this
    case And(f1, f2) => And(f1.distribute, f2.distribute)
    case Or(f1, And(f2,f3)) => And(Or(f1,f2).distribute, Or(f1,f3).distribute)
    case Or(And(f1,f2), f3) => And(Or(f1,f3).distribute, Or(f2,f3).distribute)
    case Or(f1, f2) => Or(f1.distribute, f2.distribute)
    case _ => throw new Exception("ERROR: Unexpected case while distributing Ors over Ands.")
  }

  // Transforms a formula to conjunctive normal form
  // 1. Transform to negation normal form
  // 2. Distribute Ors over Ands
  // OBS: works for propositional formulas only
  // TODO: tests for this
  def toCNF : FOLFormula = this.toNNF.distribute

  def numOfAtoms : Int = this match {
    case Atom(_,_) => 1
    case Function(_,_) => 1
    case Imp(f1,f2) => f1.numOfAtoms + f2.numOfAtoms
    case And(f1,f2) => f1.numOfAtoms + f2.numOfAtoms
    case Or(f1,f2) => f1.numOfAtoms + f2.numOfAtoms
    case ExVar(x,f) => f.numOfAtoms
    case AllVar(x,f) => f.numOfAtoms
    case Neg(f) => f.numOfAtoms
    case _ => throw new Exception("ERROR: Unexpected case while counting the number of atoms.")
  }

  // Returns the quantifier free part of a prenex formula
  def getMatrix : FOLFormula = {
    assert(this.isPrenex)
    this match {
      case Var(_,_) |
           Atom(_,_) |
           Imp(_,_) |
           And(_,_) |
           Or(_,_) |
           Neg(_) => this
      case ExVar(x,f0) => f0.getMatrix
      case AllVar(x,f0) => f0.getMatrix
      case _ => throw new Exception("ERROR: Unexpected case while extracting the matrix of a formula.")
    }
  }
}

// the companion object converts HOL formulas into fol if the hol version has fol type
object FOLFormula {
 
  def apply(f: HOLFormula): FOLFormula = f match {
    case HOLNeg(x) => Neg(FOLFormula(x))
    case HOLOr(x,y) => Or(FOLFormula(x), FOLFormula(y))
    case HOLAnd(x,y) => And(FOLFormula(x), FOLFormula(y))
    case HOLImp(x,y) => Imp(FOLFormula(x), FOLFormula(y))
    case HOLAtom(nm: ConstantSymbolA, ls) if ls.forall(_.isInstanceOf[HOLExpression]) => Atom(nm, ls.map(x => FOLTerm(x.asInstanceOf[HOLExpression])))
    case HOLExVar(HOLVar(n,t),s) if (t == Ti()) => ExVar(FOLVar(n), FOLFormula(s))
    case HOLAllVar(HOLVar(n,t),s) if (t == Ti()) => AllVar(FOLVar(n), FOLFormula(s))
    case _ => throw new IllegalArgumentException("Cannot extract FOLFormula from higher order epxression: " + f.toString)
  }

}

trait FOLTerm extends FOLExpression
// trait FOLTerm extends HOLExpression with FOL
{
  require( exptype == Ti() )
}
object FOLTerm {
  def apply(t: HOLExpression): FOLTerm = t match {
    case HOLVar(n,t) if (t == Ti()) => FOLVar(n)
    case HOLConst(n,t) if (t == Ti()) => FOLConst(n)
    case HOLFunction(name: ConstantSymbolA, ls, t) if (ls.forall(_.isInstanceOf[HOLExpression])) => Function(name, ls.map(x => FOLTerm(x.asInstanceOf[HOLExpression])))
    case _ => throw new IllegalArgumentException("Cannot extract FOLTerm from higher order epxression: " + t.toString)
  }
}

// individual variable
class FOLVar (name: VariableSymbolA, dbInd: Option[Int])
  extends HOLVar(name, Ti(), dbInd) with FOLTerm

// individual constant
class FOLConst (name: ConstantSymbolA)
  extends HOLConst(name, Ti()) with FOLTerm

protected[fol] class FOLApp(function: LambdaExpression, argument: LambdaExpression)
  extends HOLApp(function, argument) with FOLExpression

protected[fol] class FOLAbs(variable: FOLVar, expression: LambdaExpression)
  extends HOLAbs(variable, expression) with FOLExpression

protected[fol] object FOLAbs {
  def apply(variable: FOLVar, expression: LambdaExpression) = new FOLAbs(variable, expression)
}

object FOLVar {
  def apply(name: VariableSymbolA) = new FOLVar(name,None)
  def unapply(exp: LambdaExpression) = exp match {
    case Var( sym : VariableSymbolA, t : Ti ) => Some( sym )
    case _ => None
  }
}

object FOLConst {
  def apply(name: ConstantSymbolA) = new FOLConst(name)
  def unapply(exp: LambdaExpression) = exp match {
    case Var( sym : ConstantSymbolA, t : Ti ) => Some( sym )
    case _ => None
  }
}


object Equation {
    def apply(left: FOLTerm, right: FOLTerm) = {
      App(App(EqC, left),right).asInstanceOf[FOLFormula]
    }
    def unapply(expression: LambdaExpression) = expression match {
        case App(App(EqC,left),right) => Some( left.asInstanceOf[FOLTerm],right.asInstanceOf[FOLTerm] )
        case _ => None
    }
  }

// FOL atom of the form P(t_1,...,t_n)
object Atom {
  def apply( sym: ConstantSymbolA, args: List[FOLTerm]) = {
    val pred : Var = FOLFactory.createVar( sym, FunctionType( To(), args.map( a => Ti() ) ) )
    AppN(pred, args).asInstanceOf[FOLFormula]
  }
  def unapply( expression: LambdaExpression ) = expression match {
    case App(sym,_) if sym.isInstanceOf[LogicalSymbolsA] => None
    case App(App(sym,_),_) if sym.isInstanceOf[LogicalSymbolsA] => None
    case AppN( Var( name: ConstantSymbolA, t ), args ) if t == FunctionType( To(), args.map( a => Ti() ) ) => Some( ( name, args.asInstanceOf[List[FOLTerm]] ) )
    case _ => None
  }
}

// FOL function of the form f(t_1,...,t_n)
object Function {
  def apply( sym: ConstantSymbolA, args: List[FOLTerm]) = {
    val f: Var = FOLFactory.createVar( sym, FunctionType( Ti(), args.map( a => Ti() ) ) )
    AppN( f, args ).asInstanceOf[FOLTerm]
  }
  def unapply( expression: LambdaExpression ) = expression match {
    case AppN( Var( name: ConstantSymbolA, t), args ) if t == FunctionType( Ti(), args.map( a => Ti() ) ) => Some( (name, args.asInstanceOf[List[FOLTerm]] ) )
    case _ => None
  }
}
// TODO put on wiki these are constants representing symbols in the logic.
case object TopC extends HOLConst(TopSymbol, "o") with FOLFormula
case object BottomC extends HOLConst(BottomSymbol, "o") with FOLFormula
case object NegC extends HOLConst(NegSymbol, "(o -> o)") with FOL
case object AndC extends HOLConst(AndSymbol, "(o -> (o -> o))") with FOL
case object OrC extends HOLConst(OrSymbol, "(o -> (o -> o))") with FOL
case object ImpC extends HOLConst(ImpSymbol, "(o -> (o -> o))") with FOL
case object EqC extends HOLConst(EqSymbol, "(i -> (i -> o))") with FOL
class ExQ(e:TA) extends HOLExQ(e) with FOL
class AllQ(e:TA) extends HOLAllQ(e) with FOL


object ExQ {
  def unapply(v: Var) = v match {
    case vo: ExQ => Some(vo.exptype)
    case _ => None
  }
}

object AllQ {
  def unapply(v: Var) = v match {
    case vo: AllQ => Some(vo.exptype)
    case _ => None
  }
}

object Neg {
  def apply(sub: FOLFormula) = App(NegC,sub).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(NegC,sub) => Some( (sub.asInstanceOf[FOLFormula]) )
    case _ => None
  }
}

object And {
  def apply(fs: Seq[FOLFormula]) : FOLFormula = fs match {
    case Nil => TopC
    case f::fs => fs.foldLeft(f)( (d, f) => And(d, f) )
  }
  def apply(left: FOLFormula, right: FOLFormula) = (App(App(AndC,left),right)).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(App(AndC,left),right) => Some( (left.asInstanceOf[FOLFormula],right.asInstanceOf[FOLFormula]) )
    case _ => None
  }
}

object Or {
    def apply(fs: Seq[FOLFormula]) : FOLFormula = fs match {
      case Nil => BottomC
      case f::fs => fs.foldLeft(f)( (d, f) => Or(d, f) )
    }
  def apply(left: FOLFormula, right: FOLFormula) = App(App(OrC,left),right).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(App(OrC,left),right) => Some( (left.asInstanceOf[FOLFormula],right.asInstanceOf[FOLFormula]) )
    case _ => None
  }
}

object Imp {
  def apply(left: FOLFormula, right: FOLFormula) = App(App(ImpC,left),right).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
      case App(App(ImpC,left),right) => Some( (left.asInstanceOf[FOLFormula],right.asInstanceOf[FOLFormula]) )
      case _ => None
  }
}


private[fol] object Ex {
  def apply(sub: LambdaExpression) = App(new ExQ(sub.exptype),sub).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(ExQ(t),sub) => Some( (sub, t) )
    case _ => None
  }
}

object All {
  def apply(sub: LambdaExpression) = App(new AllQ(sub.exptype),sub).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(AllQ(t),sub) => Some( (sub, t) )
    case _ => None
  }
}

object ExVar {
  def apply(variable: FOLVar, sub: FOLFormula) = Ex(FOLAbs(variable, sub))
  def unapply(expression: LambdaExpression) = expression match {
    case Ex(Abs(variable: FOLVar, sub: FOLFormula), _) => Some( (variable, sub) )
    case _ => None
  }
}

object AllVar {
  def apply(variable: FOLVar, sub: FOLFormula) = All(FOLAbs(variable, sub))
  def unapply(expression: LambdaExpression) = expression match {
    case All(Abs(variable: FOLVar, sub: FOLFormula), _) => Some( (variable, sub) )
    case _ => None
  }
}

object BinaryLogicSymbol {
  def unapply(expression: LambdaExpression) = expression match {
    case And(l, r) => Some( (AndC, l, r) )
    case Or(l, r) => Some( (OrC, l, r) )
    case Imp(l, r) => Some( (ImpC, l, r) )
    case _ => None
  }
}

object FOLFactory extends LambdaFactoryA {
  import at.logic.language.fol.Utils._

  def createVar( name: SymbolA, exptype: TA, dbInd: Option[Int] ) : Var = exptype match {
    case Ti() => name match {
      case a: ConstantSymbolA => FOLConst(a)
      case a: VariableSymbolA => new FOLVar(a,dbInd)
    }
    case To() => name match {
      case a: ConstantSymbolA => new HOLConstFormula(a) with FOLFormula
      case _ => throw new Exception("In FOL, of type 'o' only constants may be created.")
    }
    case ->(tr, ta) => {
      if (!(isFirstOrderType(exptype)))
        throw new Exception("In FOL, cannot create a symbol of type " + exptype)
      name match {
        case a: ConstantSymbolA => new HOLConst(a, exptype) with FOLExpression
        case _ => throw new Exception("In FOL, of type 'a -> b' only constants may be created.")
      }
    }
  }

  def createVar( name: SymbolA ) : Var = createVar( name, Ti() )

  def createApp( fun: LambdaExpression, arg: LambdaExpression ) : App =
    if (HOLFactory.isFormulaWhenApplied(fun.exptype)) new HOLAppFormula(fun, arg) with FOLFormula
    else if (isTermWhenApplied(fun.exptype)) new FOLApp(fun, arg) with FOLTerm
    else new FOLApp(fun, arg)

  def createAbs( variable: Var, exp: LambdaExpression ) : Abs =  new HOLAbs( variable, exp ) with FOLExpression

  private def isTermWhenApplied(typ: TA) = typ match {
    case ->(_,Ti()) => true
    case _ => false
  }

}

object getFreeVariablesFOL {
  def apply( f: FOLFormula ) = f.freeVariables.asInstanceOf[Set[FOLVar]]
}

object FOLSubstitution
{
  def apply(f: FOLFormula, x: FOLVar, t: FOLTerm) : FOLFormula =
  {
    val sub = Substitution(x, t.asInstanceOf[FOLExpression])
      sub( f.asInstanceOf[FOLExpression]
         ).asInstanceOf[FOLFormula]
  }

  def apply(f: FOLTerm, x: FOLVar, t: FOLTerm) : FOLTerm =
  {
    val sub = Substitution(x,
        t.asInstanceOf[FOLExpression])
      sub(
          f.asInstanceOf[FOLExpression]
         ).asInstanceOf[FOLTerm]
  }
}

