package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lk.SolveUtils
import at.logic.gapt.utils.Logger

/**
 * Created by matthias on 5/12/16.
 */
object Deskolemize extends Deskolemize {
}

class Deskolemize extends SolveUtils with Logger {
  type Error = (Seq[ETImp], ExpansionSequent)

  // TODO take an ExpansionProof, not ExpansionSequent
  def apply(expSequent: Sequent[ExpansionTree]): Sequent[ExpansionTree] = {

    //val skFuns = println(ExpansionProof(expSequent).skolemFunctions)

    //val deskAnt = for { (a, e) <- antecedent } yield desk(false, 0, Nil, a, e)
    val deskAnt = for { e <- expSequent.antecedent } yield rm(e, PartialFunction.empty)
    //val deskSucc = for { (b, f) <- succedent } yield desk(true, 0, Nil, b, f)
    val deskSucc = for { e <- expSequent.succedent } yield rm(e, PartialFunction.empty)
    Sequent(deskAnt, deskSucc)


    //for { e <- expSequent } yield cleanStructureET(desk(polarity = false, 0, Nil, e.shallow, e))
  }

  // TODO unify with replaceET, code is very similar
  def rm( ep: ExpansionProof, repl: PartialFunction[LambdaExpression, LambdaExpression] ): ExpansionProof =
    ExpansionProof( ep.expansionSequent map { rm( _, repl ) } )

  def rm( et: ExpansionTree, repl: PartialFunction[LambdaExpression, LambdaExpression] ): ExpansionTree = et match {
    case ETMerge( child1, child2 ) => ETMerge( rm( child1, repl ), rm( child2, repl ) )

    case et @ ETWeakening( formula, _ ) =>
      et.copy( formula = TermReplacement( formula, repl ) )
    case et @ ETAtom( atom, _ ) =>
      et.copy( atom = TermReplacement( atom, repl ) )
    case ETDefinedAtom( atom, pol, definition ) =>
      ETDefinedAtom( TermReplacement( atom, repl ), pol, TermReplacement( definition, repl ) )

    case _: ETTop | _: ETBottom  => et
    case ETNeg( child )          => ETNeg( rm( child, repl ) )
    case ETAnd( child1, child2 ) => ETAnd( rm( child1, repl ), rm( child2, repl ) )
    case ETOr( child1, child2 )  => ETOr( rm( child1, repl ), rm( child2, repl ) )
    case ETImp( child1, child2 ) => ETImp( rm( child1, repl ), rm( child2, repl ) )

    case ETWeakQuantifier( shallow, instances ) =>
      ETWeakQuantifier.withMerge(
        TermReplacement(shallow, repl),
        instances.map {
          case (selectedTerm, child) =>
            // TODO: pick variable not in expansion tree
            val v = Var("z", selectedTerm.exptype)
            def f: PartialFunction[LambdaExpression, LambdaExpression] = {
              // TODO check if t is a skolem function
              case t if t.toString == "s_0(X0)" => v
            }
            val newRepl = repl.orElse(f)
            (TermReplacement(selectedTerm, newRepl), rm(child, newRepl))
        }
      )
    case ETStrongQuantifier( shallow, eigenVariable, child ) =>
      ETStrongQuantifier(
        TermReplacement( shallow, repl ),
        TermReplacement( eigenVariable, repl ).asInstanceOf[Var], rm( child, repl )
      )
    case ETSkolemQuantifier( shallow, skolemTerm, skolemDef, child ) =>
      // TODO: pick variable not in expansion tree
      val v = Var("z", skolemTerm.exptype)
      def f: PartialFunction[LambdaExpression, LambdaExpression] = {
          case t if t == skolemTerm => v
      }
      ETStrongQuantifier(
        TermReplacement(shallow, repl),
        TermReplacement(skolemTerm, repl).asInstanceOf[Var],
        rm(child, repl.orElse(f)))
  }


  def rm(e: ExpansionTree): ExpansionTree = {
    e match {
      case ETMerge( child1, child2 ) => ETMerge( rm(child1), rm(child2) )

      case e @ ETWeakening( formula, _ ) => e
      case e @ ETAtom( atom, _ ) => e
      case ETDefinedAtom( atom, pol, definition ) => e
      case _: ETTop | _: ETBottom  => e
      case ETNeg( child )          => ETNeg( rm( child ) )
      case ETAnd( child1, child2 ) => ETAnd( rm( child1 ), rm( child2 ) )
      case ETOr( child1, child2 )  => ETOr( rm( child1 ), rm( child2 ) )
      case ETImp( child1, child2 ) => ETImp( rm( child1 ), rm( child2 ) )
      case ETWeakQuantifier( shallow, instances ) =>
        ETWeakQuantifier(shallow, instances map {
          case (ev,inst) =>
            val v = Var("z", ev.exptype)
            def f: PartialFunction[LambdaExpression, LambdaExpression] = {
              case t if t.toString == "s_0(X0)" => v
            }
            println("ev " + ev + " " + ev.exptype)
            println("inst: " + inst)
            val c = replaceET(inst, f)
            println("c: " + c)
            (v, rm(c))
            //(ev, rm(inst))
        })
      case ETStrongQuantifier( shallow, eigenVariable, child ) =>
        ETStrongQuantifier(shallow, eigenVariable, rm(child))
      case ETSkolemQuantifier(shallow, skolemTerm, skolemDef, child) =>
        val v = Var("z", skolemTerm.exptype)
        def f: PartialFunction[LambdaExpression, LambdaExpression] = {
            case t if t == skolemTerm => v
        }
        val c = replaceET(child, f)
        ETStrongQuantifier(shallow, v , rm(c))
      case _ =>
        println(e.getClass)
        e
    }
  }

  def desk(polarity: Boolean, m: Int, selected: List[LambdaExpression], a: HOLFormula, e: ExpansionTree) : ExpansionTree = {
    debug ("------------------------------------------------------------------")
    debug ("polarity : " + polarity)
    debug ("m        : " + m)
    debug ("selected : " + selected)
    println("BEFORE")
    println("polarity : " + polarity)
    println("a.class: " + a.getClass)
    println("e.class: " + e.getClass)
    println("a: " + a)
    println("e: " + e)
    debug ("class    : " + e.getClass)
    debug ("e.deep   : " + e.deep)
    debug ("e.shallow: " + e.shallow)
    val ret =
    (a, e) match {
      case (_, ETBottom(_)) => e
      case (_, ETTop(_))    => e
      case (Neg(a1), ETNeg(e1)) =>
        ETNeg(desk(!polarity, m, selected, a1, e1))
      case (Or(a1, a2), ETOr(e1, e2)) =>
        debug( "Or a1: " + a1)
        debug( "Or a2: " + a2)
        debug( "Or e1: " + e1)
        debug( "Or e2: " + e2)
        val q = qocc(a1, polarity)
        debug("qocc: " + q)
        ETOr(
          desk( polarity, m, selected, a1, e1 ),
          desk( polarity, m + q, selected, a2, e2 )
        )
      case (And(a1, a2), ETAnd(e1, e2)) =>
        debug( "And a1: " + a1)
        debug( "And a2: " + a2)
        debug( "And e1: " + e1)
        debug( "And e2: " + e2)
        val q = qocc(a1, polarity)
        debug("qocc: " + q)
        ETAnd(
          desk( polarity, m, selected, a1, e1 ),
          desk( polarity, m + q, selected, a2, e2 )
        )
      case (Imp(a1, a2), ETImp(e1, e2)) =>
        debug( "Imp a1: " + a1)
        debug( "Imp a2: " + a2)
        debug( "Imp e1: " + e1)
        debug( "Imp e2: " + e2)
        val q = qocc(a1, polarity)
        debug("qocc: " + q)
        ETImp(
          desk(!polarity, m, selected, a1, e1 ),
          desk(polarity, m + q, selected, a2, e2)
        )
      case (All(x, a1), _) if polarity =>
        val sym = Const( "s_0", FunctionType( x.exptype, selected.map( _.exptype ) ) )
        //val sym = Const( "s_" + (m + 1), FunctionType( x.exptype, selected.map( _.exptype ) ) )
        val skolemFunction = sym( selected: _* )
        debug("STRONG ALL: ")

        val fprime: HOLFormula = Substitution( x -> skolemFunction )(a1)
        debug ("fprime: " + fprime)
        val inner = desk(polarity = true, m+1, selected, fprime, e)
        debug("inner: " + inner)
        ETSkolemQuantifier(a, skolemFunction, Abs(x, a), inner)
      case (All(x, a1), q @ ETWeakQuantifier(s, i)) if !polarity =>
        debug( "WeakQuantifier x: " + x)
        debug( "WeakQuantifier a1: " + a1)
        debug( "WeakQuantifier s: " + s)
        debug( "WeakQuantifier i: " + i)

        val tmp = i.map{ case (t, v) =>
          val fprime: HOLFormula = Substitution( x -> t )(a1)
          debug( "WeakQuantifier v: " + v)
          debug( "WeakQuantifier f: " + a1 + "\n  {" + x + " -> " + t + "}--> fprime: " + fprime)
          t -> desk(polarity = false, m, t :: selected, fprime, v)
        }
        debug( "WeakQuantifier tmp: " + tmp)
        ETWeakQuantifier(a, tmp)
      case (Ex(x, a1), _) if !polarity =>
        val sym = Const( "s_0", FunctionType( x.exptype, selected.map( _.exptype ) ) )
        //val sym = Const( "s_" + (m + 1), FunctionType( x.exptype, selected.map( _.exptype ) ) )
        val skolemFunction = sym( selected: _* )
        debug("STRONG EX: ")

        val fprime: HOLFormula = Substitution( x -> skolemFunction )(a1)
        debug ("fprime: " + fprime)
        val inner = desk(polarity = false, m+1, selected, fprime, e)
        debug("inner: " + inner)
        ETSkolemQuantifier(a, skolemFunction, Abs(x, a), inner)
      case (Ex(x, a1), q @ ETWeakQuantifier(s, i)) if polarity =>
        debug( "WeakQuantifier x: " + x)
        debug( "WeakQuantifier a1: " + a1)
        debug( "WeakQuantifier s: " + s)
        debug( "WeakQuantifier i: " + i)
        val tmp = i.map{ case (t, v) =>
          val fprime: HOLFormula = Substitution( x -> t )(a1)
          debug( "WeakQuantifier v: " + v)
          debug( "WeakQuantifier f: " + a1 + "\n  {" + x + " -> " + t + "}--> fprime: " + fprime)
          t -> desk(polarity = true, m, t :: selected, fprime, v)
        }
        debug( "WeakQuantifier tmp: " + tmp)
        ETWeakQuantifier(a, tmp)
      case (FOLAtom(_,_), ETAtom(_, _)) =>
        debug ("ETAtom " + e)
        e
      case (_, _) =>
        println( "UNSUPPORTED" )
        println("a.class: " + a.getClass)
        println("e.class: " + e.getClass)
        println("a: " + a)
        println("e: " + e)
        e
    }
    println("---------------------------")
    println("a: " + a)
    println("a.class: " + a.getClass)
    println("e: " + e)
    println("e.class: " + e.getClass)
    println("e.shallow: " + e.shallow)
    println("e.deep: " + e.deep)
    println("desk ret: " + ret)
    println("---------------------------")
    ret
  }


  def qocc(a: LambdaExpression, polarity: Boolean): Int = {
    a match {
      case Neg(a1)     => qocc(a1, !polarity)
      case Or(a1, a2)  => qocc(a1, polarity) + qocc(a2, polarity)
      case And(a1, a2) => qocc(a1, polarity) + qocc(a2, polarity)
      case Imp(a1, a2) => qocc(a1, !polarity) + qocc(a2, polarity)
      case Ex(_, a1) if polarity   => qocc(a1, true)
      case Ex(_, a1) if !polarity  => 1 + qocc(a1, false)
      case All(_, a1) if polarity  => 1 + qocc(a1, true)
      case All(_, a1) if !polarity => qocc(a1, false)
      case _   => 0
    }
  }
  /*
  def pr(sequent: Sequent): LKProof = TopAxiom

  def permL(i: Int, sequent: Sequent, proof: LKProof) = ()

  def permR(i: Int, sequent: Sequent, proof: LKProof) = ()
  */
}
