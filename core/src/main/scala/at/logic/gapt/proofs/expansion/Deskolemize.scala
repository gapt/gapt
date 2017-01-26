package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lk.SolveUtils
import at.logic.gapt.utils.{Logger, NameGenerator}

import scala.collection.immutable.Iterable

/**
 * Created by matthias on 5/12/16.
 */
object Deskolemize extends Deskolemize {
}

class Deskolemize extends SolveUtils with Logger {
  type Error = (Seq[ETImp], ExpansionSequent)

  def replacement(t: LambdaExpression, skolemTerms: Set[LambdaExpression], nameGenerator: NameGenerator): Option[(LambdaExpression, LambdaExpression)] =
    t match {
    case a @ App(e1, e2) if skolemTerms.contains(e1) => Some((a, Var(nameGenerator.fresh("v"), Ti)))
    case App(e1, e2) if !skolemTerms.contains(e1) => replacement(e2, skolemTerms, nameGenerator)
    case c: Const if skolemTerms.contains(c) => Some((c, Var(nameGenerator.fresh("v"), Ti)))
    case _ => None
  }

  def apply(expansionProof: ExpansionProof): Sequent[ExpansionTree] = {

    val skolemTerms: Set[LambdaExpression] = expansionProof.skolemFunctions.skolemDefs.keys.toSet
    println(expansionProof.skolemFunctions)
    val nameGenerator = rename.awayFrom(containedNames(expansionProof))
    println(s"skolemTerms: $skolemTerms")
    val repl: Map[LambdaExpression, LambdaExpression] = skolemTerms.collect {
      case c: Const if c.exptype == Ti => (c, Var(nameGenerator.fresh( "v" ), Ti))
      case c: Const => (c, Var(nameGenerator.fresh( "v" ), Ti))
      //case c: Const => (App(c, ), Var(nameGenerator.fresh( "v" ), Ti))
      case a @ App(e, _)  => (a, Var(nameGenerator.fresh( "v" ), Ti))
    }.toMap
    println(repl)

    val terms = for {e <- expansionProof.expansionSequent} yield collect(e)
    println(s"terms: $terms")
    println("flatmap: " + terms.elements.reduce(_ union _).flatMap(replacement(_, skolemTerms, nameGenerator)))
    val m: Set[LambdaExpression] = terms.elements.reduce(_ union _)
    val n = m.flatMap(replacement(_, skolemTerms, nameGenerator)).toMap
    println("map " + n)
    // TODO f shouldn't always get a fresh variable, reuse for terms already seen
    var mm: Map[LambdaExpression, LambdaExpression] = Map.empty
    def f: PartialFunction[LambdaExpression, LambdaExpression] = {
      case a@App(e1, e2) if skolemTerms.contains(e1) => {
        if (!mm.contains(a)) {
          val v = Var(nameGenerator.fresh("v"), Ti)
          mm = mm.+((a, v))
          v
        } else {
          mm(a)
        }
      }
      case c: Const if skolemTerms.contains(c) => {
        if (!mm.contains(c)) {
          val v = Var(nameGenerator.fresh("v"), Ti)
          mm = mm.+((c, v))
          v
        } else {
          mm(c)
        }
      }
    }
    apply(expansionProof.expansionSequent, f)(skolemTerms, nameGenerator)
  }

  def apply(es: ExpansionSequent, repl: PartialFunction[LambdaExpression, LambdaExpression])(implicit skolemTerms: Set[LambdaExpression], nameGenerator: NameGenerator): ExpansionSequent = {
    for { e <- es } yield apply(e, repl)
  }

  def apply(e: ExpansionTree, repl: PartialFunction[LambdaExpression, LambdaExpression])(implicit skolemTerms: Set[LambdaExpression], nameGenerator: NameGenerator): ExpansionTree = {
    rm(e, repl)
  }

  // TODO unify with replaceET? code is very similar
  def rm( et: ExpansionTree, repl: PartialFunction[LambdaExpression, LambdaExpression])(implicit skolemTerms: Set[LambdaExpression], nameGenerator: NameGenerator): ExpansionTree = et match {
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
            println(s"selectedTerm: $selectedTerm")
            val t = TermReplacement(selectedTerm, repl)
            println(s"t: $t")

            (TermReplacement(selectedTerm, repl), rm(child, repl))
        }
      )
    case ETStrongQuantifier( shallow, eigenVariable, child ) =>
      ETStrongQuantifier(
        TermReplacement( shallow, repl ),
        TermReplacement( eigenVariable, repl ).asInstanceOf[Var], rm( child, repl )
      )
    case ETSkolemQuantifier( shallow, skolemTerm, skolemDef, child ) =>
      println(s"skolemTerm: $skolemTerm")
      val t = TermReplacement(skolemTerm, repl)
      println(s"t: $t")
      println("shallow: "+ TermReplacement(shallow, repl))
      val m = rm(child, repl)
      println("child: " +m )
      ETStrongQuantifier(
        TermReplacement(shallow, repl),
        TermReplacement(skolemTerm, repl).asInstanceOf[Var],
        rm(child, repl))
  }


  // TODO unify with replaceET? code is very similar
  def collect( et: ExpansionTree): Set[LambdaExpression] = et match {
    case ETMerge( child1, child2 ) => collect(child1) union collect(child2)

    case et @ ETWeakening( formula, _ ) =>
      Set.empty
    case et @ ETAtom( atom, _ ) =>
      Set.empty
    case ETDefinedAtom( atom, pol, definition ) =>
      Set.empty
    case _: ETTop | _: ETBottom  =>
      Set.empty
    case ETNeg( child )          => collect(child)
    case ETAnd( child1, child2 ) => collect(child1) union collect(child2)
    case ETOr( child1, child2 )  => collect(child1) union collect(child2)
    case ETImp( child1, child2 ) => collect(child1) union collect(child2)

    case ETWeakQuantifier( shallow, instances ) =>
        val t: Iterable[Set[LambdaExpression]] = instances.map {
          case (selectedTerm, child) =>
            collect(child) union Set(selectedTerm)
        }
        t.reduce(_ union _)
    case ETStrongQuantifier( shallow, eigenVariable, child ) =>
      collect(child)
    case ETSkolemQuantifier( shallow, skolemTerm, skolemDef, child ) =>
      collect(child) union Set(skolemTerm)
  }
}
