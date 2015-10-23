import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.expr.fol.reduceHolToFol
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.expr._
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.grammars.{minimizeRecursionScheme, Rule, RecursionScheme, RecSchemTemplate}
import at.logic.gapt.proofs.expansionTrees.{InstanceTermEncoding, extractInstances}
import at.logic.gapt.proofs.lkNew.LKToExpansionProof
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.veriT.VeriT

val tipProblem = TipSmtParser parse """
  (declare-sort sk_a 0)
  (declare-datatypes ()
    ((list (nil) (cons (head sk_a) (tail list)))))
  (define-fun-rec
    qrev
      ((x list) (y list)) list
      (match x
        (case nil y)
        (case (cons z xs) (qrev xs (cons z y)))))
  (assert-not (forall ((x list)) (= (qrev (qrev x nil) nil) x)))
  (check-sat)
"""

val sequent = tipProblem toSequent

val list = TBase("list")
val sk_a = TBase("sk_a")
val nil = Const("nil", list)
val cons = Const("cons", sk_a -> (list -> list))

def mkList(i: Int) = (0 until i).foldRight[LambdaExpression](nil) { (j, l) => cons(Const(s"a$j", sk_a), l) }

val instances = 0 to 2 map mkList

// Compute many-sorted expansion sequents
val instanceProofs = instances map { inst =>
  val instanceSequent = sequent.map(identity, instantiate(_, inst))
  val erasure = (constants(instanceSequent) ++ variables(instanceSequent)).zipWithIndex.flatMap {
    case (EqC(_), _) => None
    case (c@NonLogicalConstant(name, FunctionType(To, argTypes)), i) =>
      Some(c -> FOLAtomHead(s"P_${name}_$i", argTypes.size))
    case (c@NonLogicalConstant(name, FunctionType(_, argTypes)), i) =>
      Some(c -> FOLFunctionHead(s"f_${name}_$i", argTypes.size))
    case (v@Var(name, TBase(ty)), i) =>
      Some(v -> FOLVar(s"x_${name}_${ty}_$i"))
  }.toMap[LambdaExpression, LambdaExpression]
  val erasedInstanceSequent = instanceSequent map { TermReplacement(_, erasure) }
  val Some(erasedProof) = Prover9 getLKProof erasedInstanceSequent
  val erasedExpansion = LKToExpansionProof(erasedProof)
  val reifiedExpansion = erasedExpansion map { TermReplacement(_, erasure.map(_.swap)) }
  inst -> reifiedExpansion
}

instanceProofs foreach { case (inst, es) =>
  println(s"Instances for x = $inst:")
  extractInstances(es).map(-_, identity).elements foreach println
  println()
}

val alpha = Var("alpha", list)
val encoding = InstanceTermEncoding(sequent.map(identity, instantiate(_, alpha)))

val A = Const("A", list -> encoding.instanceTermType)
val G = Const("G", list -> (list -> encoding.instanceTermType))
val x = Var("x", list)
val y = Var("y", sk_a)
val w = Var("w", list)
val w2 = Var("w2", list)
val z = Var("z", encoding.instanceTermType)

val template = RecSchemTemplate(A,
  A(x) -> G(x, w2), A(x) -> z,
  G(cons(y, x), w) -> G(x, w2),
  G(cons(y, x), w) -> z,
  G(nil, w) -> z)

val targets = for ((inst, es) <- instanceProofs; term <- encoding encode es) yield A(inst) -> term
val stableRS = template.stableRecSchem(targets.toSet)
// FIXME: the class of rs w/o skolem symbols is not closed under the rewriting that stableTerms() expects :-/
val stableRSWithoutSkolemSymbols =
  RecursionScheme(stableRS.axiom, stableRS.nonTerminals,
    stableRS.rules filterNot { case Rule(from, to) =>
        constants(to) exists { _.exptype == sk_a }
    })
//println(stableRSWithoutSkolemSymbols)
val rs = minimizeRecursionScheme( stableRSWithoutSkolemSymbols, targets, template.targetFilter )
println(s"Minimized recursion scheme:\n$rs\n")

val inst = mkList(8)
val lang = Substitution(alpha -> inst)(encoding decodeToInstanceSequent rs.parametricLanguage(inst))
lang.elements foreach println
println(VeriT isValid reduceHolToFol(lang))
