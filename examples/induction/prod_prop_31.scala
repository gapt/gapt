import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.expr._
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.expansionTrees.extractInstances
import at.logic.gapt.proofs.lkNew.LKToExpansionProof
import at.logic.gapt.provers.prover9.Prover9

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

val instances = 0 to 4 map { i => (0 until i).foldRight[LambdaExpression](nil) { (j, l) => cons(Const(s"a$j", sk_a), l) } }

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
  extractInstances(es).map(identity, -_).elements foreach println
  println()
}
