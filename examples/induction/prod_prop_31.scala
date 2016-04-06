package at.logic.gapt.examples.induction
import at.logic.gapt.examples.Script
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.provers.inductionProver._

object prod_prop_31 extends Script {
  val tipProblem = TipSmtParser parse
    """
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

  Viper solve tipProblem
}
