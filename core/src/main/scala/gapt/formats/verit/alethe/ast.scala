package gapt.formats.verit.alethe

case class AletheProof(steps: List[ProofCommand])

sealed trait ProofCommand {
  val label: String
  val premises: List[String]
}
case class Step(
    rule: String,
    override val label: String,
    clause: List[Term],
    premises: List[String],
    arguments: List[Argument]
) extends ProofCommand

case class Assume(label: String, formula: Term) extends ProofCommand {
  val premises = Nil
}

case class Anchor(label: String, arguments: Option[List[(VariableDeclaration, Term)]]) extends ProofCommand {
  val premises = Nil
}

case class Argument(t: Term, v: Option[String])
case class Sort(name: String)
case class VariableDeclaration(name: String, sort: Option[Sort])

sealed trait Term

trait SpecialConstant extends Term
case object True extends SpecialConstant
case object False extends SpecialConstant
case class Numeral(n: Int) extends SpecialConstant

case class Identifier(name: String, sort: Option[Sort]) extends Term
case class Forall(vars: List[VariableDeclaration], f: Term) extends Term
case class Exists(vars: List[VariableDeclaration], f: Term) extends Term
case class Application(identifier: String, terms: List[Term]) extends Term
case class Let(bindings: List[(String, Term)], term: Term) extends Term
case class Not(t: Term) extends Term
