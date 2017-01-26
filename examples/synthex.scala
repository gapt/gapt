import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.expansion.{ deskolemizeET, ExpansionProof, ExpansionProofToLK }
import at.logic.gapt.provers.vampire.Vampire

object synthex extends Script {

  val peano5 = hof"!x 0 = x*0"
  val peano7 = hof"!x!y (x<y -> s(x)<s(y))"
  val lem1 = hof"!x s(pow2(s x)) < pow2(s(s x))"
  val lem2 = hof"!x pow2(x) < pow2(s x)"
  val lem4 = hof"!x!y (y<x | x<y | x=y)"
  val lem5 = hof"!x!y!z (y<z & x<y -> x<z)"
  val defleq = hof"!x!y (x<=y <-> (x=y | x<y))"
  val defpow2 = hof"!x x*x = pow2(x)"
  val defind = hof"!x (i(x) <-> ?y (x < pow2(s y) & pow2(y) <= x))"
  val thm1 =
    hof"""!y!x (
    s(x)<pow2(s y) & x<pow2(s y) & pow2(y)<=x ->
      s(x)<pow2(s y) & pow2(y)<=s(x)
  )"""
  val ind = hof"!x (i x -> i(s x)) & i 0 -> !x i x"

  val thm = hof"!x i(x)"

  //val problem = peano5 +: peano7 +: lem1 +: lem2 +: lem4 +: lem5 +:
  //  defleq +: defpow2 +: defind +: ind +: thm1 +: Sequent() :+ thm

  val problem = Sequent() :+ hof"?x (P x -> !y (x = x & P y))"
  println( "Problem" )
  println( problem )

  val expansionProof: Option[ExpansionProof] = Vampire getExpansionProof problem
  println( expansionProof.get )
  val desk: ExpansionProof = deskolemizeET( expansionProof.get )
  println( desk )
  println( ExpansionProofToLK( desk ) )

  /*
  var i = 918
  var break = false
  while (i < 100000 && !break) {
    try {
      println ("trying seed " + i)
      val vmp = new Vampire(commandName = "vampire", extraArgs = Seq("--time_limit", "1m", "--random_seed", i.toString))
      val expansionProof: Option[ExpansionProof] = vmp getExpansionProof problem
      println(expansionProof.get)

      val desk: Sequent[ExpansionTree] = Deskolemize(expansionProof.get)
      println(desk)

      println(ExpansionProofToLK(ExpansionProof(desk)))
      break = true
    } catch {
      case e => println ("timeout")
    }
    i+=1
  }
  */
}
