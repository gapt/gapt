package at.logic.proofs.expansionTrees.algorithms

import at.logic.language.hol.{HOLAnd => AndHOL, HOLAtom => AtomHOL, HOLImp => ImpHOL, HOLOr => OrHOL, _}
import at.logic.language.lambda.types.{Ti => i, To => o}
import at.logic.proofs.expansionTrees._
import at.logic.provers.minisat.MiniSATProver
import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class minimalExpansionSequentTest extends SpecificationWithJUnit {

  val x = HOLVar(("x" ), i)
  val c = HOLConst(("c" ), i)
  val d = HOLConst(("d" ), i)
  val P = HOLConst("P", i -> o)
  
  val et1: ExpansionTree = merge(
    WeakQuantifier(
      HOLAllVar(x, AtomHOL(P,x::Nil)),
      List((Atom(AtomHOL(P,c::Nil)),c),(Atom(AtomHOL(P,d::Nil)),d))
      )
  )

  val et2: ExpansionTree = merge(
    WeakQuantifier(
      HOLExVar(x, AtomHOL(P, x::Nil)),
      List((Atom(AtomHOL(P, c::Nil)),c),(Atom(AtomHOL(P,d::Nil)),d))
     )
  )
  
  val eSeq = compressQuantifiers(ExpansionSequent(List(et1), List(et2)))
  
  val minESeq = List(
    ExpansionSequent(List(merge(
    WeakQuantifier(
      HOLAllVar(x, AtomHOL(P,x::Nil)),
      List((Atom(AtomHOL(P,c::Nil)),c))
    )
  )), List(merge(
    WeakQuantifier(
      HOLExVar(x, AtomHOL(P, x::Nil)),
      List((Atom(AtomHOL(P, c::Nil)),c))
    )
  ))),
    ExpansionSequent(List(merge(
    WeakQuantifier(
      HOLAllVar(x, AtomHOL(P,x::Nil)),
      List((Atom(AtomHOL(P,d::Nil)),d))
    )
  )), List(merge(
    WeakQuantifier(
      HOLExVar(x, AtomHOL(P, x::Nil)),
      List((Atom(AtomHOL(P, d::Nil)),d))
    )
  )))
  ).map(compressQuantifiers.apply)
  
  args(skipAll = !(new MiniSATProver).isInstalled())

  "Minimal expansion trees" should {
    "be computed correctly by the smart algorithm" in {
      minESeq mustEqual minimalExpansionSequents(eSeq, new MiniSATProver)
    }
  }
}
