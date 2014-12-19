package at.logic.algorithms.expansionTrees

import at.logic.language.hol.{Atom => AtomHOL, And => AndHOL, Or => OrHOL, Imp => ImpHOL, _}
import at.logic.language.lambda.types.{Ti => i, To => o, ->}
import at.logic.calculi.expansionTrees._
import at.logic.calculi.lk.base.FSequent
import at.logic.algorithms.expansionTrees._
import at.logic.provers.minisat.MiniSATProver
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class minimalExpansionSequentTest extends SpecificationWithJUnit {

  val x = HOLVar(("x" ), i)
  val c = HOLConst(("c" ), i)
  val d = HOLConst(("d" ), i)
  val P = HOLConst("P", i -> o)
  
  val et1: ExpansionTree = merge(
    WeakQuantifier(
      AllVar(x, AtomHOL(P,x::Nil)),
      List((Atom(AtomHOL(P,c::Nil)),c),(Atom(AtomHOL(P,d::Nil)),d))
      )
  )

  val et2: ExpansionTree = merge(
    WeakQuantifier(
      ExVar(x, AtomHOL(P, x::Nil)),
      List((Atom(AtomHOL(P, c::Nil)),c),(Atom(AtomHOL(P,d::Nil)),d))
     )
  )
  
  val eSeq = compressQuantifiers(ExpansionSequent(List(et1), List(et2)))
  
  val minESeq = List(
    ExpansionSequent(List(merge(
    WeakQuantifier(
      AllVar(x, AtomHOL(P,x::Nil)),
      List((Atom(AtomHOL(P,c::Nil)),c))
    )
  )), List(merge(
    WeakQuantifier(
      ExVar(x, AtomHOL(P, x::Nil)),
      List((Atom(AtomHOL(P, c::Nil)),c))
    )
  ))),
    ExpansionSequent(List(merge(
    WeakQuantifier(
      AllVar(x, AtomHOL(P,x::Nil)),
      List((Atom(AtomHOL(P,d::Nil)),d))
    )
  )), List(merge(
    WeakQuantifier(
      ExVar(x, AtomHOL(P, x::Nil)),
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
