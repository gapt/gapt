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
class compressTest extends SpecificationWithJUnit {

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
  
  val eSeq = ExpansionSequent(List(et1), List(et2))

  val meSeq = compressQuantifiers(eSeq)
  val eSeq2 = decompressQuantifiers(meSeq)
  
  "Expansion tree compression and decompression" should {
    "be computed correctly" in {
      eSeq2 mustEqual eSeq
    }
  }
}
