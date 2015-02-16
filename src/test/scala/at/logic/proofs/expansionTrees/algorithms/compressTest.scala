package at.logic.proofs.expansionTrees.algorithms

import at.logic.language.hol.{HOLAnd => AndHOL, HOLAtom => AtomHOL, HOLImp => ImpHOL, HOLOr => OrHOL, _}
import at.logic.language.lambda.types.{Ti => i, To => o}
import at.logic.proofs.expansionTrees._
import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner


@RunWith(classOf[JUnitRunner])
class compressTest extends SpecificationWithJUnit {

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
  
  val eSeq = ExpansionSequent(List(et1), List(et2))

  val meSeq = compressQuantifiers(eSeq)
  val eSeq2 = decompressQuantifiers(meSeq)
  
  "Expansion tree compression and decompression" should {
    "be computed correctly" in {
      eSeq2 mustEqual eSeq
    }
  }
}
