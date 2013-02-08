package at.logic.algorithms.hlk

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import java.io.File.separator
import java.io.{FileInputStream, InputStreamReader}
import org.specs2.execute.Success
import at.logic.parsing.readers.StringReader
import at.logic.calculi.lk.base.LKProof
import collection.immutable

@RunWith(classOf[JUnitRunner])
class LKParserTest extends SpecificationWithJUnit {
  private class MyParser extends StringReader("")
  "LKParser" should {
    val path = "target" + separator + "test-classes" + separator

    "parse correctly a FO LK-proof" in {
      val s = new InputStreamReader(new FileInputStream(path + "proof1.lk"))
      val db = LKProofParser.parseProof(s)
      //val pmap = immutable.Map.empty[String,LKProof] ++ db.proofs
      db.proofs must not beEmpty

      db.proofs map ( x => println("Proof "+x._1 + " of end-sequent "+x._2.root))
      //println("\n\nend_seq = "+  pmap("\\psi").root  )
      Success()
    }


    "parse correctly the tape proof" in {
      val s = new InputStreamReader(new FileInputStream(path + "tape-in2.lk"))
      val db = LKProofParser.parseProof(s)
      val pmap = immutable.Map.empty[String,LKProof] ++ db.proofs
      println("\n\nend_seq = "+  pmap("\\psi").root  )
      Success()
    }


  }
}


