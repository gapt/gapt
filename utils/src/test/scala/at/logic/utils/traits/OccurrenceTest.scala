package at.logic.utils.traits

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class OccurrenceTest extends SpecificationWithJUnit {
    "OccurrenceTest" should {
        " check whether there is a pointer equality " in {
          class Temp2(val x: Int) {
           override def equals(y: Any): Boolean = y match {
             case z: Temp2 => x == z.x
             case _ => false
           }
          }
          class Temp(x: Int) extends Temp2(x) with Occurrence
          "without occurrences" in {new Temp2(1) must beEqualTo (new Temp2(1))}
          "with occurrences" in {new Temp(1) must not be equalTo (new Temp(1))}  //uses pointer equiality
        }
    }
}