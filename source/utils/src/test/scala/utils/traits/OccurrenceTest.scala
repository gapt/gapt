package at.logic.utils.traits

import org.specs.SpecificationWithJUnit


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
          "without occurrences" in {new Temp2(1) must beEqual (new Temp2(1))}
          "with occurrences" in {new Temp(1) mustNot beEqual (new Temp(1))}  //uses pointer equiality
        }
    }
}