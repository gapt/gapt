package at.logic.utils.traits

/**
 * Created by IntelliJ IDEA.
 * User: shaolin
 * Date: 8/30/11
 * Time: 4:13 PM
 * To change this template use File | Settings | File Templates.
 */

//objects mixed with occurrence are always pointerwise equal
trait Occurrence {

  // in order to make sure a == b <=> b == a (we sometime override this method to give a different behavior than pointers
  // like, for example, when we wrap an occurrence within another occurrence but we want the equality to be according to the inner
  // occurrence).Our solution is to have an auxiliary trait extending Occurrence whose equals will always be used
  override def equals(a: Any): Boolean = a match {
    case o: NestingOccurrence => o.nestedOccurrence eq this
    case o: Occurrence => this eq o
    case _ => false
  }

  // hashcode does not need to be overriden as equals now means the two points to the same
  // address and therefore has the same hashcode.
}

// any class extending occurrence and overriding equals must extend this trait. this will solve problems when comparing
// occurrence with auxOccurrence but will not solve problems of comparing two aux occurrences (see Clause wrappers for formulaoccurrence)
trait NestingOccurrence extends Occurrence {
  val nestedOccurrence: Occurrence

  override def equals(a: Any): Boolean = a match {
    case o: NestingOccurrence => nestedOccurrence eq o.nestedOccurrence
    case o: Occurrence => nestedOccurrence eq o
    case _ => false
  }
}