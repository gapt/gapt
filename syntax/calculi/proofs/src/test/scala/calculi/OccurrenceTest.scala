package at.logic.calculi

import at.logic.calculi.occurrences._
import org.specs._
import at.logic.language.hol._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._
import scala.collection.immutable.Set
/**
 * The following properties of each rule are tested:
 * 1) The right principal formula is created
 * 2) The principal formula is managed correctly
 * 3) The Auxiliaries formulas are managed in the correct way
 * 4) The context is unchanged with regard to multiset equality
 * 5) The formula occurrences are different from the upper sequents occurrences
 *
 * Still missing for each rule:
 * 1) To check that all exceptions are thrown when needed
 */
class OccurrenceTest extends SpecificationWithJUnit {

  // implicits for using positions as occurrences
  "Positions" should {
    // import implicit coverters and definitions
    import positions._

    "be created correctly" in {
      val c1 = HOLVar("a", i->o)
      val v1 = HOLVar("x", i)
      val f1 = HOLAppFormula(c1,v1)

      val c2 = HOLVar("b", i->o)
      val v2 = HOLVar("y", i)
      val f2 = HOLAppFormula(c2,v2)   
      
      val fo1 = PositionsFOFactory.createPrincipalFormulaOccurrence(f1, Nil, Set[FormulaOccurrence]())
      fo1 must beEqual (Occ(1))
      PositionsFOFactory.createPrincipalFormulaOccurrence(f2, Nil, Set(fo1)) must beEqual(Occ(2))
    }
  }
}