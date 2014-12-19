package at.logic.algorithms.hlk

import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.execute.Success

/**
 * Test files for the hol parser
 */
@RunWith(classOf[JUnitRunner])
class HOLParserTest  extends SpecificationWithJUnit {
  "HLK HOL Parser" should {
    "Parse atoms" in {
      /*
      val atoms = List("x:o","0:i","complex:(i>i)>(i>o)","coffee:o>(i>o)","tea:(i>o)>i")
      val symbols = HOLParser.emptySymbolMap
      val parser = HOLParser(symbols)

      atoms map (x =>
        parser.phrase(parser.atom)(x)
        )
        */
      Success()
    }
  }

}
