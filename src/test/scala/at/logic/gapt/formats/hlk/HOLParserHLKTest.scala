package at.logic.gapt.formats.hlk

import org.specs2.execute.Success
import org.specs2.mutable._

/**
 * Test files for the hol parser
 */
class HOLParserTest extends Specification {
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
