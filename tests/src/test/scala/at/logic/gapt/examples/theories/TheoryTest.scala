package at.logic.gapt.examples.theories

import org.specs2.mutable.Specification
import org.specs2.specification.core.Fragment

abstract class TheoryTest( t: Theory, skipping: Set[String] = Set() ) extends Specification {
  "definitions" in { t.ctx; ok }
  Fragment.foreach( t.proofsHere ) {
    case ( n, p ) => n in {
      if ( skipping( n ) ) skipped
      p.value; ok
    }
  }
}

class LogicTest extends TheoryTest( logic )
class PropsTest extends TheoryTest( props )
class NatTest extends TheoryTest( nat )
class NatDivisibleTest extends TheoryTest( natdivisible )
class NatDivisionTest extends TheoryTest( natdivision )
class NatOrderTest extends TheoryTest( natorder )
class ListTest extends TheoryTest( list )
class ListLengthTest extends TheoryTest( listlength )
class ListFoldTest extends TheoryTest( listfold )
class ListDropTest extends TheoryTest( listdrop )
class NatListsTest extends TheoryTest( natlists )
class FtaTest extends TheoryTest( fta )
