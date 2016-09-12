package at.logic.gapt.examples.church_numerals

import org.specs2.mutable.Specification

/**
 * Created by marty on 9/10/16.
 */
class ChurchNumeralsTest extends Specification {

  "0+0 = 0" in {
    plus( num( 0 ), num( 0 ) ) must_== num( 0 )
  }

  "0*0 = 0" in {
    times( num( 0 ), num( 0 ) ) must_== num( 0 )
  }

  "2+3 = 3+2" in {
    plus( num( 2 ), num( 3 ) ) must_== plus( num( 3 ), num( 2 ) )
  }

  "2*12 = 6*4" in {
    times( num( 2 ), num( 12 ) ) must_== times( num( 6 ), num( 4 ) )
  }

  "(50+50)*500 = 50000" in {
    int_of_num( times( plus( num( 50 ), num( 50 ) ), num( 500 ) ) ) must_== 50000
  }

  "if (0) then 3 else 5 = 3" in {
    int_of_num( cond( num( 3 ), num( 5 ), num( 0 ) ) ) must_== 3
  }

  "if (1) then 3 else 5 = 5" in {
    int_of_num( cond( num( 3 ), num( 5 ), num( 1 ) ) ) must_== 5
  }

}
