package at.logic.gapt.proofs

import org.specs2.matcher.{ Matchers, Matcher }

trait SequentMatchers extends Matchers {

  def beMultiSetEqual[A]( expected: Sequent[A] ): Matcher[Sequent[A]] = { actual: Sequent[A] =>
    ( actual multiSetEquals expected,
      s"""
         | Sequent
         |   $actual
         | is not multi-set equal to
         |   $expected
         |
         | Additional elements in actual:
         |   ${actual diff expected}
         | Additional elements in expected:
         |   ${expected diff actual}
       """.stripMargin )
  }

  def beSetEqual[A]( expected: Sequent[A] ): Matcher[Sequent[A]] =
    beMultiSetEqual( expected.distinct ) ^^ { ( actual: Sequent[A] ) => actual.distinct }

}
