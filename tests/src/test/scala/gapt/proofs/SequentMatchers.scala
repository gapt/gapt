package gapt.proofs

import gapt.formats.babel.BabelSignature
import org.specs2.matcher.{Matcher, Matchers}

trait SequentMatchers extends Matchers {

  def beMultiSetEqual[A](expected: Sequent[A])(implicit sig: BabelSignature): Matcher[Sequent[A]] = { (actual: Sequent[A]) =>
    (
      actual multiSetEquals expected,
      s"""
         | Sequent
         |   ${actual.toSigRelativeString}
         | is not multi-set equal to
         |   ${expected.toSigRelativeString}
         |
         | Additional elements in actual:
         |   ${actual diff expected toSigRelativeString}
         | Additional elements in expected:
         |   ${expected diff actual toSigRelativeString}
       """.stripMargin
    )
  }

  def beSetEqual[A](expected: Sequent[A])(implicit sig: BabelSignature): Matcher[Sequent[A]] =
    beMultiSetEqual(expected.distinct) ^^ { (actual: Sequent[A]) => actual.distinct }

}
