package gapt.provers.congruence
import gapt.expr._
import org.specs2.mutable.Specification

class CongruenceClosureTest extends Specification {
  "simple" in {
    val cc = CC().internAndMerge(Seq(
      hof"b = a",
      hof"f c = f b"
    )).intern(Seq(le"f a"))

    cc.isEq(le"f a", le"f c") must_== true
    cc.isEq(le"a", le"c") must_== false
  }
}
