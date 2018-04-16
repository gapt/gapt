package gapt.provers.congruence
import gapt.expr._
import org.specs2.mutable.Specification

class CongruenceClosureTest extends Specification {
  "simple" in {
    val cc = CongruenceClosure().merges(
      hof"b = a",
      hof"f c = f b" )

    cc.isEquivalent( le"f a", le"f c" ) must_== true
    cc.isEquivalent( le"a", le"c" ) must_== false
  }

  "ac" in {
    val cc1 = CongruenceClosure().merges(
      hof"a * b = c",
      hof"c * c = 1" ).internalize( hof"b*c*a = 1" )
    val cc2 = cc1.saturate( acTheory( FOLFunctionConst( "*", 2 ) ).step )
    cc2.isEquivalent( le"b*c*a", le"1" ) must_== true
  }

  "assoc" in {
    val cc1 = CongruenceClosure().merges(
      hof"a * b = c",
      hof"c * c = 1" ).internalize( hof"(c*a)*b = 1" )
    val cc2 = cc1.saturate( acTheory( FOLFunctionConst( "*", 2 ) ).step )
    cc2.isEquivalent( le"(c*a)*b", le"1" ) must_== true
  }
}
