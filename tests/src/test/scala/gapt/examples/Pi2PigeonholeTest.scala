package gapt.examples
import org.specs2.mutable._

class PigeonholeTest extends Specification {
  "pi2" in { Pi2Pigeonhole.ctx.check( Pi2Pigeonhole.proof ); ok }
  "pi3" in { Pi3Pigeonhole.ctx.check( Pi3Pigeonhole.proof ); ok }
}
