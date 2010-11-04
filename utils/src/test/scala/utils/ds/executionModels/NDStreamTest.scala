package at.logic.utils.executionModels

import org.specs._
import org.specs.runner._

import ndStream._

class NDStreamTest extends SpecificationWithJUnit {
  class MyConfiguration(val n: Int) extends Configuration {
    def result = if (n < 1) Some(n) else None
  }
  
  "BFSNDStream" should {
    "return None if empty" in {
      def myFun(conf: Configuration): List[Configuration] = (for {i <- 2 to conf.asInstanceOf[MyConfiguration].n} yield new MyConfiguration(i - 1)).toList
      val st = new BFSNDStream(new MyConfiguration(6), myFun)
      st.next must beEqual (None)
    }
    "return one result" in {
      def myFun(conf: Configuration): List[Configuration] = List(new MyConfiguration(conf.asInstanceOf[MyConfiguration].n - 1) )
      val st = new BFSNDStream(new MyConfiguration(6), myFun)
      st.next must beEqual (Some(0))
    }
    "return six results" in {
      def myFun(conf: Configuration): List[Configuration] = (for {i <- 1 to conf.asInstanceOf[MyConfiguration].n} yield new MyConfiguration(i - 1)).toList
      val st = new BFSNDStream(new MyConfiguration(6), myFun)
      st.next must beEqual (Some(0))
      st.next must beEqual (Some(0))
      st.next must beEqual (Some(0))
      st.next must beEqual (Some(0))
      st.next must beEqual (Some(0))
      st.next must beEqual (Some(0))
    }
  }
}