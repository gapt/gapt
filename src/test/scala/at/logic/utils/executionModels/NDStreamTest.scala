package at.logic.utils.executionModels

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import ndStream._
import searchAlgorithms._

@RunWith(classOf[JUnitRunner])
class NDStreamTest extends SpecificationWithJUnit {
  class MyConfiguration(val n: Int) extends Configuration[Int] {
    def result = if (n < 1) Some(n) else None
    def isTerminal = result != None
  }
  
  "BFSNDStream" should {
    "return None if empty" in {
      def myFun(conf: Configuration[Int]): List[Configuration[Int]] = (for {i <- 2 to conf.asInstanceOf[MyConfiguration].n} yield new MyConfiguration(i - 1)).toList
      val st = new NDStream(new MyConfiguration(6), myFun) with BFSAlgorithm
      st.next must beEqualTo (None)
    }
    "return one result" in {
      def myFun(conf: Configuration[Int]): List[Configuration[Int]] = List(new MyConfiguration(conf.asInstanceOf[MyConfiguration].n - 1) )
      val st = new NDStream(new MyConfiguration(6), myFun) with BFSAlgorithm
      st.next must beEqualTo (Some(0))
    }
    "return six results" in {
      def myFun(conf: Configuration[Int]): List[Configuration[Int]] = (for {i <- 1 to conf.asInstanceOf[MyConfiguration].n} yield new MyConfiguration(i - 1)).toList
      val st = new NDStream(new MyConfiguration(6), myFun) with BFSAlgorithm
      st.next must beEqualTo (Some(0))
      st.next must beEqualTo (Some(0))
      st.next must beEqualTo (Some(0))
      st.next must beEqualTo (Some(0))
      st.next must beEqualTo (Some(0))
      st.next must beEqualTo (Some(0))
    }
  }
}