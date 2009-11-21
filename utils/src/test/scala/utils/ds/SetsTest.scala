/*
 * SetsTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils.ds

import org.specs._
import org.specs.runner._

import org.scalacheck._
import org.scalacheck.Prop._


import Sets._

import Sets.SetImplicitDefs._

class SetsTest extends SpecificationWithJUnit {

    "Sets" should {

        class Fruit(var name : String) {
            override def equals(x:Any) : Boolean = {
                try {
                    var f : Fruit = x.asInstanceOf[Fruit]
                    return f.name == this.name
                } catch {
                    case _ =>
                }
                return false
            }
        }

        class Apple(name : String, var colors : Int) extends Fruit(name) {
            override def equals(x:Any) : Boolean = {
                try {
                    if (! super.equals(x)) return false
                    var a = x.asInstanceOf[Apple]
                    return (a.colors == colors)

                } catch { case _ => }
                return false
            }
        }
        class Orange(name : String, var bloodorange : Boolean) extends Fruit(name) {

        }

        var apple = new Apple("apfel",2)
        var apple2 = new Apple("apfel",2)
        var orange = new Orange("orange",true)


    "be invariant to multiple additions of an element" in {
        var set: Set[String] = Set[String]
        var set2: Set[String] = Set[String]

        set = set + "abc"
        set = set + "abc"
        set = set + "abc"
        set = set + "xyz"
        set = set + "xyz"
        set = set + "xyz"

        set2 = set2 + "xyz"
        set2 = set2 + "abc"

        set.sameElements(set2) must beEqual (true)
    }

    "be scalacheck invariant to multiple additions of an element" in {
        var mul_additions = forAll( (str1:String, str2:String) => {
            var set1: Set[String] = Set[String];
            var set2: Set[String] = Set[String];
            
            (set1 + new String(str1) + new String(str2)) sameElements
            (set2 + new String(str2) + new String(str1)
             + new String(str1) + new String(str2)
             + new String(str1) + new String(str2)
             + new String(str1) + new String(str2))
        })
        
        Test.check(Test.defaultParams , mul_additions).passed must beEqual (true)
    }

    "be covariant" in {
        var set1 = (new Sets.CovariantSet) + apple + orange
        var set2 = (new Sets.CovariantSet) + orange + apple2

        set1.sameElements(set2) must beEqual (true)
    }

    " be idempotent " in {
        val idempotency = forAll { (l : List[Int]) => var s = listToSet(l);
                                  s.sameElements(s++s) }
        Test.check(Test.defaultParams , idempotency).passed must beEqual (true)
    }
    }


    "Implicit conversions on sets" should {
        "convert correctly between a list and a set" in {
            val ls = "a"::"a"::"b"::"c"::"a"::Nil
            val st1 = "a"::"b"::"c"::Set[String]
            val st2 = Set[String] + "b" + "c" + "a"
            (listToSet(ls)) must beEqual (st1)
            (listToSet(ls)) must beEqual (st2)
        }
    }

}
