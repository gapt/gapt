/*
 * SetsTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils.ds

import org.specs._
import org.specs.runner._

import Sets._


class SetsTest extends Specification with JUnit {

    "Sets" should {
        var set: Set[String] = Set[String]
        set = set + "abc"
        set = set + "abc"
        set = set + "abc"
        set = set + "xyz"
        set = set + "xyz"
        set = set + "xyz"

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
        var set2: Set[String] = Set[String]
        set2 = set2 + "xyz"
        set2 = set2 + "abc"
        //set == set2

        //Console.println(set == set2)
        set.sameElements(set2) must beEqual (true)
    }

    "be covariant" in {
        var set1 = (new Sets.CovariantSet) + apple + orange
        var set2 = (new Sets.CovariantSet) + orange + apple2

        //var set3 = set1 + orange
        //var set4 = set2 + apple
        /*
        Console.print("Fruit:"+(apple.asInstanceOf[Fruit]).name)
        Console.print(" Apple:"+(apple.asInstanceOf[Apple]).name)
        Console.print(" "+ ((apple.asInstanceOf[Fruit]).name eq (apple.asInstanceOf[Fruit]).name))
        Console.println(" Apple:"+(apple.asInstanceOf[Apple]).colors)
        Console.println("check for apple equality" + (apple == apple2))
        Console.println(set1)
        Console.println(set2)
        Console.println(set1.sameElements(set2))
        */
        //val f = x

        set1.sameElements(set2) must beEqual (true)
    }
    }

    import Sets.SetImplicitDefs._

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
