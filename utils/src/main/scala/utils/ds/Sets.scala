/*
 * Sets.scala
 *
 * None mathematical definition of sets. I.e. sets code does not follow the scala convention of defining mathematical objects in mathematical terms (set as a function (A => Noolean)),
 * as we want the set to be covariant. We will only follow the interface that two sets are equal if they have the same elements.
 */

package at.logic.utils.ds

import scala.collection.mutable.HashSet
import scala.util.Sorting

object Sets {
    trait Set[+A] extends Collection[A]{
        //def apply[U>:A](s:Set[A])
    }

    /* a hashset based implementation of a covariant set */
    class CovariantSet[+A] private (
        private[this] var set : HashSet[A]  )
    extends Set[A] 
    {
        def this() = this(new HashSet[A])
        
        def size() : Int = return set.size
        def elements : Iterator[A]= { return set.elements }


        /* gives restricted access to the hash set*/
        protected def getHashSet[B>:A]() : HashSet[B] = {
            var bset = new HashSet[B]
            bset ++= set
            return bset
        }

        /* there is no difference in adding in the beginning or the end in a hashset */
        def +[B>:A](x:B) : CovariantSet[B] = this.::(x)

        /* override of list constructor */
        def ::[B>:A](x:B) : CovariantSet[B] = {
            var setb : HashSet[B] = new HashSet[B]
            setb ++= set

            var s : CovariantSet[B] = new CovariantSet[B](setb)
            val r = s.find( (v:B) => v == x )
            if (r == None) {
                setb += x
            }

            return s
        }

        /* two CovariantSets are equal, if their private HashSets are equal.
         * two HasSets are equal, if their Elements are reference equal.
         *
         * see also http://programming-scala.labs.oreilly.com/ch06.html
         * chapter "Array Equality and the sameElements Method"
         */
        override def equals(x:Any) : Boolean = {
            try {
                var i = x.asInstanceOf[CovariantSet[A]]
                var bset = new HashSet[A]()
                bset ++= set

                if (i.getHashSet().equals(bset) ) return true
            } catch {
                case _ =>
            }

            return false
        }

    /** two sets A and B are the same, if they have the same size,
     * and if every element from A is in B and vice versa          
     *
     */
    override def sameElements[B>:A](that : Iterable[B]) : Boolean = {
        // TODO: check, if the HashMap.sameElements method always iterates the same over if objects in it are equal, but not reference equal - then this method is not necessary
        var that_size = 0
        for (b <- that) {
            that_size += 1
            if (this.elements.find((x : B) => x == b) == None) {
                //Console.println("could not find "+b)
                return false
            } else {
                //Console.println("found "+b)
            }
        }

        for (a <- this.elements) {
            if (that.find((x:B) => x == a ) == None) {
                //Console.println("could not find "+a)
                return false
            } else {
                //Console.println("found "+a)
            }

        }

        return this.size == that_size
    }

    /*class HashSet[+A] extends Set[A] {

    }*/
    }
 }
