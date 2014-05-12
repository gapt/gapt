package at.logic.language.hol

import at.logic.language.lambda.types._

/**
 * Ordering for HOL Formulas (also for FOL)
 */
object HOLOrdering extends HOLOrdering
class HOLOrdering extends Ordering[HOLExpression] {
  override def compare(x:HOLExpression, y:HOLExpression) : Int =  (x,y) match {
    case (x,y) if x syntaxEquals y => 0
    case (HOLVar(s1,t1), HOLVar(s2,t2) ) =>
      s1.toString() compare s2.toString() match {
        case 0 => TAOrdering.compare(t1,t2)
        case x => x
      }

    case (HOLConst(s1,t1), HOLConst(s2,t2) ) =>
      s1.toString() compare s2.toString() match {
        case 0 => TAOrdering.compare(t1,t2)
        case x => x
      }

    case (HOLApp(s1,t1), HOLApp(s2,t2)) =>
      compare(s1,s2) match {
        case 0 => compare(t1,t2)
        case x => x
      }

    case (HOLAbs(x1,t1), HOLAbs(x2,t2)) =>
      compare(x1,x2) match {
        case 0 => compare(t1,t2)
        case x => x
      }

    case (HOLVar(_,_), _            )   => -1

    case (HOLConst(_,_), HOLVar(_,_)) => 1
    case (HOLConst(_,_), _          ) => -1

    case (HOLApp(_,_), HOLVar(_,_)) => 1
    case (HOLApp(_,_), HOLConst(_,_)) => 1
    case (HOLApp(_,_), _          ) => -1

    case (HOLAbs(_,_), HOLVar(_,_))   => 1
    case (HOLAbs(_,_), HOLConst(_,_)) => 1
    case (HOLAbs(_,_), HOLApp(_,_))   => 1
    case (HOLAbs(_,_), _          )   => -1

    case _ => throw new Exception("Unhandled comparision of hol epxressions: "+x+" ? "+y)
  }
}

/**
 * Ordering on types.
 */
object TAOrdering extends TAOrdering
class TAOrdering extends Ordering[TA] {
  override def compare(x :TA,y:TA) : Int = (x,y) match {
    case (x,y) if x == y => 0
    case (t1->t2, t3 -> t4) =>
      val r = compare(t1,t3)
      if (r == 0) compare(t2,t4) else r
    case (_, _ -> _) => -1
    case (_ -> _, _) => 1

    //o < i < index
    case (To,Ti) => -1
    case (To,Tindex) => -1

    case (Ti,To) => 1
    case (Ti,Tindex) => -1

    case (Tindex, Ti) => 1
    case (Tindex, To) => 1
    case _ => throw new Exception("Unhandled case in type comparison: "+x+" ? "+y)
  }
}
