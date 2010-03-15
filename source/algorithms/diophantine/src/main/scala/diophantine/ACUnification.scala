package diophantine

import _root_.at.logic.language.fol._

/**
 * Created by IntelliJ IDEA.
 * User: marty
 * Date: Mar 14, 2010
 * Time: 10:01:30 PM
 * To change this template use File | Settings | File Templates.
 */

object ACUnification {
  

  def unify(term1 : FOLTerm, term2 : FOLTerm) = {
    
  }

  def nestedFunctions_toList(function: String, term : FOLTerm) : List[FOLTerm] = {
    term match {
      case v : FOLVar => List(v)
      case c : FOLConst => List(c)
      case Function(name,arguments) =>
        if (name == function) {
          //arguments.
          Nil
        } else {
          Nil
        }
      case _ =>
        Nil
    }
    
  }
  
}