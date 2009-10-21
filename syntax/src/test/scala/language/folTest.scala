package at.logic.language.fol


import org.specs._
import org.specs.runner._


class folTest  extends Specification with JUnit {
  "fol" should {
    import at.logic.syntax.language.fol._
    
    "be able to create and compare constants: c = c" in 
      	{  (Constant("c")) must beEqual (Constant("c")) }

    "be able to create and compare constants: c /= d" in 
      	{  (Constant("c")) mustNot beEqual (Constant("d")) }
    
    "be able to create and compare variables: x = x" in 
      	{  (Variable("x")) must beEqual (Variable("x")) }

    "be able to create and compare variables: x /= y" in 
      	{  (Variable("x")) mustNot beEqual (Variable("y")) }

    "differentiate between constants and variables: var(x) /= const(x)" in 
      	{  //try { 
      			(Variable("x")) mustNot beEqual (Constant("x"))  
      	   /* } catch {
      		  case e => println("Exception!");  
                        println(e);      		
      	   } */
          
        }
   
    
  }

}
