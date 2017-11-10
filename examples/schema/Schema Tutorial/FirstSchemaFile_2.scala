import at.logic.gapt.expr._  
import at.logic.gapt.proofs.Context._ 
import at.logic.gapt.proofs.gaptic._ 
import at.logic.gapt.proofs.Context  
import at.logic.gapt.proofs.Sequent  

object FirstSchema extends TacticsProof {
ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
ctx += Context.Sort( "i" )
ctx += hoc"z:i"
ctx += hoc"g:i>i"
ctx += hoc"f:i>nat"
 ctx += hoc"max:i>i>i"

//By importing at.logic.gapt.proofs.Context we include some basic context definitions. 
// For example ctx += Context.Sort( "o" ) the sort of booleans. this allows one 
// to introduce new predicate symbols. 

ctx += hoc"E: nat>nat>o" //equality of two natural numbers
ctx += hoc"LEQ: i>i>o"   //ordering of two "i" terms 
ctx += hoc"LE: i>i>o"    //strict ordering of two "i" terms 

//At this point E,LEQ,LE are just functions of the boolean sort. We can introduce the needed
//theory by adding theory definitions to the context concerning these symbols:


ctx += "efef" -> hos"E(f(p),n),E(f(q),n) :- E(f(p),f(q))"
ctx += "leq_refl" -> hos" :- LEQ(p,p)"
ctx += "leq_g" -> hos"LEQ(g(p),q):- LE(p,q)"
ctx += "leq_max1" -> hos"LEQ(max(a, b), c) :- LEQ(a, c)"
ctx += "leq_max2" -> hos"LEQ(max(a, b), c) :- LEQ(b, c)"

//Notice that the prefix of the strings is now hos meaning higher-order sequent. Each of these 
//theory axioms is associated with a name and is stored in the context using this name. The 
//theory axioms use the same construction as proof links and will show up in the proof as a link to 
//the statement associated with the name. The name is an expression as we will see when 
//introducing proof names. 

//Even though proof symbols are to some extent at the boolean level, they are not 
// introduced as formulas but as expressions. 

ctx += hoc"omega: nat>nat"
ctx += hoc"phi: nat>nat"
ctx += hoc"chi: nat>i>nat"

//Proof names always end with a type "nat". The arguements before the final nat represents 
// the arguements associated with the proof name. That is omega takes one arguement while
// chi takes two. 

//The only thing missing for the construction of proof schema are primitive recursive definitions
//of functions and predicates. 

 ctx += PrimRecFun( hoc"POR:nat>i>o", "POR 0 x = E (f x) 0", "POR (s y) x = (E (f x) (s y) ∨ POR y x)" )

//Notice that this uses a different syntax than our previous context extensions, that is we write 
//functions and predicates as applications, i.e. E (f x) 0 instead of E(f(x),0). This is 
// important to note or you will get frustrated when it does not work. The first arguement is 
//the name and type of the predicate (or function). in this case "POR:nat>i>o" or Primitive 
//recursive OR. The second arguement is the basecase and the thirds is the step case. 


//In FirstSchemaFile_3.scala we go over the schema specific parts of the Context



}
