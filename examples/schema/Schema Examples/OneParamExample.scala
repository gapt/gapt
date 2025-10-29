
import gapt.expr._
import gapt.proofs.ceres._
import gapt.proofs.gaptic._
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.{PrimitiveRecursiveFunction => PrimRecFun}
import gapt.proofs.context.update.ProofDefinitionDeclaration
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.lk.util.instantiateProof
//used to unfold proof schema


object OneParamExample extends TacticsProof {
  // This is where the actual proof is constructed and stored.
  // calling this object will result in the construction of the
  // proof or proof schema.


  /* More about the context ctx */
  // Everything is stored within the context, the proof components, proof names, end sequents
  // of proofs, recursive predicates, logical sorts, and theory axioms.

  // These are the two fundamental additions to the context needed for Schematic
  // proof construction.
  ctx += InductiveType("nat", hoc"0 : nat", hoc"s : nat>nat") // defines the natural numbers
  ctx += Sort("i") // defines the first order term sort
  ctx += hoc"h:i>i" 
  ctx += hoc"g:nat>i>i"

  // Note that at this point both sorts are empty (though in the case of the type "nat"
  // we do have the individuals 0, s(0), s(s(0)), and so on, but no predicates or
  // additional function symbols). We need to add constants, functions,
  // and predicate symbols individually to the sorts. The above declarations
  // only provide the particular types this objects can have but not the
  // individuals of these types.

  // By importing gapt.proofs.context.Context we include some basic context definitions.
  // For example ctx += Context.Sort( "o" ) the sort of booleans. this allows one
  // to introduce new predicate symbols.

  // Introduce predicate symbols 
  ctx += hoc"P: i>o" // predicate of arity 1

  // Proof symbols
  ctx += hoc"delta: nat>nat"
  ctx += hoc"omega: nat>i>nat"

  // Primitive recursive definitions of functions and predicates.
  ctx += PrimRecFun(hoc"f:nat>i>i", "f 0 x = x", "f (s y) x = h (f y x)")


  // The names are there to match proofs to the appropriate end sequents. This is done
  // using the ProofNameDeclaration Facet of the context. But first we need to construct
  // the end sequents which are associated with each proof name

  // End Sequents
  val esDelta = Sequent(Seq(hof"!x (P(x) -> P(h(x)))"), Seq( hof" !x (P(x) -> P(f(n,x)))"))
  val esOmega = Sequent(Seq(hof"!x (P(x) -> P(h(x)))"), Seq( hof"(P(f(n,c)) -> P(g(n,c)))->(P(c)->P(g(n,c)))"))


  // Now that we have the end sequents we need to add the association to the context. The important thing is
  // that all the free variables in the sequents are present in the association. For example eschi has two
  // free variable thus, its association expression must have two free variables.

  // Proof Declaration
  ctx += ProofNameDeclaration(le"delta n", esDelta)
  ctx += ProofNameDeclaration(le"omega n c", esOmega)


  // To work with the base case we need to take the sequent from the proof name declaration and instantiate
  // it in the proper way, i.e. n-> 0 and a-> a
  val esDeltaBc = Sequent(Seq("Ant_0" -> hof"!x (P(x) -> P(h(x)))"), Seq("Suc_0" -> hof" !x (P(x) -> P(f(0,x)))"))
  // notice that we associated a name with each formula this type. The propose  of this naming is to
  // refer to them in the tactic proof. we construct a tactic proof with the follow command. Try to run the following
  // in  gapt by typing FirstSchema.chiBc after loading the file and see what happens:
  val deltaBc = Lemma(esDeltaBc) {
    forget("Ant_0") // weakening left
    allR("Suc_0", fov"a")
    impR
    unfold("f") atMost 1 in "Suc_0_1" // unfold LHS instead of RHS as in example
    trivial
  }

  // We can open this proof in prooftool by typing prooftool(OneParamExample.deltaBc). The last step is to add this
  // proof to the context to the ProofDefinition facet using the following command.
  ctx += ProofDefinitionDeclaration(le"delta 0", deltaBc)

    // This is similar to a proof declaration except the variables are instantiated correctly to associate with
  // the specific case addressed.

  // Now we need to build the step case of chi in a similar fashion.

  val esDeltaSc = Sequent(Seq("Ant_0" -> hof"!x (P(x) -> P(h(x)))"), Seq("Suc_0" -> hof" !x (P(x) -> P(f( s(n) ,x)))"))

  // Notice two differences between esChiSc and esChiBc, not only are both n and a present but we have also
  // add a sucessor symbol around n. This tells the system that this is a stepcase sequent. This must
  // always be added, even in the case of multiple parameters.

  val deltaSc = Lemma(esDeltaSc) {
     cut("cut", hof"!x(P(x) -> P(f(n,x)))") 
        //
     // LHS
     //forget("Suc_0")
     //ref("delta") // The proof link tactic 

     forget("Suc_0")
     ref("delta")
     //
     // RHS
     //focus(1)
     allR("Suc_0", fov"a")
     allL("cut", fov"a") 
     forget("cut") // necessary as weak quantifier formulas are kept in the sequent after instantiations
     impR
     impL("cut_0") 
     // RHS - RHS
     forget("Ant_0")
     forget("Suc_0_1")
     trivial
//
  // 
     // RHS - LHS
     forget("Suc_0_0")
     allL("Ant_0", le"f(n,a)")
     forget("Ant_0") // necessary as weak quantifier formulas are kept in the sequent after instantiations
     impL("Ant_0_0")
//
     // RHS - RHS - LHS
     forget("Suc_0_1")
     trivial
//
     // RHS - RHS - RHS
     forget("cut_0")
     unfold("f") atMost 1 in "Suc_0_1" // unfold LHS instead of RHS as in example
     trivial
//
    
}
  ctx += ProofDefinitionDeclaration(le"delta (s n)", deltaSc)


  // We can instantiate the proof schema of delta as follows:
  val deltaThree = instantiateProof(le"delta (s (s (s 0)))")
  // prooftool(FirstSchema.phiThree)



  // OMEGA

  val esOmegaPr = Sequent(Seq("Ant_2" -> hof"!x(P(x)->P(h(x)))"), 
                          Seq("Suc_2" -> hof"(P(f(n,c))->P(g(n,c)))->(P(c)->P(g(n,c)))"))

  val omegaPr = Lemma(esOmegaPr) {
     //trivial 
    cut("cut1", hof"!x(P(x) -> P(f(n,x)))") 

    forget("Suc_2")
    ref("delta")

    forget("Ant_2")
    allL( "cut1" ,fov"c")
    forget("cut1")
    impR
    impR
    impL("cut1_0")

    forget("Suc_2_0")
    forget("Suc_2_1_1")
    trivial

    forget("Suc_2_1_0")
    impL("Suc_2_0")

    forget("Suc_2_1_1")
    trivial

    forget("cut1_0")
    trivial
  }

  ctx += ProofDefinitionDeclaration(le"omega n c", omegaPr)
  
  val omegaNull = instantiateProof(le"omega 0 c")
  val omegaOne = instantiateProof(le"omega (s 0) c")


  val thestruct = StructCreators.extract(omegaOne)
  val cs = CharacteristicClauseSet(thestruct)

}
