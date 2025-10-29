

import gapt.expr._
import gapt.proofs.gaptic._
import gapt.proofs.Sequent
import gapt.proofs.ceres.CharacteristicClauseSet
import gapt.proofs.ceres.StructCreators
import gapt.proofs.context.Context
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.{PrimitiveRecursiveFunction => PrimRecFun}
import gapt.proofs.context.update.ProofDefinitionDeclaration
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.lk.util.instantiateProof
import gapt.proofs.lk.transformations.cutNormal

import gapt.proofs.lk.util.isCutFree
import gapt.proofs.expansion.numberOfInstancesET

import gapt.expr.schema.Numeral


object hydraSchemaPred extends TacticsProof{
  
  // Type
  ctx += InductiveType("nat", hoc"0 : nat", hoc"s : nat>nat", hoc"p : nat>nat")
  ctx += Sort("i")



  // Introduce predicate symbols 
  ctx += hoc"P: nat>nat>o" // predicate of arity 1

    // Proof names

  ctx += hoc"hydraProof: nat>nat>nat"


  // Proof End Sequent
  val esHydraProof = Sequent(Seq(hof"!(n:nat) (P(0,0) & P(s(0),0) & P(n,s(0)) ) ", 
                         hof"!(n:nat) !(m:nat) ( P(p(n),p(p(m))) -> P(n, m ) )", 
                         hof"!(m:nat) (P(p(m),p(p(m))) -> P(0, m) )",
                         hof"!(n:nat) (P(p(n), p(p(n)))  -> P(n,0))"),
                     Seq(hof"P(u,v)"))


  // Proof Declarations
  ctx += ProofNameDeclaration(le"hydraProof u v", esHydraProof)




// End-sequents of the subproofs (formerly BC and SC, now 6 cases)

    val esHa1 = Sequent(Seq(("HaAx" -> hof"!(n:nat) (P(0,0) & P(s(0),0) & P(n,s(0)) ) "), 
                            ("HbAx" -> hof"!(n:nat) !(m:nat) ( P(p(n),p(p(m))) -> P(n, m )) "), 
                            ("HcAx" -> hof"!(m:nat) (P(p(m),p(p(m))) -> P(0, m) )"),
                            ("HdAx" -> hof"!(n:nat) (P(p(n), p(p(n)))  -> P(n,0))")),
                        Seq(("Suc_0" -> hof"P(0,0)")))

    val esHa2 = Sequent(Seq(("HaAx" -> hof"!(n:nat) (P(0,0) & P(s(0),0) & P(n,s(0)) ) "), 
                            ("HbAx" -> hof"!(n:nat) !(m:nat) ( P(p(n),p(p(m))) -> P(n, m )) "), 
                            ("HcAx" -> hof"!(m:nat) (P(p(m),p(p(m))) -> P(0, m) )"),
                            ("HdAx" -> hof"!(n:nat) (P(p(n), p(p(n)))  -> P(n,0))")),
                        Seq(("Suc_0" ->hof"P(s(0),0)")))

    val esHa3 = Sequent(Seq(("HaAx" -> hof"!(n:nat) (P(0,0) & P(s(0),0) & P(n,s(0)) ) "), 
                            ("HbAx" -> hof"!(n:nat) !(m:nat) ( P(p(n),p(p(m))) -> P(n, m )) "), 
                            ("HcAx" -> hof"!(m:nat) (P(p(m),p(p(m))) -> P(0, m) )"),
                            ("HdAx" -> hof"!(n:nat) (P(p(n), p(p(n)))  -> P(n,0))")),
                        Seq(("Suc_0" ->hof"P(u,s(0))")))

    val esD4 = Sequent(Seq(("HaAx" -> hof"!(n:nat) (P(0,0) & P(s(0),0) & P(n,s(0)) ) "), 
                            ("HbAx" -> hof"!(n:nat) !(m:nat) ( P(p(n),p(p(m))) -> P(n, m )) "), 
                            ("HcAx" -> hof"!(m:nat) (P(p(m),p(p(m))) -> P(0, m) )"),
                            ("HdAx" -> hof"!(n:nat) (P(p(n), p(p(n)))  -> P(n,0))")),
                        Seq(("Suc_0" ->hof"P(u,0)")))

    val esC3 = Sequent(Seq(("HaAx" -> hof"!(n:nat) (P(0,0) & P(s(0),0) & P(n,s(0)) ) "), 
                            ("HbAx" -> hof"!(n:nat) !(m:nat) ( P(p(n),p(p(m))) -> P(n, m )) "), 
                            ("HcAx" -> hof"!(m:nat) (P(p(m),p(p(m))) -> P(0, m) )"),
                            ("HdAx" -> hof"!(n:nat) (P(p(n), p(p(n)))  -> P(n,0))")),
                        Seq(("Suc_0" ->hof"P(0,v)")))

    val esB2 = Sequent(Seq(("HaAx" -> hof"!(n:nat) (P(0,0) & P(s(0),0) & P(n,s(0)) ) "), 
                            ("HbAx" -> hof"!(n:nat) !(m:nat) ( P(p(n),p(p(m))) -> P(n, m )) "), 
                            ("HcAx" -> hof"!(m:nat) (P(p(m),p(p(m))) -> P(0, m) )"),
                            ("HdAx" -> hof"!(n:nat) (P(p(n), p(p(n)))  -> P(n,0))")),
                        Seq(("Suc_0" ->hof"P(u,v)")))

                        

   // Proof of D1 basecase
    val Ha1 = Lemma(esHa1) {
        allL("HaAx" , le"(z:nat)") 
        andL("HaAx_0")
        andL("HaAx_0_0")
        trivial
    }
    
    val Ha2 = Lemma(esHa2) {
        allL("HaAx" , le"(z:nat)") 
        andL("HaAx_0")
        andL("HaAx_0_0")
        trivial
    }
    
    val Ha3 = Lemma(esHa3) {
        allL("HaAx" , le"(u:nat)") 
        andL("HaAx_0")
        andL("HaAx_0_0")
        trivial
    }
    
    val D4 = Lemma(esD4) {
        allL("HdAx" , le"(u:nat)") 
        cut("cutLink", hof"P(p(u),p(p(u)))")
        focus(1)

        impL("HdAx_0")

        forget("HaAx")
        forget("HbAx")
        forget("HcAx")
        forget("HdAx")
        forget("Suc_0")
        axiomLog

        forget("HaAx")
        forget("HbAx")
        forget("HcAx")
        forget("HdAx")
        forget("cutLink")
        axiomLog
        
        forget("Suc_0")
        ref("hydraProof")
    }

    val C3 = Lemma(esC3) {
        allL("HcAx" , le"(v:nat)") 
        cut("cutLink", hof"P(p(v),p(p(v)))")
        focus(1)

        impL("HcAx_0")

        forget("HaAx")
        forget("HbAx")
        forget("HcAx")
        forget("HdAx")
        forget("Suc_0")
        axiomLog

        forget("HaAx")
        forget("HbAx")
        forget("HcAx")
        forget("HdAx")
        forget("cutLink")
        axiomLog
        
        forget("Suc_0")
        ref("hydraProof")
    }

    val B2 = Lemma(esB2) {
        allL("HbAx" , le"(u:nat)") 
        allL("HbAx_0" , le"(v:nat)") 
        cut("cutLink", hof"P(p(u),p(p(v)))")
        focus(1)

        impL("HbAx_0_0")

        forget("HaAx")
        forget("HbAx")
        forget("HcAx")
        forget("HdAx")
        forget("Suc_0")
        axiomLog

        forget("HaAx")
        forget("HbAx")
        forget("HcAx")
        forget("HdAx")
        forget("cutLink")
        axiomLog
        
        forget("Suc_0")
        ref("hydraProof")
    }
  
/*

  ctx += ProofDefinitionDeclaration(le"hydraProof 0 0", Ha1) 
  ctx += ProofDefinitionDeclaration(le"hydraProof (s 0) 0", Ha2) 
  ctx += ProofDefinitionDeclaration(le"hydraProof u (s 0)", Ha3) 
  ctx += ProofDefinitionDeclaration(le"hydraProof (s (s u)) 0", D4) 
  ctx += ProofDefinitionDeclaration(le"hydraProof 0 (s (s v))", C3) 
  ctx += ProofDefinitionDeclaration(le"hydraProof (s u) (s (s v))", B2) 
  


*/

/*




  // Only Axiom Cases  
  val FullProof_00 = instantiateProof(le"hydraProof 0 0")
  val FullProof_10 = instantiateProof(le"hydraProof (s 0) 0")
  val FullProof_21 = instantiateProof(le"hydraProof (s (s 0)) (s 0)")

  // D4 -> Ha2
  val FullProof_20 = instantiateProof(le"hydraProof (s (s 0)) 0")

  // B2 -> C3 -> B2 -> Ha3
  val FullProof_17 = instantiateProof(le"hydraProof (s 0) (s(s(s(s(s(s(s 0)))))))")

  val FullProof_15 = instantiateProof(le"hydraProof (s 0) (s(s(s(s(s 0)))))")
  val FullProof_50 = instantiateProof(le"hydraProof (s(s(s(s(s 0))))) 0")

  val FullProof_2_12 = instantiateProof(le"hydraProof (s (s 0)) (s(s(s(s(s(s(s(s(s(s(s(s 0 ))))))))))))")

  val FullProof_20_8 = instantiateProof(le"hydraProof (s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s( 0)))))))))))))))))))))  (s(s(s(s(s(s(s(s 0))))))))")

  val thestruct = StructCreators.extract(FullProof_2_12)
  val cs = CharacteristicClauseSet(thestruct)


*/

}
