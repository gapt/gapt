

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


object hydraSchema extends TacticsProof{
  
  // Type
  ctx += InductiveType("nat", hoc"0 : nat", hoc"s : nat>nat")
  ctx += Sort("i")

  // Introduce predicate symbols 
  ctx += hoc"P: nat>nat>o" // predicate of arity 1

    // Proof names

  ctx += hoc"hydraProof: nat>nat>nat"


  // Proof End Sequent
  val esHydraProof = Sequent(Seq(hof"!(n:nat) (P(0,0) & P(s(0),0) & P(n,s(0)) ) ", 
                         hof"!(n:nat) !(m:nat) ( P(n,m) -> P(s(n), s(s(m))) ) ", 
                         hof"!(m:nat) (P(s(m),m) -> P(0, s(s(m))) )",
                         hof"!(n:nat) (P(s(n), n)  -> P(s(s(n)),0))"),
                     Seq(hof"P(p,q)"))


  // Proof Declarations
  ctx += ProofNameDeclaration(le"hydraProof p q", esHydraProof)




// End-sequents of the subproofs (formerly BC and SC, now 6 cases)

    val esHa1 = Sequent(Seq(("HaAx" -> hof"!(n:nat) (P(0,0) & P(s(0),0) & P(n,s(0)) ) "), 
                            ("HbAx" -> hof"!(n:nat) !(m:nat) ( P(n,m) -> P(s(n), s(s(m))) ) "), 
                            ("HcAx" -> hof"!(m:nat) (P(s(m),m) -> P(0, s(s(m))) )"),
                            ("HdAx" -> hof"!(n:nat) (P(s(n), n)  -> P(s(s(n)),0))")),
                        Seq(("Suc_0" -> hof"P(0,0)")))

    val esHa2 = Sequent(Seq(("HaAx" -> hof"!(n:nat) (P(0,0) & P(s(0),0) & P(n,s(0)) ) "), 
                            ("HbAx" -> hof"!n !m ( P(n,m) -> P(s(n), s(s(m))) ) "), 
                            ("HcAx" -> hof"!m (P(s(m),m) -> P(0, s(s(m))) )"),
                            ("HdAx" -> hof"!n (P(s(n), n)  -> P(s(s(n)),0))")),
                        Seq(("Suc_0" ->hof"P(s(0),0)")))

    val esHa3 = Sequent(Seq(("HaAx" -> hof"!(n:nat) (P(0,0) & P(s(0),0) & P(n,s(0)) ) "), 
                            ("HbAx" -> hof"!n !m ( P(n,m) -> P(s(n), s(s(m))) ) "), 
                            ("HcAx" -> hof"!m (P(s(m),m) -> P(0, s(s(m))) )"),
                            ("HdAx" -> hof"!n (P(s(n), n)  -> P(s(s(n)),0))")),
                        Seq(("Suc_0" ->hof"P(p,s(0))")))

    val esD4 = Sequent(Seq(("HaAx" -> hof"!(n:nat) (P(0,0) & P(s(0),0) & P(n,s(0)) ) "), 
                            ("HbAx" -> hof"!n !m ( P(n,m) -> P(s(n), s(s(m))) ) "), 
                            ("HcAx" -> hof"!m (P(s(m),m) -> P(0, s(s(m))) )"),
                            ("HdAx" -> hof"!n (P(s(n), n)  -> P(s(s(n)),0))")),
                        Seq(("Suc_0" ->hof"P(s(s(p)),0)")))

    val esC3 = Sequent(Seq(("HaAx" -> hof"!(n:nat) (P(0,0) & P(s(0),0) & P(n,s(0)) ) "), 
                            ("HbAx" -> hof"!n !m ( P(n,m) -> P(s(n), s(s(m))) ) "), 
                            ("HcAx" -> hof"!m (P(s(m),m) -> P(0, s(s(m))) )"),
                            ("HdAx" -> hof"!n (P(s(n), n)  -> P(s(s(n)),0))")),
                        Seq(("Suc_0" ->hof"P(0,s(s(q)))")))

    val esB2 = Sequent(Seq(("HaAx" -> hof"!(n:nat) (P(0,0) & P(s(0),0) & P(n,s(0)) ) "), 
                            ("HbAx" -> hof"!n !m ( P(n,m) -> P(s(n), s(s(m))) ) "), 
                            ("HcAx" -> hof"!m (P(s(m),m) -> P(0, s(s(m))) )"),
                            ("HdAx" -> hof"!n (P(s(n), n)  -> P(s(s(n)),0))")),
                        Seq(("Suc_0" ->hof"P(s(p),s(s(q)))")))

                        

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
        allL("HaAx" , le"(p:nat)") 
        andL("HaAx_0")
        andL("HaAx_0_0")
        trivial
    }
    val D4 = Lemma(esD4) {
        allL("HdAx" , le"(p:nat)") 
        cut("cutLink", hof"P(s(p),p)")
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
        allL("HcAx" , le"(q:nat)") 
        cut("cutLink", hof"P(s(q),q)")
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
        allL("HbAx" , le"(p:nat)") 
        allL("HbAx_0" , le"(q:nat)") 
        cut("cutLink", hof"P(p,q)")
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
  


  ctx += ProofDefinitionDeclaration(le"hydraProof 0 0", Ha1) 
  ctx += ProofDefinitionDeclaration(le"hydraProof (s 0) 0", Ha2) 
  ctx += ProofDefinitionDeclaration(le"hydraProof p (s 0)", Ha3) 
  ctx += ProofDefinitionDeclaration(le"hydraProof (s (s p)) 0", D4) 
  ctx += ProofDefinitionDeclaration(le"hydraProof 0 (s (s q))", C3) 
  ctx += ProofDefinitionDeclaration(le"hydraProof (s p) (s (s q))", B2) 
  







  // Only Axiom Cases  
  val FullProof_00 = instantiateProof(le"hydraProof 0 0")
  val FullProof_10 = instantiateProof(le"hydraProof (s 0) 0")
  val FullProof_21 = instantiateProof(le"hydraProof (s (s 0)) (s 0)")

  // D4 -> Ha2
  val FullProof_20 = instantiateProof(le"hydraProof (s (s 0)) 0")

  // B2 -> C3 -> B2 -> Ha3
  val FullProof_17 = instantiateProof(le"hydraProof (s 0) (s(s(s(s(s(s(s 0)))))))")

  val FullProof_15 = instantiateProof(le"hydraProof (s 0) (s(s(s(s(s 0)))))")

  val FullProof_2_12 = instantiateProof(le"hydraProof (s (s 0)) (s(s(s(s(s(s(s(s(s(s(s(s 0 ))))))))))))")

  val FullProof_20_8 = instantiateProof(le"hydraProof (s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s( 0)))))))))))))))))))))  (s(s(s(s(s(s(s(s 0))))))))")

  val thestruct = StructCreators.extract(FullProof_20_8)
  val cs = CharacteristicClauseSet(thestruct)




}
