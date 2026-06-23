
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


object addExample extends TacticsProof {

  // Type

  ctx += InductiveType("nat", hoc"0 : nat", hoc"s : nat>nat", hoc"p : nat>nat")
  ctx += Sort("i")

    // Introduce predicate symbols 
  ctx += hoc"A1: nat>nat>nat>o" // predicate of arity 3
  ctx += hoc"A2: nat>nat>nat>o" // predicate of arity 3

    // Proof names
  ctx += hoc"d1:  nat>nat>nat>nat"
  ctx += hoc"phi: nat>nat>nat>nat"

    // End Sequents
  val esD1 = Sequent(Seq( 
                          hof"!y (A1(0,y,y))",
                          hof"!x!y!z (A1(s(x), y, s(z)) -> A1(x,y,z))",
                          hof"!x!y!z (A1(x,y,z) -> A1(s(x), y, s(z)))",
                          hof"!y (A2(0,y,y))",
                          hof"!x!y!z ( A2(s(x), y, z) -> A2(x,s(y),z) )",
                          hof"!x!y!z ( A2(x,s(y),z) -> A2(s(x), y , z) )",

                          hof"!y!z ( (y != z) -> -A1(0,y,z))",
                          hof"!y!z ( -A1(0,y,z) -> (y != z))",
                          hof"!x!y (-A1(s(x),y,0))",
                          hof"!y!z ( (y != z) -> -A2(0,y,z) )",
                          hof"!y!z ( -A2(0,y,z) -> (y != z) )",

                          hof"A1(x,s(y),z)"
                        ), 
                     Seq( hof"A1(s(x),y,z)"))

  val esPhi = Sequent(Seq(
                          hof"!y (A1(0,y,y))",
                          hof"!x!y!z (A1(s(x), y, s(z)) -> A1(x,y,z))",
                          hof"!x!y!z (A1(x,y,z) -> A1(s(x), y, s(z)))",
                          hof"!y (A2(0,y,y))",
                          hof"!x!y!z ( A2(s(x), y, z) -> A2(x,s(y),z) )",
                          hof"!x!y!z ( A2(x,s(y),z) -> A2(s(x), y , z) )",
                          hof"!y!z ( (y != z) -> -A1(0,y,z))",
                          hof"!y!z ( -A1(0,y,z) -> (y != z))",
                          hof"!x!y (-A1(s(x),y,0))",
                          hof"!y!z ( (y != z) -> -A2(0,y,z) )",
                          hof"!y!z ( -A2(0,y,z) -> (y != z) )",
                          hof"A2(x,y,z)"
                         ), 
                      Seq(hof"A1(x,y,z)"))


  // Proof Declarations
   ctx += ProofNameDeclaration(le"d1 x y z ", esD1)
   ctx += ProofNameDeclaration(le"phi x y z", esPhi)


  // End Sequents
    val esD1Bc = Sequent(
    Seq(
            "A1BC"  -> hof"!y (A1(0,y,y))", //2
            "A1SC1" -> hof"!x!y!z (A1(s(x), y, s(z)) -> A1(x,y,z))",
            "A1SC2" -> hof"!x!y!z (A1(x,y,z) -> A1(s(x), y, s(z)))", //1
            "A2BC"  -> hof"!y (A2(0,y,y))",
            "A2SC1" -> hof"!x!y!z ( A2(s(x), y, z) -> A2(x,s(y),z) )",
            "A2SC2" -> hof"!x!y!z ( A2(x,s(y),z) -> A2(s(x), y , z) )",
            "A1Neg1"-> hof"!y!z ( (y != z) -> -A1(0,y,z))",
            "A1Neg2"-> hof"!y!z ( -A1(0,y,z) -> (y != z))",
            "A1Neg3"-> hof"!x!y (-A1(s(x),y,0))",
            "A2Neg1"-> hof"!y!z ( (y != z) -> -A2(0,y,z) )",
            "A2Neg2"-> hof"!y!z ( -A2(0,y,z) -> (y != z) )",
            "Ant"   -> hof"A1(0,s(y),s(y))"
    ),
    Seq(
            "Suc"   -> hof"A1(s(0),y,s(y))")
  )

    val esD1Sc = Sequent(
    Seq(
            "A1BC"  -> hof"!y (A1(0,y,y))", //2
            "A1SC1" -> hof"!x!y!z (A1(s(x), y, s(z)) -> A1(x,y,z))",
            "A1SC2" -> hof"!x!y!z (A1(x,y,z) -> A1(s(x), y, s(z)))", //1
            "A2BC"  -> hof"!y (A2(0,y,y))",
            "A2SC1" -> hof"!x!y!z ( A2(s(x), y, z) -> A2(x,s(y),z) )",
            "A2SC2" -> hof"!x!y!z ( A2(x,s(y),z) -> A2(s(x), y , z) )",
            "A1Neg1"-> hof"!y!z ( (y != z) -> -A1(0,y,z))",
            "A1Neg2"-> hof"!y!z ( -A1(0,y,z) -> (y != z))",
            "A1Neg3"-> hof"!x!y (-A1(s(x),y,0))",
            "A2Neg1"-> hof"!y!z ( (y != z) -> -A2(0,y,z) )",
            "A2Neg2"-> hof"!y!z ( -A2(0,y,z) -> (y != z) )",
            "Ant"   -> hof"A1(s(x),s(y),s(z))"
    ),
    Seq(
            "Suc"   -> hof"A1(s(s(x)),y,s(z))")
  )

// Negation proof x>0 , z= 0
    val esD1Neg1 = Sequent(
    Seq(
            "A1BC"  -> hof"!y (A1(0,y,y))", //2
            "A1SC1" -> hof"!x!y!z (A1(s(x), y, s(z)) -> A1(x,y,z))",
            "A1SC2" -> hof"!x!y!z (A1(x,y,z) -> A1(s(x), y, s(z)))", //1
            "A2BC"  -> hof"!y (A2(0,y,y))",
            "A2SC1" -> hof"!x!y!z ( A2(s(x), y, z) -> A2(x,s(y),z) )",
            "A2SC2" -> hof"!x!y!z ( A2(x,s(y),z) -> A2(s(x), y , z) )",
            "A1Neg1"-> hof"!y!z ( (y != z) -> -A1(0,y,z))",
            "A1Neg2"-> hof"!y!z ( -A1(0,y,z) -> (y != z))",
            "A1Neg3"-> hof"!x!y (-A1(s(x),y,0))",
            "A2Neg1"-> hof"!y!z ( (y != z) -> -A2(0,y,z) )",
            "A2Neg2"-> hof"!y!z ( -A2(0,y,z) -> (y != z) )",
            "Ant"   -> hof"A1(s(x),s(y), 0)"
    ),
    Seq(
            "Suc"   -> hof"A1(s(s(x)), y, 0)")
  )

// Negation proof x=0 , z != s(y)
    val esD1Neg2 = Sequent(
    Seq(
            "A1BC"  -> hof"!y (A1(0,y,y))", //2
            "A1SC1" -> hof"!x!y!z (A1(s(x), y, s(z)) -> A1(x,y,z))",
            "A1SC2" -> hof"!x!y!z (A1(x,y,z) -> A1(s(x), y, s(z)))", //1
            "A2BC"  -> hof"!y (A2(0,y,y))",
            "A2SC1" -> hof"!x!y!z ( A2(s(x), y, z) -> A2(x,s(y),z) )",
            "A2SC2" -> hof"!x!y!z ( A2(x,s(y),z) -> A2(s(x), y , z) )",
            "A1Neg1"-> hof"!y!z ( (y != z) -> -A1(0,y,z))", // 1
            "A1Neg2"-> hof"!y!z ( -A1(0,y,z) -> (y != z))", //2
            "A1Neg3"-> hof"!x!y (-A1(s(x),y,0))",
            "A2Neg1"-> hof"!y!z ( (y != z) -> -A2(0,y,z) )",
            "A2Neg2"-> hof"!y!z ( -A2(0,y,z) -> (y != z) )",
            "Ant"   -> hof"A1(0,s(y), z)"
    ),
    Seq(
            "Suc"   -> hof"A1(s(0), y, z)")
  )

    val esPhiBc = Sequent(
    Seq(
            "A1BC"  -> hof"!y (A1(0,y,y))", //1
            "A1SC1" -> hof"!x!y!z (A1(s(x), y, s(z)) -> A1(x,y,z))",
            "A1SC2" -> hof"!x!y!z (A1(x,y,z) -> A1(s(x), y, s(z)))",
            "A2BC"  -> hof"!y (A2(0,y,y))",
            "A2SC1" -> hof"!x!y!z ( A2(s(x), y, z) -> A2(x,s(y),z) )",
            "A2SC2" -> hof"!x!y!z ( A2(x,s(y),z) -> A2(s(x), y , z) )",
            "A1Neg1"-> hof"!y!z ( (y != z) -> -A1(0,y,z))",
            "A1Neg2"-> hof"!y!z ( -A1(0,y,z) -> (y != z))",
            "A1Neg3"-> hof"!x!y (-A1(s(x),y,0))",
            "A2Neg1"-> hof"!y!z ( (y != z) -> -A2(0,y,z) )",
            "A2Neg2"-> hof"!y!z ( -A2(0,y,z) -> (y != z) )",
            "Ant"   -> hof"A2(0,z,z)"
    ),
    Seq(
            "Suc"   -> hof"A1(0,z,z)")
  )

    val esPhiSc = Sequent(
    Seq(
            "A1BC"  -> hof"!y (A1(0,y,y))",
            "A1SC1" -> hof"!x!y!z (A1(s(x), y, s(z)) -> A1(x,y,z))",
            "A1SC2" -> hof"!x!y!z (A1(x,y,z) -> A1(s(x), y, s(z)))",
            "A2BC"  -> hof"!y (A2(0,y,y))",
            "A2SC1" -> hof"!x!y!z ( A2(s(x), y, z) -> A2(x,s(y),z) )", // 1
            "A2SC2" -> hof"!x!y!z ( A2(x,s(y),z) -> A2(s(x), y , z) )",
            "A1Neg1"-> hof"!y!z ( (y != z) -> -A1(0,y,z))",
            "A1Neg2"-> hof"!y!z ( -A1(0,y,z) -> (y != z))",
            "A1Neg3"-> hof"!x!y (-A1(s(x),y,0))",
            "A2Neg1"-> hof"!y!z ( (y != z) -> -A2(0,y,z) )",
            "A2Neg2"-> hof"!y!z ( -A2(0,y,z) -> (y != z) )",
            "Ant"   -> hof"A2(s(x),y,z)"
    ),
    Seq(
            "Suc"   -> hof"A1(s(x),y,z)")
  )

// Negation proof x=0 , z != y
    val esPhiNeg = Sequent(
    Seq(
            "A1BC"  -> hof"!y (A1(0,y,y))", //2
            "A1SC1" -> hof"!x!y!z (A1(s(x), y, s(z)) -> A1(x,y,z))",
            "A1SC2" -> hof"!x!y!z (A1(x,y,z) -> A1(s(x), y, s(z)))", //1
            "A2BC"  -> hof"!y (A2(0,y,y))",
            "A2SC1" -> hof"!x!y!z ( A2(s(x), y, z) -> A2(x,s(y),z) )",
            "A2SC2" -> hof"!x!y!z ( A2(x,s(y),z) -> A2(s(x), y , z) )",
            "A1Neg1"-> hof"!y!z ( (y != z) -> -A1(0,y,z))", // 1
            "A1Neg2"-> hof"!y!z ( -A1(0,y,z) -> (y != z))", //2
            "A1Neg3"-> hof"!x!y (-A1(s(x),y,0))",
            "A2Neg1"-> hof"!y!z ( (y != z) -> -A2(0,y,z) )",
            "A2Neg2"-> hof"!y!z ( -A2(0,y,z) -> (y != z) )",
            "Ant"   -> hof"A2(0, y, z)"
    ),
    Seq(
            "Suc"   -> hof"A1(0, y, z)")
  )



      // Proof of D1 basecase
  val D1Bc = Lemma(esD1Bc) {
  
    forget("A1SC1")
    forget("A2BC")
    forget("A2SC1")
    forget("A2SC2")

    allL("A1SC2",     le"(0:nat)")
    allL("A1SC2_0",   le"(y:nat)")
    allL("A1SC2_0_0", le"(y:nat)")
    forget("A1SC2")
    forget("A1SC2_0")
    forget("A1SC2_0_0")

    impL("A1SC2_0_0_0")

    forget("Suc")
    allL("A1BC",     le"(y:nat)")
    forget("A1BC")


    trivial
    trivial

  }

      // Proof of D1 stepcase
  val D1Sc = Lemma(esD1Sc) {


    allL("A1SC1",     le"(x:nat)")
    allL("A1SC1_0",   le"(s(y):nat)") // s 
    allL("A1SC1_0_0", le"(z:nat)")
   
    forget("A1SC1_0")
    forget("A1SC1_0_0")

    impL("A1SC1_0_0_0")

    trivial

    forget("Ant")

    allL("A1SC2",     le"(s(x):nat)")
    allL("A1SC2_0",   le"(y:nat)") //s
    allL("A1SC2_0_0", le"(z:nat)")
    
    forget("A1SC2_0")
    forget("A1SC2_0_0")

    cut("cutAxR", hof"A1(s(x), y, z)") //s

    focus(1)
    impL
    trivial
    trivial

    forget("A1SC2_0_0_0")
    forget("Suc")

    ref("d1")

  } 

     // D1 negation proof x>0, z= 0
  val D1Neg1 = Lemma(esD1Neg1) {
    allL("A1Neg3",     le"(x:nat)")
    allL("A1Neg3_0",   le"(s(y):nat)")
    escargot
  }

       // D1 negation proof x=0, z != s(y)
  val D1Neg2 = Lemma(esD1Neg2) {

    allL("A1Neg1",     le"(y:nat)")
    allL("A1Neg1_0",   le"(z:nat)")
    forget("A1Neg1_0")
    impL
    
    focus(1)
    escargot

    allL("A1Neg2",     le"(y:nat)")
    allL("A1Neg2_0",   le"(z:nat)")
    forget("A1Neg2_0")
    impL

    escargot
    escargot

  }



     // Proof of Phi basecase
  val PhiBc = Lemma(esPhiBc) {


    allL("A1BC",     le"(z:nat)")

    trivial

  }

     // Proof of Phi stepcase
  val PhiSc = Lemma(esPhiSc) {


    allL("A2SC1",     le"(x:nat)")
    allL("A2SC1_0",   le"(y:nat)")
    allL("A2SC1_0_0", le"(z:nat)")

    impL("A2SC1_0_0_0")

    trivial

    forget("Ant")
    forget("A2SC1_0")
    forget("A2SC1_0_0")

    cut("cut", hof"A1(x, s(y), z)")

    forget("Suc")

    ref("phi")

    forget("A2SC1_0_0_0")
    ref("d1")

  }


       // Phi negation proof x=0, z != y
  val PhiNeg = Lemma(esPhiNeg) {

    allL("A1Neg1",     le"(y:nat)")
    allL("A1Neg1_0",   le"(z:nat)")
    forget("A1Neg1_0")
    impL
    
    focus(1)
    escargot
    escargot

  }



  ctx += ProofDefinitionDeclaration(le"d1 0 y (s y)", D1Bc) 
  ctx += ProofDefinitionDeclaration(le"d1 (s x) y (s z)", D1Sc) 
  ctx += ProofDefinitionDeclaration(le"d1 (s x) y 0", D1Neg1) 
  ctx += ProofDefinitionDeclaration(le"d1 0 y z", D1Neg2)

  ctx += ProofDefinitionDeclaration(le"phi 0 z z", PhiBc) 
  ctx += ProofDefinitionDeclaration(le"phi (s x) y z", PhiSc)
  ctx += ProofDefinitionDeclaration(le"phi 0 y z", PhiNeg) 

  val FullProof_2_3_2 = instantiateProof(le"phi (s ( s 0)) (s (s (s 0)))   (s (s 0))  ")
  val redCut_2_3_2    = cutNormal(FullProof_2_3_2)
  val thestruct_2_3_2 = StructCreators.extract(FullProof_2_3_2)
  val cs_2_3_2        = CharacteristicClauseSet(thestruct_2_3_2)

  val FullProof_2_3_0 = instantiateProof(le"phi (s ( s 0)) (s (s (s 0)))   0  ")
  val redCut_2_3_0    = cutNormal(FullProof_2_3_0)
  val thestruct_2_3_0 = StructCreators.extract(FullProof_2_3_0)
  val cs_2_3_0        = CharacteristicClauseSet(thestruct_2_3_0)

  val FullProof_2_0_0 = instantiateProof(le"phi (s ( s 0)) 0   0  ")
  val redCut_2_0_0    = cutNormal(FullProof_2_0_0)
  val thestruct_2_0_0 = StructCreators.extract(FullProof_2_0_0)
  val cs_2_0_0        = CharacteristicClauseSet(thestruct_2_0_0)

  val FullProof_1_3_2 = instantiateProof(le"phi ( s 0) (s (s (s 0)))   (s (s 0))  ")
  val redCut_1_3_2    = cutNormal(FullProof_1_3_2)
  val thestruct_1_3_2 = StructCreators.extract(FullProof_1_3_2)
  val cs_1_3_2        = CharacteristicClauseSet(thestruct_1_3_2)

  val FullProof_6_7_7 = instantiateProof(le"phi (s(s(s(s(s( s 0)))))) (s(s(s(s(s (s (s 0)))))))   (s(s(s(s(s(s (s 0)))))))  ")
  val redCut_6_7_7    = cutNormal(FullProof_6_7_7)
  val thestruct_6_7_7 = StructCreators.extract(FullProof_6_7_7)
  val cs_6_7_7        = CharacteristicClauseSet(thestruct_6_7_7)

  val FullProof_1_1_1 = instantiateProof(le"phi  ( s 0)  (s 0)  (s 0)  ")
  val redCut_1_1_1    = cutNormal(FullProof_1_1_1)
  val thestruct_1_1_1 = StructCreators.extract(FullProof_1_1_1)
  val cs_1_1_1        = CharacteristicClauseSet(thestruct_1_1_1)



}