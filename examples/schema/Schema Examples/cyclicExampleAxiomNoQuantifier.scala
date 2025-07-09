


import gapt.expr._
import gapt.expr.formula.{Formula, Top}
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






object cyclicExampleAxiomNoQuantifier extends TacticsProof {

  // Type
  ctx += InductiveType("nat", hoc"0 : nat", hoc"s : nat>nat")
  ctx += Sort("i")

  val phiAxioms = Sequent(Seq("Refl" -> hof"!(p:nat)  (p = p) ",
    "A2Ax" -> hof"!p !q ((s(p)= s(q) ) -> (p = q)) ",
    "DistinctConstructors" -> hof"!(x:nat) 0 != s(x)"),
    Nil)

  val phiAxiomsUnlabeled = phiAxioms.map(_._2)

  // Primitive Recursive Definitions
  ctx += PrimRecFun(hoc"Add1:nat>nat>nat>o",
    "Add1 0 y z          = ( z = y )", // Base Case
    "Add1 (s(x:nat)) y z = (?(u:nat) ?(v:nat) (s(x) = s(u) ∧ z = s(v) ∧ Add1(u,y,v) ) )") // Step Case

  ctx += PrimRecFun(hoc"Add2:nat>nat>nat>o",
    "Add2 0 y z          = ( z = y )", // Base Case
    "Add2 (s(x:nat)) y z = (?(u:nat)  (s(x) = s(u) ∧ Add2(u,s(y),z) ) )") // Step Case

  // Proof names
  ctx += hoc"d1: nat>nat>nat>nat"
  ctx += hoc"phi: nat>nat>nat>nat"


  // Proof End Sequent
  val esD1 = phiAxiomsUnlabeled ++ Sequent(Seq(hof"Add1(n,s(y),(z:nat)) "),
    Seq(hof"Add1(s(n),y,(z:nat))"))

  val esPhi = phiAxiomsUnlabeled ++ Sequent(Seq(hof"Add2(n,y,z)"),
    Seq(hof"Add1(n,y,z)"))

  // Proof Declarations
  ctx += ProofNameDeclaration(le"d1 n y z", esD1)
  ctx += ProofNameDeclaration(le"phi n y z", esPhi)

  // basecase and stepcase  end sequents

  val esD1Bc = phiAxioms ++ Sequent(Seq("Ant_0" -> hof"Add1(0,s(y),z)"),
    Seq("Suc_0" -> hof"Add1(s(0),y,z)"))
  val esD1Sc = phiAxioms ++ Sequent(Seq("Ant_0" -> hof"Add1(s(n),s(y),s(z))"),
    Seq("Suc_0" -> hof"Add1(s(s(n)),y,s(z))"))
  val esD1ScClash = phiAxioms ++ Sequent(Seq("Ant_0" -> hof"Add1(s(n),s(y),0)"),
    Seq("Suc_0" -> hof"Add1(s(s(n)),y,0)"))


  val esPhiBc = phiAxioms ++ Sequent(Seq("Ant_0" -> hof"Add2(0,y,z)"),
    Seq("Suc_0" -> hof"Add1(0,y,z)"))
  val esPhiSc = phiAxioms ++ Sequent(Seq("Ant_0" -> hof"Add2(s(n),y,z)"),
    Seq("Suc_0" -> hof"Add1(s(n),y,z)"))


  // Proof of D1 basecase
  val D1Bc = Lemma(esD1Bc) {
    forget("A2Ax")


    unfold("Add1") atMost 1 in "Ant_0"
    unfold("Add1") atMost 1 in "Suc_0"
    exR("Suc_0", hoc"0")
    exR("Suc_0_0", hov"y:nat")
    forget("Suc_0_")
    forget("Suc_0_0")
    andR
    andR

    allL("Refl", le"s(0):nat")
    axiomLog
    axiomLog

    unfold("Add1") atMost 1 in "Suc_0_0_0"
    allL("Refl", le"y:nat")
    axiomLog


  }


  val D1Sc = Lemma(esD1Sc) {


    unfold("Add1") atMost 1 in "Ant_0"
    exL("Ant_0")
    exL("Ant_0")
    andL
    andL

    unfold("Add1") atMost 1 in "Suc_0"


    exR("Suc_0", le"(s(n):nat)")
    exR("Suc_0_0", le"(z:nat)") // <--- z
    forget("Suc_0")
    forget("Suc_0_0")


    andR
    andR

    allL("Refl", le"s(s(n))")
    axiomLog

    // axiomLog // <-- this is new



    allL("Refl", le"s(z)")
    axiomLog

    allL("A2Ax", le"(n:nat)")
    allL("A2Ax_0", le"(u:nat)")

    forget("A2Ax_0")

    allL("A2Ax", le"(z:nat)")
    allL("A2Ax_1", le"(v:nat)")

    forget("A2Ax_1")

    impL("A2Ax_1_0")
    axiomLog

    impL("A2Ax_0_0")
    axiomLog

    eql("A2Ax_1_0", "Ant_0_1")
    eql("A2Ax_0_0", "Ant_0_1")

    forget("Ant_0_0_0")
    forget("Ant_0_0_1")
    forget("A2Ax_0_0")
    forget("A2Ax_1_0")

    ref("d1")


  }

  val D1ScClash = Lemma(esD1ScClash) {
    forget("Suc_0")
    forget("Refl")
    unfold("Add1") atMost 1 in "Ant_0"
    decompose
    forget("Ant_0_0_0")
    forget("Ant_0_1")
    allL("DistinctConstructors", hov"v:nat")
    negL("DistinctConstructors_0")
    trivial
  }


  ctx += ProofDefinitionDeclaration(le"d1 0 y z", D1Bc)
  ctx += ProofDefinitionDeclaration(le"d1 (s n) y (s z)", D1Sc) // (s z)
  ctx += ProofDefinitionDeclaration(le"d1 (s n) y 0", D1ScClash)

  // Instantiation
  val d1Zero = instantiateProof(le"d1 0 y 2") // note: 2 is interpreted as a variable here
  val d1One = instantiateProof(le"d1 (s 0) y (s 3)") // note: same for 3
  val d1Two = instantiateProof(le"d1 (s (s 0)) y (s 3)")
  val d1Three = instantiateProof(le"d1 (s (s (s 0))) y (s 3)")

  val thestruct = StructCreators.extract(d1One)
  val cs = CharacteristicClauseSet(thestruct)




  //////////////////////////
  // Full proof
  //////////////////////////


  val phiBc = Lemma(esPhiBc) {
    forget("A2Ax")
    forget("Refl")
    unfold("Add2") atMost 1 in "Ant_0"
    unfold("Add1") atMost 1 in "Suc_0"
    axiomLog
  }


  val phiSc = Lemma(esPhiSc) {

    unfold("Add2") atMost 1 in "Ant_0"
    exL("Ant_0")
    andL
    allL("A2Ax", le"n:nat")
    allL("A2Ax_0", le"u:nat")
    forget("A2Ax_0")
    impL("A2Ax_0_0")
    axiomLog

    forget("Ant_0_0")
    eql("A2Ax_0_0", "Ant_0_1")
    forget("A2Ax_0_0")

    cut("cutLink", hof"Add1(n,s(y),z)")

    forget("Suc_0")
    ref("phi")

    ref("d1")
  }


  ctx += ProofDefinitionDeclaration(le"phi 0 y z", phiBc)
  ctx += ProofDefinitionDeclaration(le"phi (s n) y z", phiSc)

  val FullProof_0y0 = instantiateProof(le"phi 0 y 0")
  val redCut_0y0 = cutNormal(FullProof_0y0)

  val FullProof_2y2 = instantiateProof(le"phi (s (s 0)) y  (s (s 0))")
  val redCut_2y2 = cutNormal(FullProof_2y2)

  val FullProof_2y3 = instantiateProof(le"phi (s (s 0)) y (s (s (s 0)))")
  val redCut_2y3 = cutNormal(FullProof_2y3)

  val FullProof_3y2 = instantiateProof(le"phi (s (s (s 0))) y  (s (s 0))")
  val redCut_3y2 = cutNormal(FullProof_3y2)


  val FullProof1 = instantiateProof(le"phi (s 0) y z")
  val thestruct1 = StructCreators.extract(FullProof1)
  val cs1 = CharacteristicClauseSet(thestruct1)
  val redCut1 = cutNormal(FullProof1)

  val FullProof2z0 = instantiateProof(le"phi (s (s 0)) y 0")
  val FullProof2zsz = instantiateProof(le"phi (s (s 0)) y (s z)")

  try {
    val FullProof3 = instantiateProof.applyWithChecking(le"phi (s (s (s 0))) y z")
    // val thestruct3 = StructCreators.extract(FullProof3)
    // val cs3 = CharacteristicClauseSet(thestruct3)
    val redCut3 = cutNormal(FullProof3)
  } catch {
    case e: Exception =>
      print(s"Could not construct FullProof3: ${e.getMessage}")
  }




  // -----------------------------------------------------------------------------------------
  // Ab hier kommt Quatsch
  // -----------------------------------------------------------------------------------------

  // Run to see the clause set in prooftool
  // prooftool(cs)


  val num1 = Numeral(1).toString
  val st = s"phi ($num1) y ($num1)"
  // Step 1: Remove all type annotations of the form `: type`
  val noTypes = st.replaceAll("""\s*:\s*[^()\s]+""", "")
  // Step 2: Add space between function and argument
  val spaced = noTypes.replaceAll("""([a-zA-Z0-9_])\(""", "$1 (")

  //val proofTest = instantiateProof(le"$spaced")

  //val paramExp = le"$spaced"
  //val test = instantiateProof(le"$spaced")

  // val FullProofTest = isCutFree(cutNormal(instantiateProof(le"phi 0 y ($num3)")))


  def testCutElim(rows: Int, cols: Int): Unit = {
    val matrix = Vector.tabulate(rows, cols)((i, j) => (i, j))

    for {
      row <- matrix
      cell <- row
    } {
      println(s"$cell")

      val xParam = Numeral(cell._1).toString
      val yParam = Numeral(cell._2).toString
      println(s" x: $xParam , z: $yParam")

      //val cutFreeTest = isCutFree(instantiateProof(le"phi (s (s 0)) y  (s (s 0))"))

    }
  }


}