// --------------------- substitution begin

package at.logic.algorithms.shlk
import at.logic.calculi.slk._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol._
import at.logic.language.lambda.types.Definitions._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base._
import scala.Predef._

import at.logic.language.schema.{SchemaSubstitution1,unfoldSFormula,unfoldSTerm,lessThan,sims,leq}
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.language.lambda.symbols.VariableStringSymbol


//test version
object applySchemaSubstitution2 {
  def handleSchemaEquivalenceRule ( new_parent: LKProof,
                                    subst: SchemaSubstitution1[HOLExpression],
                                    old_parent: LKProof,
                                    old_proof: LKProof,
                                    constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas,
                                    m: FormulaOccurrence
                                    ) = {
    val new_proof = constructor( new_parent, subst(m.formula).asInstanceOf[HOLFormula])
    new_proof
  }
  def handleWeakening( new_parent: LKProof,
                       subst: SchemaSubstitution1[HOLExpression],
                       old_parent: LKProof,
                       old_proof: LKProof,
                       constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas,
                       m: FormulaOccurrence ) = {
    val new_proof = constructor( new_parent, unfoldSFormula(subst(m.formula).asInstanceOf[HOLFormula]) )
    new_proof
  }
  def handleContraction( new_parent: LKProof,
                         subst: SchemaSubstitution1[HOLExpression],
                         old_parent: LKProof,
                         old_proof: LKProof,
                         a1: FormulaOccurrence,
                         a2: FormulaOccurrence,
                         constructor: (LKProof, HOLFormula) => LKProof) = {

    //    println("n = "+subst.map.toList.head._2)
    //    println("\n\nContrL:")
    //    println("aux = "+subst(a1.formula))
    //    println("seq = "+new_parent.root)
    constructor( new_parent, unfoldSFormula(subst(a1.formula).asInstanceOf[HOLFormula]) )
    //    ( new_proof, computeMap( old_parent.root.antecedent ++ old_parent.root.succedent, old_proof, new_proof, new_parent._2 ) )
  }
  def handleBinaryProp( new_parent_1: LKProof,
                        new_parent_2: LKProof,
                        subst: SchemaSubstitution1[HOLExpression],
                        a1: FormulaOccurrence,
                        a2: FormulaOccurrence,
                        old_parent_1: LKProof,
                        old_parent_2: LKProof,
                        old_proof: LKProof,
                        constructor: (LKProof, LKProof, HOLFormula, HOLFormula) => LKProof) = {

    constructor( new_parent_1, new_parent_2, unfoldSFormula(subst(a1.formula).asInstanceOf[HOLFormula]), unfoldSFormula(subst(a2.formula).asInstanceOf[HOLFormula]) )
  }



  def handleRule( proof: LKProof, new_parents: List[LKProof], subst: SchemaSubstitution1[HOLExpression] ) : LKProof = {
    implicit val factory = defaultFormulaOccurrenceFactory
    proof match {

      case Axiom(ro) => {
        val a = Axiom(ro.antecedent.map(fo => unfoldSFormula(subst(fo.formula).asInstanceOf[HOLFormula])),ro.succedent.toList.map(fo => unfoldSFormula(subst(fo.formula).asInstanceOf[HOLFormula])))
        a
      }
      case WeakeningLeftRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningLeftRule.apply, m )
      case WeakeningRightRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningRightRule.apply, m)
      case ContractionLeftRule(p, s, a1, a2, m) => handleContraction( new_parents.head, subst, p, proof, a1, a2, sContractionLeftRule.apply )
      case ContractionRightRule(p, s, a1, a2, m) => handleContraction( new_parents.head, subst, p, proof, a1, a2, sContractionRightRule.apply)
      case CutRule(p1, p2, s, a1, a2) => {
        val new_p1 = new_parents.head
        val new_p2 = new_parents.last
        //        println("Cut:")
        //        println(new_p1.root)
        //        println("aux = "+subst( a1.formula ))
        //        println(new_p2.root)
        //val new_proof = CutRule( new_p1._1, new_p2._1, new_p1._2( a1 ), new_p2._2( a2 ) )
        val new_proof = sCutRule( new_p1, new_p2, unfoldSFormula(subst(a1.formula).asInstanceOf[HOLFormula]) )
        //    ( new_proof, computeMap(
        //     p1.root.antecedent ++ (p1.root.succedent - a1) ++ (p2.root.antecedent - a2) ++ p2.root.succedent,
        //    proof, new_proof, new_p1._2 ++ new_p2._2 ) )
        new_proof
      }
      case AndRightRule(p1, p2, s, a1, a2, m) => handleBinaryProp( new_parents.head, new_parents.last, subst, a1, a2, p1, p2, proof, AndRightRule.apply )

      case AndLeft1Rule(p, s, a, m) => {
        val f = m.formula match { case And(_, w) => w }
        val new_parent = new_parents.head
        val new_proof = AndLeft1Rule( new_parent, unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula]), unfoldSFormula(subst(f.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula] ) )
        new_proof
      }
      case AndLeft2Rule(p, s, a, m) => {
        val f = m.formula match { case And(w, _) => w }
        val new_parent = new_parents.head
        //        val new_proof = AndLeft2Rule( new_parent._1, subst( f ).asInstanceOf[HOLFormula], new_parent._2( a ) )
        val new_proof = AndLeft2Rule( new_parent, unfoldSFormula(subst(f.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula]), unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula]) )
        new_proof
      }
      //    case OrLeftRule(p1, p2, s, a1, a2, m) => handleBinaryProp( new_parents.head, new_parents.last, subst, a1, a2, p1, p2, proof, OrLeftRule.apply )

      case OrRight1Rule(p, s, a, m) => {
        val f = m.formula match {
          case Or(_, w) => w
          case _ => throw new Exception("Error in OrRight1Rule in unfoldSIND.scala")
        }
        val new_parent = new_parents.head
        //        val new_proof = OrRight1Rule( new_parent._1, new_parent._2( a ), subst( f ).asInstanceOf[HOLFormula] )
        val new_proof = OrRight1Rule( new_parent, unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula]), unfoldSFormula(subst(f.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula] ) )
        new_proof
      }
      case OrRight2Rule(p, s, a, m) => {
        val f = m.formula match {
          case Or(w, _) => w
          case _ => throw new Exception("Error in OrRight2Rule in unfoldSIND.scala")
        }
        val new_parent = new_parents.head
        val new_proof = OrRight2Rule( new_parent, unfoldSFormula(subst(f.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula]), unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula] ) )
        new_proof
      }
      case NegLeftRule(p, s, a, m) => {
        val new_parent = new_parents.head
        //  val new_proof = NegLeftRule( new_parent._1, new_parent._2( a ) )
        val new_proof = NegLeftRule( new_parent, unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula]) )
        //       ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
        new_proof
      }
      case NegRightRule(p, s, a, m) => {
        val new_parent = new_parents.head
        val new_proof = NegRightRule( new_parent, unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula]) )
        new_proof
      }
      case ImpLeftRule(p1, p2, s, a1, a2, m) => {
        val new_parent1 = new_parents.head
        val new_parent2 = new_parents.last
        ImpLeftRule(new_parent1, new_parent2, unfoldSFormula(subst(a1.formula).asInstanceOf[HOLFormula]), unfoldSFormula(subst(a2.formula).asInstanceOf[HOLFormula]))
      }
      case ImpRightRule(p, s, a1, a2, m) => {
        val new_parent = new_parents.head
        ImpRightRule(new_parent, unfoldSFormula(subst(a1.formula).asInstanceOf[HOLFormula]), unfoldSFormula(subst(a2.formula).asInstanceOf[HOLFormula]))
      }
      case ForallLeftRule(p, seq, a, m, t) => {
        val new_parent = new_parents.head
        ForallLeftRule(new_parent, unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula]), unfoldSFormula(subst(m.formula).asInstanceOf[HOLFormula]), unfoldSTerm(subst(t)))
      }
      case ForallRightRule(p, seq, a, m, v) => {
        val new_parent = new_parents.head
        ForallRightRule(new_parent, unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula]), unfoldSFormula(subst(m.formula).asInstanceOf[HOLFormula]), subst(v).asInstanceOf[HOLVar])
      }
    }
  }


  //************************************************************************************


  def apply( proof_name: String, number: Int, ProofLinkPassing:List[Pair[HOLExpression,HOLExpression]] ): LKProof = {
      val rewriterules = new scala.collection.mutable.HashMap[HOLFormula, HOLFormula]
      if(number == 0) CloneLKProof2(SchemaProofDB.get(proof_name).base,proof_name,rewriterules,0,1,ProofLinkPassing)
      else anotherfunction(proof_name: String, maketogether(number),rewriterules, ProofLinkPassing)
  }
  def anotherfunction(proof_name: String, number:HOLExpression, rewriterules: scala.collection.mutable.HashMap[HOLFormula, HOLFormula], ProofLinkPassing:List[Pair[HOLExpression,HOLExpression]] ): LKProof = {
    val k =  backToInt(number)
    if (k  == 0)  CloneLKProof2(SchemaProofDB.get(proof_name).base,proof_name,rewriterules,k,1,ProofLinkPassing)
    else{
      val proofist = CloneLKProof2(SchemaProofDB.get(proof_name).rec,proof_name,rewriterules,k-1,2, ProofLinkPassing)
      CloneLKProof2(proofist,proof_name,rewriterules,k-1,1,ProofLinkPassing)
    }
  }
}

//creates a copy of an existing LK proof (used for unfolding, not to have cycles in the tree having the base proof several times)
//uses t.r.s. !!!
object CloneLKProof2 {
  import at.logic.language.hol._
  def rewriteruleconverter( argsPos: Int, mainArgsList:Seq[HOLExpression], ausArgsList:Seq[HOLExpression],  Thepair: (Seq[HOLExpression], Seq[HOLExpression]) ):  (Seq[HOLExpression], Seq[HOLExpression])  = {
      if(mainArgsList.isEmpty) Thepair
      else rewriteruleconverter( argsPos+1, mainArgsList.tail, ausArgsList, Thepair)




  }
  def apply(proof: LKProof,name:String, rewriterules:scala.collection.mutable.HashMap[HOLFormula, HOLFormula],proofSize: Int, version: Int, ProofLinkPassing:List[Pair[HOLExpression,HOLExpression]] ):LKProof = {
    proof match {
      case trsArrowLeftRule(p, s, a, m) => {
        if(version == 0)proof
        else if(version == 1) apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 2){
           proof
        }
        else proof
      }
      case trsArrowRightRule(p, s, a, m) => {
        if(version == 0)proof
        else if(version == 1) apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 2){
           proof
        }
        else proof
      }

      case foldLeftRule(p, s, a, m) => {
        if(version == 0){
          apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        }
        else if(version == 1) {
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          foldLeftRule(new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          foldLeftRule(new_p,cloneMySol(a.formula.asInstanceOf[HOLFormula],proofSize),cloneMySol(m.formula.asInstanceOf[HOLFormula],proofSize))
        }
        else proof
      }
      case foldRightRule(p, s, a, m) => {
        if(version == 0){
          //val main = SchemaSubTerms(m.formula)
          //val aux = SchemaSubTerms(a.formula)
          // d.tail.tail.head.isInstanceOf[HOLAbs]
          println(m.formula  + "   "+ a.formula)
          //println( SchemaSubTerms(m.formula) + "   "+ SchemaSubTerms(a.formula)/*+ "   "+ d.tail.tail.head.isInstanceOf[HOLAbs] + d.tail.tail.head.isInstanceOf[HOLApp]  +"  "+ d.tail.tail.head +"w   "+ d.head + "    " +  d.head.isInstanceOf[HOLAbs] + d.head.isInstanceOf[HOLApp]*/  )
          //for each  value in main find all instances in within aux and replace both occurances
          //in main and aux with SubConst(i) where i is a number indicating the arguemnt position.
          //Add these versions to rewrite rules.
          //rewriterules.put(m.formula,a.formula)
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          foldRightRule(new_p, a.formula.asInstanceOf[HOLFormula], m.formula.asInstanceOf[HOLFormula])
        }
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          foldRightRule(new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          foldRightRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize))
        }
        else proof
      }
      case foldRule(p, s, a, m) => {
        if(version == 0){
          //SchemaSubTerms(m.formula)
          //SchemaSubTerms(a.formula)
          //println( SchemaSubTerms(m.formula) + "   "+ SchemaSubTerms(a.formula))
          //rewriterules.put(m.formula,a.formula)
          apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          //foldRightRule(new_p, a, m)
        }
        else if(version == 1)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 2){ proof         }         else proof
      }

      case Axiom(ro) => {
        if(version == 0)proof
        else if(version == 1)  Axiom(ro.antecedent.map(fo => iterateOnFormula(fo.formula.asInstanceOf[HOLFormula],ProofLinkPassing)),ro.succedent.map(fo => iterateOnFormula(fo.formula.asInstanceOf[HOLFormula],ProofLinkPassing)))
        else if(version == 2){
          Axiom(ro.antecedent.map(fo => cloneMySol(fo.formula.asInstanceOf[HOLFormula],proofSize)),ro.succedent.map(fo => cloneMySol(fo.formula.asInstanceOf[HOLFormula],proofSize)))
        }
        else proof
      }

      case AndLeftEquivalenceRule1(p, s, a, m) => {
        if(version == 0) apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          AndLeftEquivalenceRule1(new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          AndLeftEquivalenceRule1(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize))
        }
        else proof
      }
      case AndRightEquivalenceRule1(p, s, a, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          AndRightEquivalenceRule1(new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          AndRightEquivalenceRule1(new_p, cloneMySol(a.formula,proofSize),cloneMySol(m.formula,proofSize))
        }
        else proof
      }

      case OrRightEquivalenceRule1(p, s, a, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          OrRightEquivalenceRule1(new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          OrRightEquivalenceRule1(new_p, cloneMySol(a.formula,proofSize),  cloneMySol(m.formula,proofSize))
        }
        else proof
      }
      case AndLeftEquivalenceRule3(p, s, a, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          AndLeftEquivalenceRule3(new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          AndLeftEquivalenceRule3(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize))
        }
        else proof
      }
      case AndRightEquivalenceRule3(p, s, a, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          AndRightEquivalenceRule3(new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          AndRightEquivalenceRule3(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize))
        }
        else proof
      }

      case OrRightEquivalenceRule3(p, s, a, m) => {
        if(version == 0) apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          OrRightEquivalenceRule3(new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing),iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          OrRightEquivalenceRule3(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize))
        }
        else proof
      }

      case WeakeningLeftRule(p, _, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          implicit val factory = defaultFormulaOccurrenceFactory
             WeakeningLeftRule( new_p, iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          implicit val factory = defaultFormulaOccurrenceFactory
          WeakeningLeftRule( new_p, cloneMySol(m.formula,proofSize) )
        }
        else proof
      }

      case WeakeningRightRule(p, _, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          implicit val factory = defaultFormulaOccurrenceFactory
          WeakeningRightRule( new_p, iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          implicit val factory = defaultFormulaOccurrenceFactory
          WeakeningRightRule( new_p, cloneMySol(m.formula,proofSize) )
        }
        else proof
      }

      case CutRule( p1, p2, _, a1, a2 ) => {
        if(version == 0){
          apply(p1,name,rewriterules,proofSize,version,ProofLinkPassing)
          apply(p2,name,rewriterules,proofSize,version,ProofLinkPassing)
        }
        else if(version == 1){
          val new_p1 =  apply(p1,name,rewriterules,proofSize,version,ProofLinkPassing)
          val new_p2 =  apply(p2,name,rewriterules,proofSize,version,ProofLinkPassing)
          CutRule(new_p1, new_p2, iterateOnFormula(a2.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p1 =  apply(p1,name,rewriterules,proofSize,version,ProofLinkPassing)
          val new_p2 =  apply(p2,name,rewriterules,proofSize,version,ProofLinkPassing)
          CutRule(new_p1, new_p2, cloneMySol(a2.formula,proofSize))
        }
        else proof
      }

      case OrLeftRule(p1, p2, _, a1, a2, m) => {
        if(version == 0){
          apply(p1,name,rewriterules,proofSize,version,ProofLinkPassing)
          apply(p2,name,rewriterules,proofSize,version,ProofLinkPassing)
        }
        else if(version == 1){
          val new_p1 =  apply(p1,name,rewriterules,proofSize,version,ProofLinkPassing)
          val new_p2 =  apply(p2,name,rewriterules,proofSize,version,ProofLinkPassing)
          OrLeftRule(new_p1, new_p2, iterateOnFormula(a1.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(a2.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p1 =  apply(p1,name,rewriterules,proofSize,version,ProofLinkPassing)
          val new_p2 =  apply(p2,name,rewriterules,proofSize,version,ProofLinkPassing)
          OrLeftRule(new_p1, new_p2, cloneMySol(a1.formula,proofSize), cloneMySol(a2.formula,proofSize))
        }
        else proof
      }

      case AndRightRule(p1, p2, _, a1, a2, m) => {
        if(version == 0){
          apply(p1,name,rewriterules,proofSize,version,ProofLinkPassing)
          apply(p2,name,rewriterules,proofSize,version,ProofLinkPassing)
        }
        else if(version == 1){
          val new_p1 =  apply(p1,name,rewriterules,proofSize,version,ProofLinkPassing)
          val new_p2 =  apply(p2,name,rewriterules,proofSize,version,ProofLinkPassing)
           AndRightRule(new_p1, new_p2, iterateOnFormula(a1.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(a2.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p1 =  apply(p1,name,rewriterules,proofSize,version,ProofLinkPassing)
          val new_p2 =  apply(p2,name,rewriterules,proofSize,version,ProofLinkPassing)
          AndRightRule(new_p1, new_p2, cloneMySol(a1.formula,proofSize), cloneMySol(a2.formula,proofSize))
        }
        else proof
      }
      case ImpLeftRule(p1, p2, s, a1, a2, m) => {
        if(version == 0){
          apply(p1,name,rewriterules,proofSize,version,ProofLinkPassing)
          apply(p2,name,rewriterules,proofSize,version,ProofLinkPassing)
        }
        else if(version == 1){
          val new_p1 =  apply(p1,name,rewriterules,proofSize,version,ProofLinkPassing)
          val new_p2 =  apply(p2,name,rewriterules,proofSize,version,ProofLinkPassing)
          ImpLeftRule(new_p1, new_p2, iterateOnFormula(a1.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(a2.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p1 =  apply(p1,name,rewriterules,proofSize,version,ProofLinkPassing)
          val new_p2 =  apply(p2,name,rewriterules,proofSize,version,ProofLinkPassing)
          ImpLeftRule(new_p1, new_p2, cloneMySol(a1.formula,proofSize), cloneMySol(a2.formula,proofSize))
        }
        else proof
      }

      case NegLeftRule( p, _, a, m ) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          NegLeftRule( new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing) )
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          NegLeftRule( new_p, cloneMySol(a.formula,proofSize) )
        }
        else proof
      }

      case AndLeft1Rule(p, r, a, m) =>  {
        if(version == 0)  apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          val a2 = m.formula  match { case And(l, right) => right }
           AndLeft1Rule( new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(a2.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          val a2 = m.formula  match { case And(l, right) => right }
          AndLeft1Rule( new_p, cloneMySol(a.formula,proofSize), cloneMySol(a2,proofSize))
        }
        else proof
      }

      case AndLeft2Rule(p, r, a, m) =>  {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          val a2 = m.formula  match { case And(l, _) => l }
          AndLeft2Rule( new_p, iterateOnFormula(a2.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing) )
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          val a2 = m.formula  match { case And(l, _) => l }
          AndLeft2Rule( new_p, cloneMySol(a2,proofSize), cloneMySol(a.formula,proofSize) )
        }
        else proof
      }

      case OrRight1Rule(p, r, a, m) =>  {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
           val a2 = m.formula  match { case Or(_, ra) => ra }
           OrRight1Rule( new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing),iterateOnFormula(a2.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          val a2 = m.formula  match { case Or(_, ra) => ra }
          OrRight1Rule( new_p,cloneMySol(a.formula,proofSize),cloneMySol(a2,proofSize))
        }
        else proof
      }

      case OrRight2Rule(p, r, a, m) =>  {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
           val a2 = m.formula match { case Or(l, _) => l }
           OrRight2Rule( new_p, iterateOnFormula(a2.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          val a2 = m.formula  match { case Or(l, _) => l }
          OrRight2Rule( new_p, cloneMySol(a2,proofSize), cloneMySol(a.formula,proofSize))
        }
        else proof
      }

      case NegRightRule( p, _, a, m ) => {
         if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
         else if(version == 1){
            val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
            NegRightRule( new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing) )
         }
         else if(version == 2){
           val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
           NegRightRule( new_p, cloneMySol(a.formula,proofSize))
         }
         else proof
      }

      case ContractionLeftRule(p, _, a1, a2, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
           ContractionLeftRule( new_p, iterateOnFormula(a1.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          ContractionLeftRule( new_p, cloneMySol(a1.formula,proofSize))
        }
        else proof
      }

      case ContractionRightRule(p, _, a1, a2, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
           ContractionRightRule( new_p, iterateOnFormula(a1.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          ContractionRightRule( new_p, cloneMySol(a1.formula,proofSize))
        }
        else proof
      }

      case ForallLeftRule(p, seq, a, m, t) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          ForallLeftRule(new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula.apply2(t,ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          ForallLeftRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize), cloneMyTerm(t,proofSize))
        }
        else proof
      }
      case ForallRightRule(p, seq, a, m, v) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          ForallRightRule(new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula.apply2(v,ProofLinkPassing).asInstanceOf[HOLVar])
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          ForallRightRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize), cloneMyTerm(v,proofSize).asInstanceOf[HOLVar])
        }
        else proof
      }

      case ExistsRightRule(p, seq, a, m, t) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
            ExistsRightRule(new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula.apply2(t,ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          ExistsRightRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize), cloneMyTerm(t,proofSize))
        }
        else proof
      }
      case ExistsLeftRule(p, seq, a, m, v) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
           ExistsLeftRule(new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula.apply2(v,ProofLinkPassing).asInstanceOf[HOLVar])
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          ExistsLeftRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize), cloneMyTerm(v,proofSize).asInstanceOf[HOLVar])
        }
        else proof
      }

      case ExistsHyperRightRule(p, seq, a, m, t) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
           ExistsHyperRightRule(new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula.apply2(t,ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          ExistsHyperRightRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize), cloneMyTerm(t,proofSize))
        }
        else proof
      }
      case ExistsHyperLeftRule(p, seq, a, m, v) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
           ExistsHyperLeftRule(new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula.apply2(v,ProofLinkPassing).asInstanceOf[HOLVar])
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          ExistsHyperLeftRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize), cloneMyTerm(v,proofSize).asInstanceOf[HOLVar])
        }
        else proof
      }
      case ForallHyperLeftRule(p, seq, a, m, t) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
           ForallHyperLeftRule(new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula.apply2(t,ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          ForallHyperLeftRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize), cloneMyTerm(t,proofSize) )
        }
        else proof
      }
      case ForallHyperRightRule(p, seq, a, m, v) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
           ForallHyperRightRule(new_p, iterateOnFormula(a.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(m.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula.apply2(v,ProofLinkPassing).asInstanceOf[HOLVar])
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          ForallHyperRightRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize), cloneMyTerm(v,proofSize).asInstanceOf[HOLVar] )
        }
        else proof
      }

      case ImpRightRule(p, s, a1, a2, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
           ImpRightRule(new_p, iterateOnFormula(a1.formula.asInstanceOf[HOLFormula],ProofLinkPassing), iterateOnFormula(a2.formula.asInstanceOf[HOLFormula],ProofLinkPassing))
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version,ProofLinkPassing)
          ImpRightRule(new_p, cloneMySol(a1.formula,proofSize), cloneMySol(a2.formula,proofSize))
        }
        else proof
      }
      case FOSchemaProofLinkRule(s,name2,l) => {
        if(version == 0)proof
        else if(version == 1){
          val next = backToInt(l.head)
          if(next == 0) CloneLKProof2(SchemaProofDB.get(name2).base,name2,rewriterules,0,version,ProofLinkPassing)
          else{
            if(SchemaProofDB.getLinkTerms(name2).length != 0 && SchemaProofDB.getLinkTerms(name2).length == l.tail.length) {
              val ProofLinkPassingNew = SchemaProofDB.getLinkTerms(name2).zip(l.tail)
              applySchemaSubstitution2(name2,next,ProofLinkPassingNew)
            }
            else if(SchemaProofDB.getLinkTerms(name2).length == 0 && SchemaProofDB.getLinkTerms(name2).length == l.tail.length)
              applySchemaSubstitution2(name2,next,List())
            else throw new Exception("ERROR ProofLinks are wrong !\n")
          }
        }
        else if(version == 2) FOSchemaProofLinkRule(
          new FSequent(s.antecedent.map( x => cloneMySol(x.formula,proofSize)),
                      s.succedent.map(x => cloneMySol(x.formula,proofSize))),name2,l.map(x => cloneMyTerm(x,proofSize)))
        else proof
      }
      case _ => throw new Exception("ERROR in unfolding: CloneLKProof2: missing rule !\n" + proof.rule + "\n")
    }}

}
object iterateOnFormula {
  import at.logic.language.hol._
  def apply(form:HOLFormula,ProofLinkPassing:List[Pair[HOLExpression,HOLExpression]]):HOLFormula = {
    if(ProofLinkPassing.length > 0){
      var tempform = form
    ProofLinkPassing.map( x => {
      tempform = cloneMySol.apply2(tempform,x._1,x._2)
      tempform })
      tempform
    }
    else form
  }
  def apply2(term:HOLExpression,ProofLinkPassing:List[Pair[HOLExpression,HOLExpression]]):HOLExpression = {
    if(ProofLinkPassing.length > 0){
      var tempterm = term
      ProofLinkPassing.map( x => {
        tempterm = cloneMyTerm(tempterm,x._1,x._2)
        tempterm })
        tempterm
    }
    else term
  }
}
object cloneMySol{
  def apply(form:HOLFormula, proofSize: Int ):HOLFormula = {
    form match {
      case Neg(nF) => {
        val finForm = apply(nF.asInstanceOf[HOLFormula],proofSize)
        Neg(finForm)
      }
      case And(lF,rF) => {
        val finFormL = apply(lF,proofSize)
        val finFormR = apply(rF,proofSize)
        And(finFormL,finFormR)
      }
      case Or(lF,rF) => {
        val finFormL = apply(lF,proofSize)
        val finFormR = apply(rF,proofSize)
        Or(finFormL,finFormR)
      }
      case Imp(lF,rF) => {
        val finFormL = apply(lF,proofSize)
        val finFormR = apply(rF,proofSize)
        Imp(finFormL,finFormR)
      }
      case AllVar(aV,aF) => {
        val finForm = apply(aF,proofSize)
        AllVar(aV,finForm)
      }
      case ExVar(aV,aF) => {
        val finForm = apply(aF,proofSize)
        ExVar(aV,finForm)
      }
      case Equation(l,r) => Equation(cloneMyTerm(l,proofSize),cloneMyTerm(r,proofSize))
      case lessThan(l,r) => lessThan(cloneMyTerm(l,proofSize),cloneMyTerm(r,proofSize))
      case sims(l,r) => sims(cloneMyTerm(l,proofSize),cloneMyTerm(r,proofSize))
      case leq(l,r) =>  leq(cloneMyTerm(l,proofSize),cloneMyTerm(r,proofSize))
      case Atom(set) => {
        val atomName = set.asInstanceOf[Pair[ConstantStringSymbol,List[HOLExpression]]]._1
        val SOLList = set.asInstanceOf[Pair[ConstantStringSymbol,List[HOLExpression]]]._2
        val finSOLList = SOLList.asInstanceOf[List[HOLExpression]].map( x => cloneMyTerm(x,proofSize))
        Atom(atomName,finSOLList)
      }
      case _ => throw new Exception("ERROR in unfolding missing formula !\n" + form.toString + "\n")
    }
  }
  def apply2(form:HOLFormula, IN:HOLExpression, OUT:HOLExpression):HOLFormula = {
    form match {
      case Neg(nF) => {
        val finForm = apply2(nF.asInstanceOf[HOLFormula],IN,OUT)
        Neg(finForm)
      }
      case And(lF,rF) => {
        val finFormL = apply2(lF,IN,OUT)
        val finFormR = apply2(rF,IN,OUT)
        And(finFormL,finFormR)
      }
      case Or(lF,rF) => {
        val finFormL = apply2(lF,IN,OUT)
        val finFormR = apply2(rF,IN,OUT)
        Or(finFormL,finFormR)
      }
      case Imp(lF,rF) => {
        val finFormL = apply2(lF,IN,OUT)
        val finFormR = apply2(rF,IN,OUT)
        Imp(finFormL,finFormR)
      }
      case AllVar(aV,aF) => {
        val finForm = apply2(aF,IN,OUT)
        AllVar(aV,finForm)
      }
      case ExVar(aV,aF) => {
        val finForm = apply2(aF,IN,OUT)
        ExVar(aV,finForm)
      }
      case Equation(l,r) => Equation(cloneMyTerm(l,IN,OUT),cloneMyTerm(r,IN,OUT))
      case lessThan(l,r) => lessThan(cloneMyTerm(l,IN,OUT),cloneMyTerm(r,IN,OUT))
      case sims(l,r) => sims(cloneMyTerm(l,IN,OUT),cloneMyTerm(r,IN,OUT))
      case leq(l,r) =>  leq(cloneMyTerm(l,IN,OUT),cloneMyTerm(r,IN,OUT))
      case Atom(set) => {
        val atomName = set.asInstanceOf[Pair[ConstantStringSymbol,List[HOLExpression]]]._1
        val SOLList = set.asInstanceOf[Pair[ConstantStringSymbol,List[HOLExpression]]]._2
        val finSOLList = SOLList.asInstanceOf[List[HOLExpression]].map( x => cloneMyTerm(x,IN,OUT))
        Atom(atomName,finSOLList)
      }
      case _ => throw new Exception("ERROR in unfolding missing formula !\n" + form.toString + "\n")
    }
  }
}

object cloneMyTerm{
  import at.logic.language.hol._
  def apply(term:HOLExpression , proofSize:Int):HOLExpression = {
    term match {
      case Function(ConstantStringSymbol(n),l,t) if n =="schS" && t == ind => Function(ConstantStringSymbol(n),l.map(x => apply(x,proofSize)),t)
      case HOLVar(VariableStringSymbol(n),t) if n== "k" && t == ind =>  maketogether(proofSize)
      case Function(ConstantStringSymbol(n),l,t) if t == ind => Function(ConstantStringSymbol(n),l.map(x => apply(x,proofSize)),t)
      case Function(ConstantStringSymbol(n),l,t) if t == i => Function(ConstantStringSymbol(n),l.map(x => apply(x,proofSize)),t)
      case HOLVar(n,t) if t == i | t == ind->i =>HOLVar(n,t)
      case HOLConst(n,t)  => HOLConst(n,t)
      case HOLAbs(x, t)   => HOLAbs(x, apply(t,proofSize))
      case _ => throw new Exception("ERROR in unfolding missing formula !\n" + term.toString + "\n")

    }
  }
  def apply(term:HOLExpression , IN:HOLExpression, OUT:HOLExpression):HOLExpression = {
    term match {
      case Function(ConstantStringSymbol(n),l,t) if n =="schS" && t == ind => Function(ConstantStringSymbol(n),l,t)
      case HOLVar(VariableStringSymbol(n),t) if n== "k" && t == ind =>  HOLVar(VariableStringSymbol(n),t)
      case Function(ConstantStringSymbol(n),l,t) if t == ind => Function(ConstantStringSymbol(n),l.map(x => apply(x,IN,OUT)),t)
      case Function(ConstantStringSymbol(n),l,t) if t == i => IN match {
          case Function(ConstantStringSymbol(ni),li,ti) if n == ni && l.equals(li) && t == ti => OUT
          case Function(ConstantStringSymbol(ni),li,ti) if n.toList.head == ni.toList.head  => OUT match {
            case HOLVar(VariableStringSymbol(no),to) =>  Function(ConstantStringSymbol(no),li,ti)
            case _ => Function(ConstantStringSymbol(ni),li,ti)
          }
          case _ =>  Function(ConstantStringSymbol(n),l.map(x => apply(x,IN,OUT)),t)
        }
      case HOLVar(VariableStringSymbol(n),t) if t == i | t == ind->i => IN match {
        case HOLVar(VariableStringSymbol(ni),ti) if  t == ti  && ni == n  => OUT
        case _ => HOLVar(VariableStringSymbol(n),t)
      }
      case HOLConst(ConstantStringSymbol(n),t)  =>  IN match {
        case HOLConst(ConstantStringSymbol(ni),ti) if  t == ti  && ni == n => OUT
        case _ => HOLConst(ConstantStringSymbol(n),t)
      }
      case HOLAbs(x, t)   => HOLAbs(x, apply(t,IN,OUT))
      case _ => throw new Exception("ERROR in unfolding missing formula !\n" + term.toString + "\n")

    }
  }
}








