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


  def apply( proof_name: String, number: Int ): LKProof = {
      val rewriterules = new scala.collection.mutable.HashMap[HOLFormula, HOLFormula]
      if(number == 0) CloneLKProof2(SchemaProofDB.get(proof_name).base,proof_name,rewriterules,0,1)
      else anotherfunction(proof_name: String, maketogether(number),rewriterules )
  }
  def anotherfunction(proof_name: String, number:HOLExpression, rewriterules: scala.collection.mutable.HashMap[HOLFormula, HOLFormula] ): LKProof = {
    val k =  backToInt(number)
    if (k  == 0)  CloneLKProof2(SchemaProofDB.get(proof_name).base,proof_name,rewriterules,k,1)
    else{
      val proofist = CloneLKProof2(SchemaProofDB.get(proof_name).rec,proof_name,rewriterules,k-1,2)
      CloneLKProof2(proofist,proof_name,rewriterules,k-1,1)
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
  def apply(proof: LKProof,name:String, rewriterules:scala.collection.mutable.HashMap[HOLFormula, HOLFormula],proofSize: Int, version: Int):LKProof = {
    proof match {
      case trsArrowLeftRule(p, s, a, m) => {
        if(version == 0)proof
        else if(version == 1) apply(p,name,rewriterules,proofSize,version)
        else if(version == 2){
           proof
        }
        else proof
      }
      case trsArrowRightRule(p, s, a, m) => {
        if(version == 0)proof
        else if(version == 1) apply(p,name,rewriterules,proofSize,version)
        else if(version == 2){
           proof
        }
        else proof
      }

      case foldLeftRule(p, s, a, m) => {
        if(version == 0){
          apply(p,name,rewriterules,proofSize,version)
        }
        else if(version == 1) {
          val new_p = apply(p,name,rewriterules,proofSize,version)
          foldLeftRule(new_p, a.formula.asInstanceOf[HOLFormula], m.formula.asInstanceOf[HOLFormula])
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
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
          val new_p = apply(p,name,rewriterules,proofSize,version)
          foldRightRule(new_p, a.formula.asInstanceOf[HOLFormula], m.formula.asInstanceOf[HOLFormula])
        }
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          foldRightRule(new_p, a.formula.asInstanceOf[HOLFormula], m.formula.asInstanceOf[HOLFormula])
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
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
          apply(p,name,rewriterules,proofSize,version)
          //foldRightRule(new_p, a, m)
        }
        else if(version == 1)apply(p,name,rewriterules,proofSize,version)
        else if(version == 2){ proof         }         else proof
      }

      case Axiom(ro) => {
        if(version == 0)proof
        else if(version == 1)  Axiom(ro.antecedent.map(fo => fo.formula.asInstanceOf[HOLFormula]),ro.succedent.map(fo => fo.formula.asInstanceOf[HOLFormula]))
        else if(version == 2){
          Axiom(ro.antecedent.map(fo => cloneMySol(fo.formula.asInstanceOf[HOLFormula],proofSize)),ro.succedent.map(fo => cloneMySol(fo.formula.asInstanceOf[HOLFormula],proofSize)))
        }
        else proof
      }

      case AndLeftEquivalenceRule1(p, s, a, m) => {
        if(version == 0) apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          AndLeftEquivalenceRule1(new_p, a.formula.asInstanceOf[HOLFormula], m.formula.asInstanceOf[HOLFormula])
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          AndLeftEquivalenceRule1(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize))
        }
        else proof
      }
      case AndRightEquivalenceRule1(p, s, a, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          AndRightEquivalenceRule1(new_p, a.formula.asInstanceOf[HOLFormula], m.formula.asInstanceOf[HOLFormula])
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          AndRightEquivalenceRule1(new_p, cloneMySol(a.formula,proofSize),cloneMySol(m.formula,proofSize))
        }
        else proof
      }

      case OrRightEquivalenceRule1(p, s, a, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          OrRightEquivalenceRule1(new_p, a.formula.asInstanceOf[HOLFormula], m.formula.asInstanceOf[HOLFormula])
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          OrRightEquivalenceRule1(new_p, cloneMySol(a.formula,proofSize),  cloneMySol(m.formula,proofSize))
        }
        else proof
      }
      case AndLeftEquivalenceRule3(p, s, a, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          AndLeftEquivalenceRule3(new_p, a.formula.asInstanceOf[HOLFormula], m.formula.asInstanceOf[HOLFormula])
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          AndLeftEquivalenceRule3(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize))
        }
        else proof
      }
      case AndRightEquivalenceRule3(p, s, a, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          AndRightEquivalenceRule3(new_p, a.formula.asInstanceOf[HOLFormula], m.formula.asInstanceOf[HOLFormula])
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          AndRightEquivalenceRule3(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize))
        }
        else proof
      }

      case OrRightEquivalenceRule3(p, s, a, m) => {
        if(version == 0) apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          OrRightEquivalenceRule3(new_p, a.formula.asInstanceOf[HOLFormula], m.formula.asInstanceOf[HOLFormula])
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          OrRightEquivalenceRule3(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize))
        }
        else proof
      }

      case WeakeningLeftRule(p, _, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          implicit val factory = defaultFormulaOccurrenceFactory
             WeakeningLeftRule( new_p, m.formula )
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          implicit val factory = defaultFormulaOccurrenceFactory
          WeakeningLeftRule( new_p, cloneMySol(m.formula,proofSize) )
        }
        else proof
      }

      case WeakeningRightRule(p, _, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          implicit val factory = defaultFormulaOccurrenceFactory
          WeakeningRightRule( new_p, m.formula )
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          implicit val factory = defaultFormulaOccurrenceFactory
          WeakeningRightRule( new_p, cloneMySol(m.formula,proofSize) )
        }
        else proof
      }

      case CutRule( p1, p2, _, a1, a2 ) => {
        if(version == 0){
          apply(p1,name,rewriterules,proofSize,version)
          apply(p2,name,rewriterules,proofSize,version)
        }
        else if(version == 1){
          val new_p1 =  apply(p1,name,rewriterules,proofSize,version)
          val new_p2 =  apply(p2,name,rewriterules,proofSize,version)
          CutRule(new_p1, new_p2, a2.formula)
        }
        else if(version == 2){
          val new_p1 =  apply(p1,name,rewriterules,proofSize,version)
          val new_p2 =  apply(p2,name,rewriterules,proofSize,version)
          CutRule(new_p1, new_p2, cloneMySol(a2.formula,proofSize))
        }
        else proof
      }

      case OrLeftRule(p1, p2, _, a1, a2, m) => {
        if(version == 0){
          apply(p1,name,rewriterules,proofSize,version)
          apply(p2,name,rewriterules,proofSize,version)
        }
        else if(version == 1){
          val new_p1 =  apply(p1,name,rewriterules,proofSize,version)
          val new_p2 =  apply(p2,name,rewriterules,proofSize,version)
          OrLeftRule(new_p1, new_p2, a1.formula, a2.formula)
        }
        else if(version == 2){
          val new_p1 =  apply(p1,name,rewriterules,proofSize,version)
          val new_p2 =  apply(p2,name,rewriterules,proofSize,version)
          OrLeftRule(new_p1, new_p2, cloneMySol(a1.formula,proofSize), cloneMySol(a2.formula,proofSize))
        }
        else proof
      }

      case AndRightRule(p1, p2, _, a1, a2, m) => {
        if(version == 0){
          apply(p1,name,rewriterules,proofSize,version)
          apply(p2,name,rewriterules,proofSize,version)
        }
        else if(version == 1){
          val new_p1 =  apply(p1,name,rewriterules,proofSize,version)
          val new_p2 =  apply(p2,name,rewriterules,proofSize,version)
           AndRightRule(new_p1, new_p2, a1.formula, a2.formula)
        }
        else if(version == 2){
          val new_p1 =  apply(p1,name,rewriterules,proofSize,version)
          val new_p2 =  apply(p2,name,rewriterules,proofSize,version)
          AndRightRule(new_p1, new_p2, cloneMySol(a1.formula,proofSize), cloneMySol(a2.formula,proofSize))
        }
        else proof
      }
      case ImpLeftRule(p1, p2, s, a1, a2, m) => {
        if(version == 0){
          apply(p1,name,rewriterules,proofSize,version)
          apply(p2,name,rewriterules,proofSize,version)
        }
        else if(version == 1){
          val new_p1 =  apply(p1,name,rewriterules,proofSize,version)
          val new_p2 =  apply(p2,name,rewriterules,proofSize,version)
          ImpLeftRule(new_p1, new_p2, a1.formula, a2.formula)
        }
        else if(version == 2){
          val new_p1 =  apply(p1,name,rewriterules,proofSize,version)
          val new_p2 =  apply(p2,name,rewriterules,proofSize,version)
          ImpLeftRule(new_p1, new_p2, cloneMySol(a1.formula,proofSize), cloneMySol(a2.formula,proofSize))
        }
        else proof
      }

      case NegLeftRule( p, _, a, m ) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          NegLeftRule( new_p, a.formula )
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          NegLeftRule( new_p, cloneMySol(a.formula,proofSize) )
        }
        else proof
      }

      case AndLeft1Rule(p, r, a, m) =>  {
        if(version == 0)  apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          val a2 = m.formula  match { case And(l, right) => right }
           AndLeft1Rule( new_p, a.formula, a2)
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          val a2 = m.formula  match { case And(l, right) => right }
          AndLeft1Rule( new_p, cloneMySol(a.formula,proofSize), cloneMySol(a2,proofSize))
        }
        else proof
      }

      case AndLeft2Rule(p, r, a, m) =>  {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          val a2 = m.formula  match { case And(l, _) => l }
          AndLeft2Rule( new_p, a2, a.formula )
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          val a2 = m.formula  match { case And(l, _) => l }
          AndLeft2Rule( new_p, cloneMySol(a2,proofSize), cloneMySol(a.formula,proofSize) )
        }
        else proof
      }

      case OrRight1Rule(p, r, a, m) =>  {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
           val a2 = m.formula  match { case Or(_, ra) => ra }
           OrRight1Rule( new_p, a.formula,a2)
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          val a2 = m.formula  match { case Or(_, ra) => ra }
          OrRight1Rule( new_p,cloneMySol(a.formula,proofSize),cloneMySol(a2,proofSize))
        }
        else proof
      }

      case OrRight2Rule(p, r, a, m) =>  {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
           val a2 = m.formula match { case Or(l, _) => l }
           OrRight2Rule( new_p, a2, a.formula)
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          val a2 = m.formula  match { case Or(l, _) => l }
          OrRight2Rule( new_p, cloneMySol(a2,proofSize), cloneMySol(a.formula,proofSize))
        }
        else proof
      }

      case NegRightRule( p, _, a, m ) => {
         if(version == 0)apply(p,name,rewriterules,proofSize,version)
         else if(version == 1){
            val new_p = apply(p,name,rewriterules,proofSize,version)
            NegRightRule( new_p, a.formula )
         }
         else if(version == 2){
           val new_p = apply(p,name,rewriterules,proofSize,version)
           NegRightRule( new_p, cloneMySol(a.formula,proofSize))
         }
         else proof
      }

      case ContractionLeftRule(p, _, a1, a2, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
           ContractionLeftRule( new_p, a1.formula)
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          ContractionLeftRule( new_p, cloneMySol(a1.formula,proofSize))
        }
        else proof
      }

      case ContractionRightRule(p, _, a1, a2, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
           ContractionRightRule( new_p, a1.formula)
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          ContractionRightRule( new_p, cloneMySol(a1.formula,proofSize))
        }
        else proof
      }

      case ForallLeftRule(p, seq, a, m, t) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          ForallLeftRule(new_p, a.formula, m.formula, t)
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          ForallLeftRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize), cloneMyTerm(t,proofSize))
        }
        else proof
      }
      case ForallRightRule(p, seq, a, m, v) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          ForallRightRule(new_p,a.formula, m.formula, v)
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          ForallRightRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize), cloneMyTerm(v,proofSize).asInstanceOf[HOLVar])
        }
        else proof
      }

      case ExistsRightRule(p, seq, a, m, t) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
            ExistsRightRule(new_p, a.formula, m.formula, t)
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          ExistsRightRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize), cloneMyTerm(t,proofSize))
        }
        else proof
      }
      case ExistsLeftRule(p, seq, a, m, v) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
           ExistsLeftRule(new_p, a.formula, m.formula, v)
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          ExistsLeftRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize), cloneMyTerm(v,proofSize).asInstanceOf[HOLVar])
        }
        else proof
      }

      case ExistsHyperRightRule(p, seq, a, m, t) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
           ExistsHyperRightRule(new_p, a.formula, m.formula, t)
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          ExistsHyperRightRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize), cloneMyTerm(t,proofSize))
        }
        else proof
      }
      case ExistsHyperLeftRule(p, seq, a, m, v) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
           ExistsHyperLeftRule(new_p, a.formula, m.formula, v)
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          ExistsHyperLeftRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize), cloneMyTerm(v,proofSize).asInstanceOf[HOLVar])
        }
        else proof
      }
      case ForallHyperLeftRule(p, seq, a, m, t) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
           ForallHyperLeftRule(new_p, a.formula, m.formula, t)
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          ForallHyperLeftRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize), cloneMyTerm(t,proofSize) )
        }
        else proof
      }
      case ForallHyperRightRule(p, seq, a, m, v) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
           ForallHyperRightRule(new_p, a.formula, m.formula, v)
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          ForallHyperRightRule(new_p, cloneMySol(a.formula,proofSize), cloneMySol(m.formula,proofSize), cloneMyTerm(v,proofSize).asInstanceOf[HOLVar] )
        }
        else proof
      }

      case ImpRightRule(p, s, a1, a2, m) => {
        if(version == 0)apply(p,name,rewriterules,proofSize,version)
        else if(version == 1){
          val new_p = apply(p,name,rewriterules,proofSize,version)
           ImpRightRule(new_p, a1.formula, a2.formula)
        }
        else if(version == 2){
          val new_p = apply(p,name,rewriterules,proofSize,version)
          ImpRightRule(new_p, cloneMySol(a1.formula,proofSize), cloneMySol(a2.formula,proofSize))
        }
        else proof
      }
      case FOSchemaProofLinkRule(s,name2,l) => {
        if(version == 0)proof
        else if(version == 1){
          val next = backToInt(l.head)
          if(next == 0) CloneLKProof2(SchemaProofDB.get(name2).base,name2,rewriterules,0,version)
          else applySchemaSubstitution2(name2,next)
        }
        else if(version == 2) FOSchemaProofLinkRule(
          new FSequent(s.antecedent.map( x => cloneMySol(x.formula,proofSize)),
                      s.succedent.map(x => cloneMySol(x.formula,proofSize))),name2,l.map(x => cloneMyTerm(x,proofSize)))
        else proof
      }
      case _ => throw new Exception("ERROR in unfolding: CloneLKProof2: missing rule !\n" + proof.rule + "\n")
    }}

}

object cloneMySol{
  import at.logic.language.hol._
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
}

object cloneMyTerm{
  import at.logic.language.hol._
  def apply(term:HOLExpression , proofSize:Int):HOLExpression = {
    term match {
      case Function(ConstantStringSymbol(n),l,t) if n =="schS" && t == ind => Function(ConstantStringSymbol(n),l.map(x => apply(x,proofSize)),t)
      case HOLVar(VariableStringSymbol(n),t) if n== "k" && t == ind =>  maketogether(proofSize)
      case Function(ConstantStringSymbol(n),l,t) if t == ind => Function(ConstantStringSymbol(n),l.map(x => apply(x,proofSize)),t)
      case Function(ConstantStringSymbol(n),l,t) if t == i => Function(ConstantStringSymbol(n),l.map(x => apply(x,proofSize)),t)
      case HOLVar(n,t) if t == i | t == ind->i =>         HOLVar(n,t)
      case HOLConst(n,t)  => HOLConst(n,t)
      case HOLAbs(x, t)   => HOLAbs(x, apply(t,proofSize))
      case _ => throw new Exception("ERROR in unfolding missing formula !\n" + term.toString + "\n")

    }
  }
}








