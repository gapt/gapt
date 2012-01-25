
package at.logic.transformations.ceres.unfolding

import at.logic.parsing.language.simple.SHLK
import at.logic.transformations.ceres.unfolding.{applySchemaSubstitution, SchemaSubstitution1}
import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher
//import scala.xml.dtd._

import at.logic.algorithms.lk.{getAncestors, getCutAncestors}
//import scala.xml._
//import at.logic.language.hol._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base.Sequent
import at.logic.transformations.ceres.struct._
import at.logic.language.schema.{IntVar, IntZero, IndexedPredicate, SchemaFormula, Succ, BigAnd, BigOr}
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.slk._
import at.logic.transformations.ceres.clauseSets.StandardClauseSet
import at.logic.calculi.lk.base.types.FSequent
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.{Or => HOLOr, Neg => HOLNeg, And => HOLAnd, _}
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.calculi.lksk.{Axiom => LKskAxiom,
WeakeningLeftRule => LKskWeakeningLeftRule,
WeakeningRightRule => LKskWeakeningRightRule,
ForallSkLeftRule, ForallSkRightRule, ExistsSkLeftRule, ExistsSkRightRule}
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.definitionRules._
import scala.collection.immutable.Seq
import at.logic.parsing.readers.StringReader
import java.io.File.separator
import scala.io._

class UnfoldSchemaProofTest extends SpecificationWithJUnit {
    implicit val factory = defaultFormulaOccurrenceFactory
    import at.logic.language.schema._
    "UnfoldSchemaProofTest" should {
        "unfold the adder.slk" in {
                  /*
             val a = HOLVarFormula( "a" )
             val b = HOLVarFormula( "b" )
             val c = HOLVarFormula( "c" )
             val d = HOLVarFormula( "d" )

             val k = IntVar(new VariableStringSymbol("k"))
             val real_n = IntVar(new VariableStringSymbol("n"))
             val n = k
             val n1 = Succ(k); val n2 = Succ(n1); val n3 = Succ(n2)
             val k1 = Succ(k); val k2 = Succ(n1); val k3 = Succ(n2)
             val s = Set[FormulaOccurrence]()

             val i = IntVar(new VariableStringSymbol("i"))
             val A = IndexedPredicate(new ConstantStringSymbol("A"), i)
             val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
             val four = Succ(three);val five = Succ(four); val six = Succ(Succ(four));val seven = Succ(Succ(five));
             val A0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero())
             val A1 = IndexedPredicate(new ConstantStringSymbol("A"), one)
             val A2 = IndexedPredicate(new ConstantStringSymbol("A"), two)
             val A3 = IndexedPredicate(new ConstantStringSymbol("A"), three)

             val B0 = IndexedPredicate(new ConstantStringSymbol("B"), IntZero())

             val Ak = IndexedPredicate(new ConstantStringSymbol("A"), k)
             val Ai = IndexedPredicate(new ConstantStringSymbol("A"), i)
             val Ai1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(i))

             val orneg = at.logic.language.schema.Or(at.logic.language.schema.Neg(Ai).asInstanceOf[SchemaFormula], Ai1.asInstanceOf[SchemaFormula]).asInstanceOf[SchemaFormula]

             val Ak1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(k))
             val An = IndexedPredicate(new ConstantStringSymbol("A"), k)
             val An1 = IndexedPredicate(new ConstantStringSymbol("A"), n1)
             val An2 = IndexedPredicate(new ConstantStringSymbol("A"), n2)
             val An3 = IndexedPredicate(new ConstantStringSymbol("A"), n3)
//             println("\n\n START \n\n")

             val ax1 = Axiom(A0 +: Seq.empty[HOLFormula], A0 +: Seq.empty[HOLFormula])
             val negl1 = NegLeftRule(ax1,A0)
                      val ax2 = Axiom(A1 +: Seq.empty[HOLFormula], A1 +: Seq.empty[HOLFormula])
                 val orl1 = OrLeftRule(negl1, ax2, at.logic.language.schema.Neg(A0), A1)
                 val negl2 = NegLeftRule(orl1,A1)
                              val ax3 = Axiom(A2 +: Seq.empty[HOLFormula], A2 +: Seq.empty[HOLFormula])
                        val orl2 = OrLeftRule(negl2, ax3, at.logic.language.schema.Neg(A1), A2)

                                                                                         val ax4 = Axiom(A0 +: Seq.empty[HOLFormula], A0 +: Seq.empty[HOLFormula])
                                                                                         val negl3 = NegLeftRule(ax4,A0)
                                                                                                   val ax5 = Axiom(A1 +: Seq.empty[HOLFormula], A1 +: Seq.empty[HOLFormula])
                                                                                              val orl3 = OrLeftRule(negl3, ax5, at.logic.language.schema.Neg(A0), A1)
                                                                                   val ax6 = Axiom(A0 +: Seq.empty[HOLFormula], A0 +: Seq.empty[HOLFormula])
                                                                                   val andEqR1 = AndRightEquivalenceRule3(ax6,A0, BigAnd(i,Ai,zero,zero))
                                                                                           val andr22 = AndRightRule(andEqR1, orl3, BigAnd(i,Ai,zero,zero), A1)
                                                                                           val andEqR2 = AndRightEquivalenceRule1(andr22, And(BigAnd(i,Ai,zero,zero), A1).asInstanceOf[SchemaFormula], BigAnd(i,A,zero,one))
                                                                                           val contrl1 = ContractionLeftRule(andEqR2, A0)
                                                         val andr2 = AndRightRule(orl2, contrl1, A2, BigAnd(i,A,zero,one))
                                                         val andr3 = AndRightEquivalenceRule1(andr2, And(A2, BigAnd(i,A,zero,one)).asInstanceOf[SchemaFormula], BigAnd(i,A,zero,two))
                                                         val contrl2 = ContractionLeftRule(andr3, A0)
                                                         val contrl3 = ContractionLeftRule(contrl2, at.logic.language.schema.Or(at.logic.language.schema.Neg(A0),A1))
                                                         val andleq3 = AndLeftEquivalenceRule3(contrl3, Or(Neg(A0),A1).asInstanceOf[SchemaFormula], BigAnd(i, Or(Neg(Ai),Ai1).asInstanceOf[SchemaFormula], zero, zero).asInstanceOf[SchemaFormula])
                                                         val andlb = AndLeftRule(andleq3, Or(Neg(A1),A2).asInstanceOf[SchemaFormula], BigAnd(i, Or(Neg(Ai),Ai1).asInstanceOf[SchemaFormula], zero, zero).asInstanceOf[SchemaFormula])
                                                         val base = AndLeftEquivalenceRule1(andlb, And(Or(Neg(A1),A2).asInstanceOf[SchemaFormula], BigAnd(i, Or(Neg(Ai),Ai1).asInstanceOf[SchemaFormula], zero, zero).asInstanceOf[SchemaFormula]), BigAnd(i, Or(Neg(Ai),Ai1).asInstanceOf[SchemaFormula], zero, one).asInstanceOf[SchemaFormula])
                                                   //      Main.display("base", base) ; while(true) {}


//--------------------------------------------------
import at.logic.transformations.ceres.projections.printSchemaProof

val chi0a = Axiom(A0 +: Seq.empty[HOLFormula], A0 +: Seq.empty[HOLFormula])
val eqq1 = AndLeftEquivalenceRule3(chi0a, A0, BigAnd(i,A,zero,zero))
val eqq2 = AndRightEquivalenceRule3(eqq1, A0, BigAnd(i,A,zero,zero))
            val axxx =  Axiom(A1 +: Seq.empty[HOLFormula], A1 +: Seq.empty[HOLFormula])
      val andddr = AndRightRule(eqq2, axxx, BigAnd(i,A,zero,zero), A1)
      val eqrrrr = AndRightEquivalenceRule1(andddr, And(BigAnd(i,A,zero,zero), A1), BigAnd(i,A,zero,one))
      val andll1 = AndLeftRule(eqrrrr, BigAnd(i,A,zero,zero), A1)
      val eqqqq11= AndLeftEquivalenceRule1(andll1, And(BigAnd(i,A,zero,zero), A1), BigAnd(i,A,zero,one))
      val chi0 = eqqqq11



val prh = SchemaProofLinkRule(Pair(BigAnd(i,A,zero,k) +: Seq.empty[HOLFormula], BigAnd(i,A,zero,k) +: Seq.empty[HOLFormula]), "\\chi", k)
            val ax8 = Axiom(An1 +: Seq.empty[HOLFormula], An1 +: Seq.empty[HOLFormula])
     val andr6 = AndRightRule(prh, ax8, BigAnd(i,A,zero,n), An1)
     val eq44 = AndRightEquivalenceRule1(andr6, And(BigAnd(i,A,zero,n).asInstanceOf[SchemaFormula], An1).asInstanceOf[SchemaFormula], BigAnd(i,A,zero,n1).asInstanceOf[SchemaFormula])
     val andlc = AndLeftRule(eq44, BigAnd(i,A,zero,n), An1)
     val chin = AndLeftEquivalenceRule1(andlc, And(BigAnd(i,A,zero,n), An1), BigAnd(i,A,zero,n1))

  val end = chin

//  val f = end.root.succedent.toList.head//.formula.asInstanceOf[SchemaFormula]
 // val f = end.root.antecedent.toList.head


 // getAncestors( f ).foreach(fo => println(formulaToString(fo.formula)))

 // Main.display("Proof", end)

    SchemaProofDB.clear
//    val chi = new SchemaProof( "\\chi", n::Nil, Pair(BigAnd(i,A,zero,n) +: Seq.empty[HOLFormula], BigAnd(i,A,zero,n) +: Seq.empty[HOLFormula]), chi0, chin )
//    SchemaProofDB.put( chi )
//    val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(n, one)
//    val subst = new SchemaSubstitution1[HOLExpression](new_map)
//    val chi1 = applySchemaSubstitution(chi, subst)
 //   Main.display("chi", chi1) ; while(true){}

  //  println("\n\n\n\n -------- SUBSTITUTION applied: --------\n\n")

 // val chi = chin
 //   val chi = applySchemaSubstitution(chin, subst)
 //  val projs = Projections(end, s+f).toList
 // projs.foreach(p => { println("\nNext projection:\n");printSchemaProof( p._1 ) } )
//  Main.display("Projection", projs.head._1);while(true) {}
//  Main.display("Projection", projs.tail.head._1)

 //   Main.display("proof", chi) ; while(true){}



//--------------------------------------------------

val pl2 = SchemaProofLinkRule(Pair(A0 +: BigAnd(i,orneg,zero,n) +: Seq.empty[HOLFormula], BigAnd(i,A,zero,n1) +: Seq.empty[HOLFormula] ), "\\psi", k)
val wl2 = WeakeningLeftRule(pl2, Neg(An1))
            val pl3 = SchemaProofLinkRule(Pair(A0 +: BigAnd(i,orneg,zero,n) +: Seq.empty[HOLFormula] , BigAnd(i,A,zero,n1) +: Seq.empty[HOLFormula]), "\\psi", k)
            val wl3 = WeakeningLeftRule(pl3, An2)
     val orl5 = OrLeftRule(wl2, wl3, Neg(An1), An2)
     val cont1l = ContractionLeftRule(orl5, A0)
     val cont2l = ContractionLeftRule(cont1l, BigAnd(i,orneg,zero,n))
     val pr2 = ContractionRightRule(cont2l, BigAnd(i,A,zero,n1))

//-------------------------------------------------

val pl1 = SchemaProofLinkRule(Pair(A0 +: BigAnd(i,orneg,zero,n) +: Seq.empty[HOLFormula], BigAnd(i,A,zero,n1) +: Seq.empty[HOLFormula] ), "\\psi", n)
            val ax66 = Axiom(An1::Nil, An1::Nil)
            val wl1 = WeakeningLeftRule(ax66, BigAnd(i,A,zero,n))
            val andl222 = AndLeftRule(wl1, An1, BigAnd(i,A,zero,n))
            val eq4 = AndLeftEquivalenceRule1(andl222, And(An1, BigAnd(i,A,zero,n)), BigAnd(i,A,zero,n1))
     val cut1 = CutRule(pl1, eq4, BigAnd(i,A,zero,n1))
     val neg4l = NegLeftRule(cut1, An1)
                       val ax7 = Axiom(An2::Nil, An2::Nil)
            val pr3 = OrLeftRule(neg4l, ax7, Neg(An1), An2)


//--------------------------------------------------

val andr5 = AndRightRule(pr2, pr3, BigAnd(i,A,zero,n1), An2)
val equiv = AndRightEquivalenceRule1(andr5, And(BigAnd(i,Ai,zero,n1), An2), BigAnd(i,Ai,zero,n2))
val contr5 = ContractionLeftRule(equiv, A0)
val contr55 = ContractionLeftRule(contr5, BigAnd(i,orneg,zero,n))
val contr555 = ContractionLeftRule(contr55, Or(Neg(An1).asInstanceOf[SchemaFormula], An2).asInstanceOf[SchemaFormula])
val andl555 = AndLeftRule(contr555, BigAnd(i,orneg,zero,n), Or(Neg(An1).asInstanceOf[SchemaFormula], An2).asInstanceOf[SchemaFormula])
val eq33 = AndLeftEquivalenceRule1(andl555, And(BigAnd(i,orneg,zero,n), Or(Neg(An1), An2)), BigAnd(i,orneg,zero,n1))
val negr33 = NegRightRule(eq33, A0)
val pl13 = OrRightRule(negr33, Neg(A0), BigAnd(i,A,zero,n2))


//--------------------------------------------------

                    val ax10 = Axiom(A0 +: Seq.empty[HOLFormula], A0 +: Seq.empty[HOLFormula])
                    val nl6 = NegLeftRule(ax10, A0)
                                         //   val hacked = Axiom(BigAnd(i,A,zero,n2)::Nil, BigAnd(i,A,zero,n2)::Nil)
                                             val khin3 = SchemaProofLinkRule(Pair(BigAnd(i,A,zero,n2) +: Seq.empty[HOLFormula] , BigAnd(i,A,zero,n2) +: Seq.empty[HOLFormula] ), "\\chi", Succ(Succ(n)))

                                 val orl10 = OrLeftRule(nl6, khin3, Neg(A0), BigAnd(i,A,zero,n2))
                         val step = CutRule(pl13, orl10, Or(Neg(A0).asInstanceOf[SchemaFormula], BigAnd(i,A,zero,n2).asInstanceOf[SchemaFormula]))
                */



//            val psi = new SchemaProof( "\\psi", n::Nil, Pair(A0 +: BigAnd(i, orneg, zero, n1) +: Seq.empty[HOLFormula], BigAnd(i,A,zero,n2) +: Seq.empty[HOLFormula]), base, step )
//            SchemaProofDB.put( psi )

     //        printSchemaProof( step )


//         val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(n, one)
//         val subst = new SchemaSubstitution1[HOLExpression](new_map)
//         val psi1 = applySchemaSubstitution(psi, subst)
    //     Main.display("psi1", applySchemaSubstitution(psi, subst)) ; while(true) {}
   //     saveXML( ("psi1", psi1)::Nil, List(), "ceco.xml" )



   //      printSchemaProof(base)
       //  Main.display("base", base) ; while(true) {}

    //     while(true) {}
//           println("\n\n PROJECTIONS \n\n")

//        val cs = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet( StructCreators.extract(psi1) ) ) )
//        cs.foreach(s => println(printSchemaProof.sequentToString(s)+"\n"))

   //    val cs = StandardClauseSet.transformStructToClauseSet( StructCreators.extractStruct( "\\chi", real_n ) )


   //      val step1 = applySchemaSubstitution(step, subst)  ;

       //  Main.display("Proof", cs)         ;while(true) {}



      //     val f = step.root.succedent.toList.head
//         val projs = Projections(step, s).toList

          val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
          println("\n\nunfolding TEST ")
          val str = Source.fromFile("target" + separator + "test-classes" + separator + "adder.lks").toList.foldLeft("")((ch,res) => ch + res)
          val map = SHLK.parseProof(str)
          val n = IntVar(new VariableStringSymbol("n"));val n1 = Succ(n);val n2 = Succ(n1);val n3 = Succ(n2);
          val k = IntVar(new VariableStringSymbol("k")) ; val i = IntVar(new VariableStringSymbol("i"))
          val A3 = IndexedPredicate(new ConstantStringSymbol("A"), three)
          val A = IndexedPredicate(new ConstantStringSymbol("A"), i)
          val An3 = IndexedPredicate(new ConstantStringSymbol("A"), n3)
          val An1 = IndexedPredicate(new ConstantStringSymbol("A"), n1)
          val b = BigAnd(i, A, zero, n3)
          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(k, two)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)

//          StepMinusOne(map.get("phi").get._2.get("root").get, k)

//          println("-1 = "+StepMinusOne.minusOne(Or(And(An3, An1), b) , n))

          val phi1 = applySchemaSubstitution(map.get("psi").get._2.get("root").get, subst, 3)

//           CloneLKProof(map.get("phi").get._1.get("root").get)

//          checkProofLinks1(map.get("phi").get._2.get("root").get)
//          checkProofLinks1(map.get("varphi").get._2.get("root").get)
//          checkProofLinks1(map.get("psi").get._2.get("root").get)
//          checkProofLinks1(map.get("chi").get._2.get("root").get)



//         projs.foreach(p => { println("\nNext projection:\n");printSchemaProof( p._1 )})
      //     Main.display("Projection", projs.tail.head._1); while(true) {}





        }
    }

 }

