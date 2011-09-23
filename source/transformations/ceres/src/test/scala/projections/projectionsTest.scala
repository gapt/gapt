
package at.logic.transformations.ceres.projections

import at.logic.transformations.ceres.unfolding.{applySchemaSubstitution, SchemaSubstitution1}
import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher
import scala.xml.dtd._

import at.logic.algorithms.lk.{getAncestors, getCutAncestors}
import scala.xml._
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


 /*
// -------- prooftool begin----------------------------------------------------------------------

    import scala.swing._
    import BorderPanel._
    import java.awt.Font._
    import java.awt.{RenderingHints, BasicStroke}
    import at.logic.calculi.treeProofs._
  //  import at.logic.calculi.slk.SchemaProofLinkRule

//    import at.logic.calculi.lk.base.Sequent
//    import at.logic.calculi.proofs.{BinaryProof, UnaryProof, Proof, RuleTypeA}
   import ProoftoolSequentFormatter._

    class DrawProof(private val proof: TreeProof[_], private val fSize: Int) extends BorderPanel {
      val white = new Color(255,255,255)
      background = white
      opaque = false
      val bd = Swing.EmptyBorder(0,fSize*3,0,fSize*3)
      val ft = new Font(SANS_SERIF, PLAIN, fSize)
      val labelFont = new Font(MONOSPACED, ITALIC, fSize-2)
      private val tx = proof.root match {
        case so: Sequent => sequentToString(so)
        case _ => proof.root.toString
      }

      proof match {

        case p: UnaryTreeProof[_] =>
          border = bd
          layout(new DrawProof(p.uProof.asInstanceOf[TreeProof[_]], fSize)) = Position.Center
        /*  if (! (p.rule == ContractionLeftRuleType ||
                 p.rule == ContractionRightRuleType ||
                 p.rule == AndEquivalenceRule1Type  ||
                 p.rule == AndEquivalenceRule12Type  ||
                 p.rule == AndEquivalenceRule2Type  ||
                 p.rule == AndEquivalenceRule3Type  ||
                 p.rule == OrEquivalenceRule1Type  ||
                 p.rule == OrEquivalenceRule2Type  ||
                 p.rule == OrEquivalenceRule3Type ))   */
            layout(new Label(tx) { font = ft }) = Position.South
        case p: BinaryTreeProof[_] =>
          border = bd
          layout(new DrawProof(p.uProof1.asInstanceOf[TreeProof[_]], fSize)) = Position.West
          layout(new DrawProof(p.uProof2.asInstanceOf[TreeProof[_]], fSize)) = Position.East
          layout(new Label(tx) { font = ft }) = Position.South
        case p: NullaryTreeProof[_] => p match {
            case Axiom(_) =>
                layout(new Label(tx) {
                border = Swing.EmptyBorder(0,fSize,0,fSize)
                    font = ft
                }) = Position.South
            case SchemaProofLinkRule(_, link, indices) =>
              layout(new BoxPanel(Orientation.Vertical) {
 	          background = white
 	          contents += new Label("(" + link + ", " + formulaToString(indices.head) + ")") {
 	            font = ft
 	            xLayoutAlignment = 0.5
 	          }
 	          contents += new Label(tx) {
 	            font = ft
 	            xLayoutAlignment = 0.5
 	          }
 	        }) = Position.South
        }
      }

      override def paintComponent(g: Graphics2D) = {
        import scala.math.max

        super.paintComponent(g)

        val metrics = g.getFontMetrics(ft)
        val lineHeight = metrics.getHeight

        g.setFont(labelFont)
        // g.setStroke(new BasicStroke(fSize / 25))
        g.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING,RenderingHints.VALUE_TEXT_ANTIALIAS_LCD_HRGB)

        proof match {
          case p: UnaryTreeProof[_] => {
            val center = this.layout.find(x => x._2 == Position.Center).get._1
            val width = center.size.width + fSize*6
            val height = center.size.height
            val seqLength = p.root match {
              case so: Sequent  =>
                max(metrics.stringWidth(sequentToString(p.uProof.root.asInstanceOf[Sequent])),
                  metrics.stringWidth(sequentToString(so)))
              case _ =>
                max(metrics.stringWidth(p.uProof.root.toString),
                  metrics.stringWidth(p.root.toString))
            }       /*
             if (! (p.rule == ContractionLeftRuleType ||
                 p.rule == ContractionRightRuleType ||
                 p.rule == AndEquivalenceRule1Type  ||
                 p.rule == AndEquivalenceRule12Type  ||
                 p.rule == AndEquivalenceRule2Type  ||
                 p.rule == AndEquivalenceRule3Type  ||
                 p.rule == OrEquivalenceRule1Type  ||
                 p.rule == OrEquivalenceRule2Type  ||
                 p.rule == OrEquivalenceRule3Type )) */{
            g.drawLine((width - seqLength) / 2, height, (width + seqLength) / 2, height)
            g.drawString(p.name, (fSize / 4 + width + seqLength) / 2, height + metrics.getMaxDescent)
            }
          }
          case p: BinaryTreeProof[_] => {
            val left = this.layout.find(x => x._2 == Position.West).get._1
            val leftWidth = left.size.width + fSize*6
            val right = this.layout.find(x => x._2 == Position.East).get._1
            val rightWidth = right.size.width
            val height = max(left.size.height, right.size.height)
            val leftSeqLength = p.uProof1.root match {
              case so: Sequent => metrics.stringWidth(sequentToString(so))
              case _ =>  metrics.stringWidth(p.uProof1.root.toString)
            }
            val rightSeqLength = p.uProof2.root match {
              case so: Sequent => metrics.stringWidth(sequentToString(so))
              case _ =>  metrics.stringWidth(p.uProof2.root.toString)
            }

            val lineLength = right.location.x + (rightWidth + rightSeqLength) / 2

            g.drawLine((leftWidth - leftSeqLength) / 2, height, lineLength, height)
            g.drawString(p.name, lineLength + fSize / 4, height + metrics.getMaxDescent)
          }
          case _ =>
        }
      }
}


import at.logic.calculi.lk.base.Sequent
import at.logic.language.lambda.types.{To, ->, Ti}
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.schema._
//import at.logic.language.fol._
//import at.logic.language.hol._
//import at.logic.language.hol.logicSymbols._

object ProoftoolSequentFormatter {
 //formats a lambda term to a readable string, distinguishing function and logical symbols
  def formulaToString(f:LambdaExpression) : String = f match {
    case BigAnd(v, formula, init, end) =>
 	        "⋀" + formulaToString(v) + "=(" + formulaToString(init) + ".." + formulaToString(end) + ")(" + formulaToString(formula) + ")"

    case BigOr(v, formula, init, end) =>
 	        "⋁" + formulaToString(v) + "=(" + formulaToString(init) + ".." + formulaToString(end) + ")(" + formulaToString(formula) + ")"

    case t : IntegerTerm  => parseIntegerTerm(t, 0)
    case App(x,y) => x match {
      case App(Var(name,tp),z) =>
        if (name.toString.matches("""[\w\p{InGreek}]*""")) name.toString+"("+formulaToString(z)+","+formulaToString(y)+")"
        else "("+formulaToString(z)+" "+name.toString()+" "+formulaToString(y)+")"
      case Var(name,tp) => tp match {
        case ->(To(), To()) => name.toString+formulaToString(y)
        case _ => y match {
          case Abs(x1,y1) => "("+name.toString+formulaToString(x1)+")"+formulaToString(y1)
          case _ => name.toString()+"("+formulaToString(y)+")"
        }
      }
      case _ => formulaToString(x) +"("+ formulaToString(y) +")"
    }
    case Var(name,t) => name.toString()
    case Abs(x,y) => formulaToString(y)
    case  x : Any    => "(unmatched class: "+x.getClass() + ")"
  }

  def parseIntegerTerm( t: IntegerTerm, n: Int) : String = t match {
 	    // FIXME: in the first case, we implicitely assume
 	    // that all IntConsts are 0!
 	    // this is just done for convenience, and should be changed ASAP
 	    case z : IntConst => n.toString
 	    case IntZero() => n.toString

 	    case v : IntVar => if (n > 0)
 	        v.toStringSimple + "+" + n.toString
 	      else
 	        v.toStringSimple
 	    case Succ(t) => parseIntegerTerm( t, n + 1 )
  }
 /*
  def formulaToString(f:SchemaExpression) : String = f match {
    case AppN(BigAndC, SchemaAbs(i, formula)::lower::upper::Nil) => BigAndC.name + "<sub>" + formulaToString(i) + " = " + formulaToString(lower) + "</sub>" +
      "<sup>" + formulaToString(upper) + "</sup>" + formulaToString(formula)
    case AppN(BigOrC, SchemaAbs(i, formula)::lower::upper::Nil) => BigAndC.name + "<sub>" + formulaToString(i) + " = " + formulaToString(lower) + "</sub>" +
      "<sup>" + formulaToString(upper) + "</sup>" + formulaToString(formula)
    case AppN(pred, indexTerms) => formulaToString(pred)+"<sub>"+indexTerms.map( x => formulaToString(x)).mkString+"</sub>"
  }*/

  // formats a sequent to a readable string
  def sequentToString(s : Sequent) : String = {
    var sb = new scala.StringBuilder()
    var first = true
    for (f <- s.antecedent) {
      if (! first) sb.append(", ")
      else first = false
      sb.append(formulaToString(f.formula))
    }
    sb.append(" \u22a2 ")
    first =true
    for (f <- s.succedent) {
      if (! first) sb.append(", ")
      else first = false
      sb.append(formulaToString(f.formula))
    }
    sb.toString
  }

//  def sequentOccurenceToString(s: SequentOccurrence) : String = sequentToString(s.getSequent)
}

import scala.swing._
import java.awt.Font._
import javax.swing.border.TitledBorder
import at.logic.calculi.lk.base.Sequent
//import at.logic.gui.prooftool.parser.{UnLoaded, Loaded, ProofToolPublisher, StructPublisher}
import at.logic.utils.ds.trees.Tree
import at.logic.calculi.treeProofs.TreeProof
import at.logic.language.hol.HOLExpression

class MyScrollPane extends ScrollPane {
  background = new Color(255,255,255)

  def getContent: Launcher = contents.last.asInstanceOf[Launcher]
}

class Launcher(private val option: Option[(String, AnyRef)], private val fSize: Int) extends GridBagPanel {
  option match {
    case Some((name: String, obj: AnyRef)) =>
      val c = new Constraints
      c.grid = (0,0)
      c.insets.set(15, 15, 15, 15)
      obj match {
        case proof: TreeProof[_] =>
          layout(new DrawProof(proof, fSize)) = c
//          ProofToolPublisher.publish(Loaded)
      //    StructPublisher.publish(UnLoaded)
           /*
        case tree: Tree[_] =>
          layout(new DrawTree(tree, fSize)) = c
          ProofToolPublisher.publish(UnLoaded)
          StructPublisher.publish(Loaded)
        case clList: List[Sequent] =>
          layout(new DrawClList(clList, fSize)) = c
          ProofToolPublisher.publish(UnLoaded)
          StructPublisher.publish(UnLoaded)   */
        case _ =>
          layout(new Label("Can't match case: "+option.get._2.getClass.toString)) = c
        //  ProofToolPublisher.publish(UnLoaded)
        //  StructPublisher.publish(UnLoaded)
      }
      val bd: TitledBorder = Swing.TitledBorder(Swing.LineBorder(new Color(0,0,0), 2), " "+name+" ")
      bd.setTitleFont(new Font(SANS_SERIF, BOLD, 16))
      border = bd
    case _ =>
  }

  background = new Color(255,255,255)

  def fontSize = fSize
  def getData = option
}

import BorderPanel._

object Main extends SimpleSwingApplication {
  override def startup(args: Array[String]) = {
    showFrame
//    if (args.length >= 1) loadProof(args(0),12)
  }

  def showFrame: Unit = {
    val t = top
    t.pack
    t.location = new Point(100,50)
    t.size = new Dimension(700,500)
    t.visible = true
  }

  // Used for displaying things directly from Scala shell
  def display(name: String, obj: AnyRef): Unit = {
    showFrame
    body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    body.contents = new Launcher(Some(name, obj), 29)
    body.cursor = java.awt.Cursor.getDefaultCursor
  }
  def top = new MainFrame {
    title = "ProofTool"
   // menuBar = mBar
    contents = new BorderPanel {
     // layout(toolbar) = Position.North
      layout(body) = Position.Center
    }
  }
 val body = new MyScrollPane
 }



   */
// prooftool end----------------------------------------------------------------------


      /*

// --------------------- substitution begin

object applySchemaSubstitution {


import  at.logic.transformations.ceres.projections.printSchemaProof
import scala.collection.mutable.{Map, HashMap}

import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.language.hol.{HOLFormula}
//import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression, Var}
import at.logic.language.schema._
import at.logic.language.schema.IntegerTerm
//import at.logic.language.schema.SchemaSubstitution


  def handleSchemaEquivalenceRule ( new_parent: (LKProof, Map[FormulaOccurrence, FormulaOccurrence]),
                                    subst: SchemaSubstitution1[HOLExpression],
                                    old_parent: LKProof,
                                    old_proof: LKProof,
                                    constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas,
                                    m: FormulaOccurrence
                                    ) = {
      val new_proof = constructor( new_parent._1, subst(m.formula).asInstanceOf[HOLFormula])
      ( new_proof, computeMap( old_parent.root.antecedent ++ old_parent.root.succedent, old_proof, new_proof, new_parent._2 ) )
  }




  // TODO: finish refactoring rules like this! there is still redundancy in handleRule!
  def handleWeakening( new_parent: (LKProof, Map[FormulaOccurrence, FormulaOccurrence]),
                       subst: SchemaSubstitution1[HOLExpression],
                       old_parent: LKProof,
                       old_proof: LKProof,
                       constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas,
                       m: FormulaOccurrence ) = {
     val new_proof = constructor( new_parent._1, subst(m.formula).asInstanceOf[HOLFormula] )
    ( new_proof, computeMap( old_parent.root.antecedent ++ old_parent.root.succedent, old_proof, new_proof, new_parent._2 ) + Pair(m, new_proof.prin.head ) )
  }
  def handleContraction( new_parent: (LKProof, Map[FormulaOccurrence, FormulaOccurrence]),
                         subst: SchemaSubstitution1[HOLExpression],
                         old_parent: LKProof,
                         old_proof: LKProof,
                         a1: FormulaOccurrence,
                         a2: FormulaOccurrence,
                        constructor: (LKProof, HOLFormula) => LKProof) = {
 //   println("n = "+subst.map.toList.head._2)
 //   println("handleContraction \n\n1"+printSchemaProof.sequentToString(new_parent._1.root))
 //   println("2\n\n"+printSchemaProof.formulaToString(subst(a1.formula)))

 //   println("3\n\n"+printSchemaProof.sequentToString(old_parent.root))
  //  println("4\n\n"+printSchemaProof.formulaToString(a1.formula))

//    println("4\n\n"+printSchemaProof.sequentToString(old_proof.root))


    (constructor( new_parent._1, subst(a1.formula).asInstanceOf[HOLFormula] ), new HashMap[FormulaOccurrence, FormulaOccurrence])
//    ( new_proof, computeMap( old_parent.root.antecedent ++ old_parent.root.succedent, old_proof, new_proof, new_parent._2 ) )
  }
  def handleBinaryProp( new_parent_1: (LKProof, Map[FormulaOccurrence, FormulaOccurrence]),
                        new_parent_2: (LKProof, Map[FormulaOccurrence, FormulaOccurrence]),
                        subst: SchemaSubstitution1[HOLExpression],
                        a1: FormulaOccurrence,
                        a2: FormulaOccurrence,
                        old_parent_1: LKProof,
                        old_parent_2: LKProof,
                        old_proof: LKProof,
                        constructor: (LKProof, LKProof, HOLFormula, HOLFormula) => LKProof) = {

     (constructor( new_parent_1._1, new_parent_2._1, subst(a1.formula).asInstanceOf[HOLFormula], subst(a2.formula).asInstanceOf[HOLFormula] ), new HashMap[FormulaOccurrence, FormulaOccurrence])


  }



  def handleRule( proof: LKProof, new_parents: List[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])],
                  subst: SchemaSubstitution1[HOLExpression] ) : (LKProof, Map[FormulaOccurrence, FormulaOccurrence]) = {
    implicit val factory = defaultFormulaOccurrenceFactory
    proof match {

      case Axiom(ro) => {
        val a = Axiom(ro.antecedent.map(fo => subst(fo.formula).asInstanceOf[HOLFormula]),ro.succedent.toList.map(fo => subst(fo.formula).asInstanceOf[HOLFormula]))
//        val ant_occs = a._1.root.antecedent.toList
//        val succ_occs = a._1.root.succedent.toList
        val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
//        a._2._1.zip(a._2._1.indices).foreach( p => map.update( ant_occs( p._2 ), p._1 ) )
//        a._2._2.zip(a._2._2.indices).foreach( p => map.update( succ_occs( p._2 ), p._1 ) )
        (a, map)
      }
      case WeakeningLeftRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningLeftRule.apply, m )
      case WeakeningRightRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningRightRule.apply, m )
      case ContractionLeftRule(p, s, a1, a2, m) => handleContraction( new_parents.head, subst, p, proof, a1, a2, ContractionLeftRule.apply )
      case ContractionRightRule(p, s, a1, a2, m) => handleContraction( new_parents.head, subst, p, proof, a1, a2, ContractionRightRule.apply )
      case CutRule(p1, p2, s, a1, a2) => {
        val new_p1 = new_parents.head
        val new_p2 = new_parents.last
        val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
        //val new_proof = CutRule( new_p1._1, new_p2._1, new_p1._2( a1 ), new_p2._2( a2 ) )
        val new_proof = CutRule( new_p1._1, new_p2._1, subst( a1.formula ).asInstanceOf[HOLFormula] )
    //    ( new_proof, computeMap(
     //     p1.root.antecedent ++ (p1.root.succedent - a1) ++ (p2.root.antecedent - a2) ++ p2.root.succedent,
      //    proof, new_proof, new_p1._2 ++ new_p2._2 ) )
        (new_proof, map)
      }
      case AndRightRule(p1, p2, s, a1, a2, m) => handleBinaryProp( new_parents.head, new_parents.last, subst, a1, a2, p1, p2, proof, AndRightRule.apply )

      case AndLeft1Rule(p, s, a, m) => {
        val f = m.formula match { case And(_, w) => w }
        val new_parent = new_parents.head
//        val new_proof = AndLeft1Rule( new_parent._1, new_parent._2( a ), subst( f ).asInstanceOf[HOLFormula] )
        val new_proof = AndLeft1Rule( new_parent._1, subst(a.formula).asInstanceOf[HOLFormula], subst( f ).asInstanceOf[HOLFormula] )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case AndLeft2Rule(p, s, a, m) => {
        val f = m.formula match { case And(w, _) => w }
        val new_parent = new_parents.head
//        val new_proof = AndLeft2Rule( new_parent._1, subst( f ).asInstanceOf[HOLFormula], new_parent._2( a ) )
        val new_proof = AndLeft2Rule( new_parent._1, subst( f ).asInstanceOf[HOLFormula], subst(a.formula).asInstanceOf[HOLFormula] )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
  //    case OrLeftRule(p1, p2, s, a1, a2, m) => handleBinaryProp( new_parents.head, new_parents.last, subst, a1, a2, p1, p2, proof, OrLeftRule.apply )

      case OrRight1Rule(p, s, a, m) => {
        val f = m.formula match { case Or(_, w) => w }
        val new_parent = new_parents.head
//        val new_proof = OrRight1Rule( new_parent._1, new_parent._2( a ), subst( f ).asInstanceOf[HOLFormula] )
        val new_proof = OrRight1Rule( new_parent._1, subst( a.formula ).asInstanceOf[HOLFormula], subst( f ).asInstanceOf[HOLFormula] )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case OrRight2Rule(p, s, a, m) => {
        val f = m.formula match { case Or(w, _) => w }
        val new_parent = new_parents.head
        val new_proof = OrRight2Rule( new_parent._1, subst( f ).asInstanceOf[HOLFormula], subst( a.formula ).asInstanceOf[HOLFormula] )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }


      case NegLeftRule(p, s, a, m) => {
        val new_parent = new_parents.head
      //  val new_proof = NegLeftRule( new_parent._1, new_parent._2( a ) )
        val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
        val new_proof = NegLeftRule( new_parent._1, subst( a.formula ).asInstanceOf[HOLFormula] )
 //       ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
        (new_proof,map)
      }
      case NegRightRule(p, s, a, m) => {
        val new_parent = new_parents.head
        val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
        //val new_proof = NegRightRule( new_parent._1, new_parent._2( a ) )
        val new_proof = NegRightRule( new_parent._1, subst( a.formula ).asInstanceOf[HOLFormula] )
   //     ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
        (new_proof,map)
      }


    }
  }

  def apply(schema : SchemaProof, subst: SchemaSubstitution1[HOLExpression]) : (LKProof, Map[FormulaOccurrence, FormulaOccurrence]) = {
     subst.map.toList.head._2 match {
        case IntZero() => (CloneLKProof(schema.base), new HashMap[FormulaOccurrence, FormulaOccurrence])
        case _ => apply(schema.rec, subst)
     }
  }

  def apply( proof: LKProof, subst: SchemaSubstitution1[HOLExpression] ) : (LKProof, Map[FormulaOccurrence, FormulaOccurrence]) = {
 //   println("\n"+proof.rule+")")

    proof match {
      case SchemaProofLinkRule( seq, link, ind::_ ) => {
     //   println("\nSchemaProofLinkRule for proof "+link+" , "+ind)
          val new_ind = subst(ind)
          val new_map = (subst.map - subst.map.head._1.asInstanceOf[Var]) + Pair(subst.map.head._1.asInstanceOf[Var], Pred(new_ind.asInstanceOf[IntegerTerm]) )
          val new_subst = new SchemaSubstitution1(new_map)

          //subst.map.toList.foreach(p => println(p._1,p._2))
          //subst.map.head._2 match {

          new_ind match {
          case IntZero() => {
                    // val res = (CloneLKProof(SchemaProofDB.get(link).base), new HashMap[FormulaOccurrence, FormulaOccurrence])
                    val res = (CloneLKProof(SchemaProofDB.get(link).base), new HashMap[FormulaOccurrence, FormulaOccurrence])
     //               printSchemaProof(res._1)
                    res
          }

          case _ => {
      //      val varmap = subst.map.head._1.asInstanceOf[Var]
       //     val new_map1 = (subst.map - varmap) + Pair(varmap, Pred(subst.map.head._2.asInstanceOf[IntegerTerm]))
       //     val new_subst = new SchemaSubstitution1(new_map1)
  //          new_subst.map.toList.head._2 match {
    //            case IntZero() =>  Pair(CloneLKProof(SchemaProofDB.get(link).base), new HashMap[FormulaOccurrence, FormulaOccurrence])
         //       case _ =>
                    apply(SchemaProofDB.get(link), new_subst)
      //      }
 //           apply(SchemaProofDB.get(link), new_subst)
          }
        }
      }
      case AndEquivalenceRule1(up, r, aux, main) =>  {
    //    println("\n UnaryProof AndEquivalenceRule1: "+printSchemaProof.sequentToString(r))
        val up1 = apply(up, subst)._1
   //     println("\n"+proof.rule+")")
   //     println("\n aux = "+printSchemaProof.formulaToString(subst(aux.formula)))

   //     println("\nAndEquivalenceRule1 up1: "+printSchemaProof.sequentToString(up1.root))
        (AndEquivalenceRule1(up1, subst(aux.formula).asInstanceOf[SchemaFormula], subst(main.formula).asInstanceOf[SchemaFormula]), new HashMap[FormulaOccurrence, FormulaOccurrence])
      }

      case OrEquivalenceRule1(up, r, aux, main) =>  {
//        println("\n UnaryProof OrEquivalenceRule1: "+printSchemaProof.sequentToString(r))
        (OrEquivalenceRule1(apply(up, subst)._1, subst(aux.formula).asInstanceOf[SchemaFormula], subst(main.formula).asInstanceOf[SchemaFormula]), new HashMap[FormulaOccurrence, FormulaOccurrence])
      }

      case Axiom(_) => {
        val res = handleRule( proof, Nil, subst )
    //    println("\nAxiom")
        res
       }
      case UnaryLKProof(_, p, _, _, _) => {
        val res = handleRule( proof, apply( p, subst )::Nil, subst )
  //      println("\n"+proof.rule+")")
        res
      }

      case OrLeftRule(p1, p2, s, a1, a2, m) => {
        val pr1 = apply( p1, subst )
        val pr2 = apply( p2, subst )
   //     println("\n"+proof.rule)
    //    println("\nleft  proof seq:"+printSchemaProof.sequentToString(pr1._1.root))
     //   println("\nright proof seq:"+printSchemaProof.sequentToString(pr2._1.root))
      //  println("\naux f :"+printSchemaProof.formulaToString(subst(a1.formula))+"     |     "+printSchemaProof.formulaToString(subst(a2.formula)))
        handleBinaryProp( pr1, pr2, subst, a1, a2, p1, p2, proof, OrLeftRule.apply )
      }

      case BinaryLKProof(_, p1, p2, _, _, _, _) => {
        val res = handleRule( proof, apply( p1, subst )::apply( p2, subst )::Nil, subst )
  //      println("\n"+proof.rule)
        res
      }
      case _ => {println("\n\n\nERROR in apply schema substitution\n"); Pair(proof, new HashMap[FormulaOccurrence, FormulaOccurrence])}
    }
  }

  // TODO: a very similar method is used in LKtoLKskc, refactor!?
  def computeMap( occs: Set[FormulaOccurrence], old_proof: LKProof,
                  new_proof: LKProof, old_map : Map[FormulaOccurrence, FormulaOccurrence]) =
  {
    val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
//    occs.foreach( fo => map.update( old_proof.getDescendantInLowerSequent( fo ).get,
//      new_proof.getDescendantInLowerSequent( old_map(fo) ).get ) )
    map
  }
}




//creates a copy of an existing LK proof (used for unrolding, not to have cycles in the tree having the base proof several times)
object CloneLKProof {
import at.logic.language.hol._

    def apply(p: LKProof):LKProof = {
 //     println("\nCloneLKProof : "+p.rule)
      p match {

        case Axiom(ro) => Axiom(ro.antecedent.map(fo => fo.formula.asInstanceOf[HOLFormula]),ro.succedent.map(fo => fo.formula.asInstanceOf[HOLFormula]))

        case AndLeftEquivalenceRule1(p, s, a, m) => {
            // println("\nAndLeftEquivalenceRule1\n")
            val new_p = apply(p)
            AndLeftEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
        }

        case AndRightEquivalenceRule1(p, s, a, m) => {
           // println("\nAndRightEquivalenceRule1\n")
            val new_p = apply(p)
            AndRightEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
        }

        case OrRightEquivalenceRule1(p, s, a, m) => {
           // println("\nOrRightEquivalenceRule1\n")
            val new_p = apply(p)
            OrRightEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
        }

        case AndLeftEquivalenceRule3(p, s, a, m) => {
           // println("\nAndLeftEquivalenceRule3\n")
            val new_p = apply(p)
            AndLeftEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
        }

        case AndRightEquivalenceRule3(p, s, a, m) => {
           // println("\nAndRightEquivalenceRule3\n")
            val new_p = apply(p)
            AndRightEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
        }

        case OrRightEquivalenceRule3(p, s, a, m) => {
          //println("\nOrRightEquivalenceRule3\n")
          val new_p = apply(p)
          OrRightEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
        }

        case WeakeningLeftRule(p, _, m) => {
            val new_p = apply(p)
            implicit val factory = defaultFormulaOccurrenceFactory

            WeakeningLeftRule( new_p, m.formula )
        }

        case CutRule( p1, p2, _, a1, a2 ) => {
            val new_p1 = apply(p1)
            val new_p2 = apply(p2)
            CutRule(new_p1, new_p2, a2.formula)
        }

        case OrLeftRule(p1, p2, _, a1, a2, m) => {
            val new_p1 = apply(p1)
            val new_p2 = apply(p2)
            OrLeftRule(new_p1, new_p2, a1.formula, a2.formula)
        }

        case AndRightRule(p1, p2, _, a1, a2, m) => {
            val new_p1 = apply(p1)
            val new_p2 = apply(p2)
            AndRightRule(new_p1, new_p2, a1.formula, a2.formula)
        }

        case NegLeftRule( p, _, a, m ) => {
            val new_p = apply(p)
            NegLeftRule( new_p, a.formula )
        }

        case AndLeft1Rule(p, r, a, m) =>  {
            val new_p = apply(p)
            val a2 = m.formula  match { case And(l, right) => right }
      //      println("AndLeft1Rule : "+printSchemaProof.sequentToString(new_p.root))
       //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
        //    println(printSchemaProof.formulaToString(a2))
            AndLeft1Rule( new_p, a.formula, a2)
        }

        case AndLeft2Rule(p, r, a, m) =>  {
            val new_p = apply(p)
            val a2 = m.formula  match { case And(l, _) => l }
       //     println("AndLeft2Rule : "+printSchemaProof.sequentToString(new_p.root))
       //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
       //     println(printSchemaProof.formulaToString(a2))
            AndLeft2Rule( new_p, a2, a.formula )
        }

        case NegRightRule( p, _, a, m ) => {
            val new_p = apply(p)
            NegRightRule( new_p, a.formula )
        }

        case ContractionLeftRule(p, _, a1, a2, m) => {
            val new_p = apply(p)
            ContractionLeftRule( new_p, a1.formula )
        }
        case _ => { println("ERROR in CloneLKProof !");exit(1) }
    }}
}


class SchemaSubstitution1[T <: HOLExpression](val map: scala.collection.immutable.Map[Var, T])  {
  import at.logic.language.schema._

  def apply(expression: T): T = expression match {
      case x:IntVar => {
          map.get(x) match {
            case Some(t) => {
              //println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
              t
            }
            case _ => {
              //println(x + " Error in schema subst 1")
              x.asInstanceOf[T]
            }
          }
      }
      case IndexedPredicate(pointer @ f, l @ ts) => IndexedPredicate(pointer.name.asInstanceOf[ConstantSymbolA], apply(l.head.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
      case BigAnd(v, formula, init, end) => BigAnd(v, formula, apply(init.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[T]
      case BigOr(v, formula, init, end) =>   BigOr(v, formula, apply(init.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[T]
      case Succ(n) => Succ(apply(n.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
      case Or(l @ left, r @ right) => Or(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
      case And(l @ left, r @ right) => And(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
      case Neg(l @ left) => Neg(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]

      case _ => expression
    }
}
//-----------------  substitution end --------------------------
    */

class ProjectionsTest extends SpecificationWithJUnit {
    implicit val factory = defaultFormulaOccurrenceFactory
    import at.logic.language.schema._
    "ProjectionsTest" should {
        "create the example of Prof.Leitsch" in {

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
             println("\n\n START \n\n")

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
    val chi = new SchemaProof( "\\chi", n::Nil, Pair(BigAnd(i,A,zero,n) +: Seq.empty[HOLFormula], BigAnd(i,A,zero,n) +: Seq.empty[HOLFormula]), chi0, chin )
    SchemaProofDB.put( chi )
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




            val psi = new SchemaProof( "\\psi", n::Nil, Pair(A0 +: BigAnd(i, orneg, zero, n1) +: Seq.empty[HOLFormula], BigAnd(i,A,zero,n2) +: Seq.empty[HOLFormula]), base, step )
            SchemaProofDB.put( psi )

     //        printSchemaProof( step )


         val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(n, one)
         val subst = new SchemaSubstitution1[HOLExpression](new_map)
         val psi1 = applySchemaSubstitution(psi, subst)
    //     Main.display("psi1", applySchemaSubstitution(psi, subst)) ; while(true) {}
   //     saveXML( ("psi1", psi1)::Nil, List(), "ceco.xml" )



   //      printSchemaProof(base)
       //  Main.display("base", base) ; while(true) {}

    //     while(true) {}
           println("\n\n PROJECTIONS \n\n")

        val cs = DeleteRedundantSequents( DeleteTautology( StandardClauseSet.transformStructToClauseSet( StructCreators.extract(psi1) ) ) )
        cs.foreach(s => println(printSchemaProof.sequentToString(s)+"\n"))

   //    val cs = StandardClauseSet.transformStructToClauseSet( StructCreators.extractStruct( "\\chi", real_n ) )


   //      val step1 = applySchemaSubstitution(step, subst)  ;

       //  Main.display("Proof", cs)         ;while(true) {}



      //     val f = step.root.succedent.toList.head
         val projs = Projections(step, s).toList
         projs.foreach(p => { println("\nNext projection:\n");printSchemaProof( p._1 )})
      //     Main.display("Projection", projs.tail.head._1); while(true) {}
















        }
    }




                /*
  "ProjectionsTest" should {
    "create projections for schema" in {

      val a = HOLVarFormula( "a" )
      val b = HOLVarFormula( "b" )
      val c = HOLVarFormula( "c" )
      val d = HOLVarFormula( "d" )

      val k = IntVar(new VariableStringSymbol("k"))
      val i = IntVar(new VariableStringSymbol("i"))
      val A = IndexedPredicate(new ConstantStringSymbol("A"), i::Nil)

      val A0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero())
      val B0 = IndexedPredicate(new ConstantStringSymbol("B"), IntZero())

      val Ak = IndexedPredicate(new ConstantStringSymbol("A"), k)
      val Ak1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(k))
      println("\n\n START \n\n")

      val ax = Axiom(A0::Nil, B0::Nil)
      val ax1 = Axiom(B0::Nil, A0::Nil)
      val cut1 = CutRule(ax, ax1, B0)
      val andl = AndLeftEquivalenceRule3(cut1, A0, BigAnd(i, A, IntZero(), IntZero()))
      val base = OrRightEquivalenceRule3(andl, A0, BigOr(i, A, IntZero(), IntZero()))


      val phi_k = SchemaProofLinkRule(Sequent(BigAnd(i, A, IntZero(), k)::Nil, BigOr(i, A, IntZero(), k)::Nil), "\\phi", k::Nil)
      val ax2 = Axiom(BigOr(i, A, IntZero(), k)::Nil, BigOr(i, A, IntZero(), k)::Nil)
      val cut = CutRule(phi_k, ax2, BigOr(i, A, IntZero(), k))

      val andlcut = AndLeft2Rule(cut, Ak1, BigAnd(i, A, IntZero(), k))
      val orrandlcut = OrRight2Rule(andlcut, Ak1, BigOr(i, A, IntZero(), k))
      val andeq = AndLeftEquivalenceRule1(orrandlcut, (And(Ak1, BigAnd(i, A, IntZero(), k))).asInstanceOf[SchemaFormula], BigAnd(i, A, IntZero(), Succ(k)))
      val step = OrRightEquivalenceRule1(andeq, (Or(Ak1, BigOr(i, A, IntZero(), k))).asInstanceOf[SchemaFormula], BigOr(i, A, IntZero(), Succ(k)))

      printSchemaProof( step )


      //projections:
            println("\n\n PROJECTIONS \n\n")

      val f = base.root.antecedent.toList.head//.formula.asInstanceOf[SchemaFormula]
      //val omega = Pair(HashMultiset[SchemaFormula]()+f, HashMultiset[SchemaFormula]())
      //val omega = Pair(HashMultiset[SchemaFormula](), HashMultiset[SchemaFormula]())
      val s = Set[FormulaOccurrence]()+f
    //  Projections(base, s).toList.foreach(p => {println("\nNext projection:\n");printSchemaProof( p._1 )})
    }
  }
  */

 }