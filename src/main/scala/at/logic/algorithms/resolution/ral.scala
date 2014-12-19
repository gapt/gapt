package at.logic.algorithms.resolution

import at.logic.algorithms.fol.{recreateWithFactory, fol2hol}
import at.logic.calculi.lk.base.{LKUnaryRuleCreationException, FSequent}
import at.logic.calculi.lksk.TypeSynonyms.{EmptyLabel, Label}
import at.logic.calculi.resolution.Clause
import at.logic.calculi.resolution.robinson._
import at.logic.calculi.resolution.ral._
import at.logic.calculi.lksk.{LabelledFormulaOccurrence, LabelledSequent}
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.fol.{FOLExpression, FOLFormula, Substitution => FOLSubstitution}
import at.logic.language.hol._
import at.logic.language.lambda.{Substitution => LambdaSubstitution, Var, FactoryA, LambdaExpression}

/**
 * Created by marty on 9/9/14.
 */

object RobinsonToRal extends RobinsonToRal {
  override def convert_formula(e:HOLFormula) : HOLFormula =
    recreateWithFactory(e,HOLFactory).asInstanceOf[HOLFormula]
  override def convert_substitution(s:Substitution) : Substitution = {
    recreateWithFactory(s, HOLFactory, convert_map).asInstanceOf[Substitution]
  }

  //TODO: this is somehow dirty....
  def convert_map(m : Map[Var,LambdaExpression]) : LambdaSubstitution =
    Substitution(m.asInstanceOf[Map[HOLVar,HOLExpression]])
}

case class RalException[V <: LabelledSequent](val message : String, val rp : List[RobinsonResolutionProof], val ralp : List[RalResolutionProof[V]], val exp : List[HOLExpression]) extends Exception(message);

abstract class RobinsonToRal {
  type TranslationMap = Map[FormulaOccurrence, LabelledFormulaOccurrence]
  val emptyTranslationMap = Map[FormulaOccurrence, LabelledFormulaOccurrence]()

  /* convert formula will be called on any formula before translation */
  def convert_formula(e:HOLFormula) : HOLFormula;

  /* convert subsitution will be called on any substitution before translation */
  def convert_substitution(s:Substitution) : Substitution;

  def convert_sequent(fs:FSequent) : FSequent = FSequent(fs.antecedent.map(convert_formula), fs.succedent.map(convert_formula))

  def apply(rp : RobinsonResolutionProof) : RalResolutionProof[LabelledSequent] = apply(rp, emptyTranslationMap)._2

  def apply(rp : RobinsonResolutionProof, map : TranslationMap) : (TranslationMap, RalResolutionProof[LabelledSequent]) =
    rp match {
      case InitialClause(clause) =>
        val fc : FSequent = clause.toFSequent
        val rule = InitialSequent(convert_sequent(fc), (fc.antecedent.toList.map(x => EmptyLabel()), fc.succedent.toList.map(x => EmptyLabel())))
        my_require(rule.root.toFSequent  , clause.toFSequent, "Error in initial translation, translated root: "+rule.root.toFSequent+" is not original root "+clause.toFSequent)
        require(! rule.root.toFSequent.formulas.contains((x:HOLFormula) => x.isInstanceOf[FOLFormula]), "Formulas contain fol content!")

        (emptyTranslationMap, rule)


      case Resolution(clause, p1, p2, aux1, aux2, sub_) =>
        //println("Resolution on "+aux1+" in "+p1.root.succedent+" and "+aux2+" in "+p2.root.antecedent+ " with sub "+sub_)
        val sub = convert_substitution(sub_)
        val (rmap1, rp1) = apply(p1, map)
        val (rmap2, rp2) = apply(p2, rmap1)
        val sub1 = if (sub.isIdentity) rp1 else Sub(rp1, sub)
        val sub2 = if (sub.isIdentity) rp2 else Sub(rp2, sub)
        val rule = Cut(sub1, sub2, List(pickFOsucc(convert_formula(sub(aux1.formula)), sub1.root, Nil)),
                                   List(pickFOant(convert_formula(sub(aux2.formula)), sub2.root, Nil)))
        my_require(rule.root.toFSequent  , clause.toFSequent, "Error in resolution translation, translated root: "+rule.root.toFSequent+" is not original root "+clause.toFSequent)

        (rmap2, rule)

      case Factor(clause, parent, List(aux1@(f1::_)), sub_) if parent.root.antecedent.contains(f1) =>
//        println("antecedent factor 1: "+aux1+"\n"+parent.root+"\n"+clause)
        val sub = convert_substitution(sub_)
        val (rmap1, rp1) = apply(parent, map)
        val sub1 = if (sub.isIdentity) rp1 else Sub(rp1, sub)
        val (a::aux) = aux1.foldLeft(List[LabelledFormulaOccurrence]())((list,x) => pickFOant(convert_formula(sub(x.formula)), rp1.root, list)::list).reverse
        val rule = AFactorF(rp1, a, aux )
        my_require(rule.root.toFSequent , clause.toFSequent, "Error in factor translation, translated root: "+rule.root.toFSequent+" is not original root "+clause.toFSequent)

        (rmap1, rule)

      case Factor(clause, parent, List(aux1@(f1::_)), sub_) if parent.root.succedent.contains(f1) =>
        println("succedent factor 1: "+aux1+"\n"+parent.root+"\n"+clause)
        val sub = convert_substitution(sub_)
        val (rmap1, rp1) = apply(parent, map)
        val sub1 = if (sub.isIdentity) rp1 else Sub(rp1, sub)
        val (a::aux) = aux1.foldLeft(List[LabelledFormulaOccurrence]())((list,x) => pickFOsucc(convert_formula(sub(x.formula)), rp1.root, list)::list).reverse
        val rule = AFactorT(rp1, a, aux )
        my_require(rule.root.toFSequent , clause.toFSequent, "Error in factor translation, translated root: "+rule.root.toFSequent+" is not original root "+clause.toFSequent)
        (rmap1, rule)

      case Paramodulation(clause, paraparent, parent, equation, modulant, primary, sub_ ) if parent.root.antecedent contains modulant =>
        val sub = convert_substitution(sub_)
        val (rmap1, rp1) = apply(paraparent, map)
        val (rmap2, rp2) = apply(parent, rmap1)
        val sub1 = if (sub.isIdentity) rp1 else Sub(rp1, sub)
        val sub2 = if (sub.isIdentity) rp2 else Sub(rp2, sub)
        val rule = ParaF(sub1,sub2, pickFOsucc(convert_formula(sub(equation.formula)), sub1.root, List()), pickFOant(convert_formula(sub(modulant.formula)), sub2.root, List()), convert_formula(primary.formula))
        my_require(rule.root.toFSequent , clause.toFSequent, "Error in para translation, translated root: "+rule.root.toFSequent+" is not original root "+clause.toFSequent)
        (rmap2, rule)

      case Paramodulation(clause, paraparent, parent, equation, modulant, primary, sub_ ) if parent.root.succedent contains modulant =>
//        println("translating instance from para parent:"+paraparent.root+" and "+ parent.root +" to "+clause+" with sub "+sub_)
        val sub = convert_substitution(sub_)
        val (rmap1, rp1) = apply(paraparent, map)
        val (rmap2, rp2) = apply(parent, rmap1)
        val sub1 = if (sub.isIdentity) rp1 else Sub(rp1, sub)
        val sub2 = if (sub.isIdentity) rp2 else Sub(rp2, sub)
        val rule = ParaT(sub1,sub2, pickFOsucc(convert_formula(sub(equation.formula)), sub1.root, List()), pickFOsucc(convert_formula(sub(modulant.formula)), sub2.root, List()), convert_formula(primary.formula))
        my_require(rule.root.toFSequent , clause.toFSequent, "Error in para translation, translated root: "+rule.root.toFSequent+" is not original root "+clause.toFSequent)
        (rmap2, rule)

      case Variant(clause, parent, sub_) =>
        val sub = convert_substitution(sub_)
        val (rmap1, rp1) = apply(parent, map)
        val sub1 = Sub(rp1, sub)
        my_require(sub1.root.toFSequent, clause.toFSequent, "Error in variant translation, translated root: "+sub1.root.toFSequent+" is not original root "+clause.toFSequent)
        (rmap1, sub1)

      case Instance(clause, parent, sub_) =>

        val sub = convert_substitution(sub_)
//        val subexps = sub.holmap.toList.flatMap(x => List(x._1,x._2)).filterNot(checkFactory(_, HOLFactory))
//        my_require(subexps.isEmpty , "Substitution contains fol content: "+subexps.map(_.factory))
        val (rmap1, rp1) = apply(parent, map)
//        val rootexps = rp1.root.toFSequent.formulas.filterNot(checkFactory(_,HOLFactory))
//        my_require(rootexps.isEmpty, "Formulas contain fol content: "+rootexps.mkString(" ::: "))
        val rule = if (sub.isIdentity) rp1 else Sub(rp1, sub)

        //println("inferring instance from parent:"+rp1.root+" to "+rule.root+" with sub "+sub)
        my_require(rule.root.toFSequent, clause.toFSequent, "Error in instance translation, translated root: "+rule.root.toFSequent+" is not original root "+clause.toFSequent)
        (rmap1, rule)


      case Factor(clause, parent, List(aux1@(f1::_), aux2@(f2::_)), sub_) =>
  //      println("factor 2")

        val sub = convert_substitution(sub_)
        val (rmap1, rp1) = apply(parent, map)
        val sub1 = if (sub.isIdentity) rp1 else Sub(rp1, sub)

        val rule1 = if (aux1.forall(parent.root.antecedent.contains(_))) {
          val (a1::auxs1) = aux1.foldLeft(List[LabelledFormulaOccurrence]())((list,x) => pickFOant(convert_formula(sub(x.formula)), rp1.root, list)::list).reverse
          AFactorF(rp1, a1, auxs1 )
        } else if (aux1.forall(parent.root.succedent.contains(_))) {
          val (a1::auxs1) = aux1.foldLeft(List[LabelledFormulaOccurrence]())((list,x) => pickFOsucc(convert_formula(sub(x.formula)), rp1.root, list)::list).reverse
          AFactorT(rp1, a1, auxs1 )
        } else throw new Exception("Could not find all auxiliary occurrences of a factor rule!")

        val rule2 = if (aux2.forall(parent.root.antecedent.contains(_))) {
          val (a1::auxs1) = aux1.foldLeft(List[LabelledFormulaOccurrence]())((list,x) => pickFOant(convert_formula(sub(x.formula)), rule1.root, list)::list).reverse
          AFactorF(rule1, a1, auxs1 )
        } else if (aux1.forall(parent.root.succedent.contains(_))) {
          val (a1::auxs1) = aux1.foldLeft(List[LabelledFormulaOccurrence]())((list,x) => pickFOsucc(convert_formula(sub(x.formula)), rule1.root, list)::list).reverse
          AFactorT(rule1, a1, auxs1 )
        } else throw new Exception("Could not find all auxiliary occurrences of a factor rule!")

        (rmap1, rule2)

      case _ =>
        throw new RalException("Unhandled case: ", rp::Nil, Nil, Nil)

  }

  def my_require(fs1 : FSequent, fs2 : FSequent, msg : String) = {
    val cfs2 = convert_sequent(fs2)
    require(fs1 multiSetEquals (convert_sequent(fs2)), msg+" (converted sequent is "+cfs2+")") //commented out, because the translation is too flexible now
  }

  import at.logic.language.lambda
  def checkFactory(e:LambdaExpression, f : FactoryA) : Boolean = e match {
    case lambda.Var(_,_) if e.factory == f => true
    case lambda.Const(_,_) if e.factory == f => true
    case lambda.App(s,t) if e.factory == f => checkFactory(s,f) && checkFactory(t,f)
    case lambda.Abs(x,t) if e.factory == f => checkFactory(x,f) && checkFactory(t,f)
    case _ if e.factory == f =>
      println("unhandled case for "+e)
      false
    case _ =>
      println("wrong factory for "+e+" expected: "+f+" but is:"+e.factory)
      false
  }

  def pickFO(f:HOLFormula, list : Seq[LabelledFormulaOccurrence], exclusion_list : Seq[LabelledFormulaOccurrence]) : LabelledFormulaOccurrence =
    list.find(x => x.formula == f && ! exclusion_list.contains(x)) match {
    case None => throw new Exception("Could not find auxiliary formula "+f+" in "+list.mkString("(",",",")"))
    case Some(focc) => focc
  }

  def pickFOant(f:HOLFormula, fs : LabelledSequent, exclusion_list : Seq[LabelledFormulaOccurrence]) = pickFO(f, fs.l_antecedent, exclusion_list)
  def pickFOsucc(f:HOLFormula, fs : LabelledSequent, exclusion_list : Seq[LabelledFormulaOccurrence]) = pickFO(f, fs.l_succedent, exclusion_list)

  def updateMap(map : TranslationMap, root1 : Clause, root2 : Clause, nroot : LabelledSequent) : TranslationMap = {

    val nmap1 = root1.occurrences.foldLeft(map)( (recmap, fo) => {
      nroot.occurrences.find(x => {
        require(x.parents.size == 1, "Ancestors of "+x+" must be exactly 1 (Substitution)")
        val newanc = x.parents(0).parents
        val oldanc = newanc.map(y => {
          map.filterKeys(_ == y).toList match {
            case x::Nil =>
              x
            case Nil =>
              throw new Exception("Could not find old ancestor match for "+y)
            case xs =>
              throw new Exception("Ambigous ancestor mapping for "+y+": all in "+xs+" map to it!")
          }
        })

        true
      }) match {
        case None =>
          throw new Exception()
        case Some(_) =>
          throw new Exception()
      }

    })
    map

  }



  def getOccFromAnteAncestor(ralp : RalResolutionProof[LabelledSequent], map : TranslationMap, occ : FormulaOccurrence) =
    getOccFromAncestor(ralp, map, occ, false)
  def getOccFromSuccAncestor(ralp : RalResolutionProof[LabelledSequent], map : TranslationMap, occ : FormulaOccurrence) =
    getOccFromAncestor(ralp, map, occ, true)
  def getOccFromAncestor(ralp : RalResolutionProof[LabelledSequent], map : TranslationMap, occ : FormulaOccurrence, side : Boolean) = {
    val occurrences = if (side == false) ralp.root.l_antecedent else ralp.root.l_succedent
    val ancocc = occurrences.find(x => {
      x.parents match {
        case List(pocc) if map(occ) == pocc => true
        case _ => false
      }
    })

    ancocc match {
      case None =>
        throw new Exception("Could not find occurrence "+occ+ " in ancestors of an occurrence in "+ralp.root)
      case Some(fo) =>
        fo
    }
  }


}
