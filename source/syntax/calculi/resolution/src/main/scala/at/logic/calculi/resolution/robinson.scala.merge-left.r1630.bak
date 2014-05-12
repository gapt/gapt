/*
 * robinson.scala
 *
 * Traditional resolution calculus with factors and para modulation. Using clauses
 */
package at.logic.calculi.resolution

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol.HOLFormula
import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.acyclicGraphs._
import at.logic.language.lambda.substitutions._
import at.logic.calculi.lk.base._
import base._
import scala.collection.immutable.HashSet

package robinson {

import at.logic.language.fol.Neg
import at.logic.language.hol.{HOLVar, Formula, HOLExpression, Neg => HOLNeg}
import at.logic.language.lambda.substitutions.Substitution._
import at.logic.language.lambda.types.->
import at.logic.utils.traits.Occurrence
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.resolution.instance._

/* creates new formula occurrences where sub is applied to each element x in the given set and which has x as an ancestor
 * additional_context  may add additional ancestors, needed e.g. for factoring */
object createContext {
    def apply(set: Seq[FormulaOccurrence], sub: Substitution[FOLExpression]): Seq[FormulaOccurrence] =
      apply(set, sub, Map[FormulaOccurrence, List[FormulaOccurrence]]())
    def apply(set: Seq[FormulaOccurrence], sub: Substitution[FOLExpression], additional_context : Map[FormulaOccurrence, Seq[FormulaOccurrence]]): Seq[FormulaOccurrence] =
      set.map(x =>
                x.factory.createFormulaOccurrence(sub(x.formula.asInstanceOf[FOLFormula]).asInstanceOf[HOLFormula],
                                                  x::additional_context.getOrElse(x,Nil).toList)
             )
}

  case object VariantType extends UnaryRuleTypeA
  case object FactorType extends UnaryRuleTypeA
  case object ResolutionType extends BinaryRuleTypeA
  case object ParamodulationType extends BinaryRuleTypeA

  trait RobinsonResolutionProof extends ResolutionProof[Clause] {
    def getAccumulatedSubstitution: Substitution[FOLExpression]
  }

  object InitialClause {
    def apply(ant: Seq[FOLFormula], suc: Seq[FOLFormula]) (implicit factory: FOFactory): RobinsonResolutionProof = {
      val left: Seq[FormulaOccurrence] = ant.map(factory.createFormulaOccurrence(_,Nil))
      val right: Seq[FormulaOccurrence] = suc.map(factory.createFormulaOccurrence(_,Nil))
      new LeafAGraph[Clause](Clause(left, right)) with NullaryResolutionProof[Clause]  with RobinsonResolutionProof {
        def rule = InitialType
        override def name = ""
        def getAccumulatedSubstitution = Substitution[FOLExpression]()
      }
    }
    def apply(literals: Seq[FOLFormula]) (implicit factory: FOFactory): RobinsonResolutionProof = {
      val lits: Seq[Pair[FormulaOccurrence,Boolean]] = literals.map(l => if (IsNeg(l)) (factory.createFormulaOccurrence(StripNeg(l),Nil),false)
        else (factory.createFormulaOccurrence(l,Nil),true))
      new LeafAGraph[Clause](Clause(lits)) with NullaryResolutionProof[Clause] with RobinsonResolutionProof {
        def rule = InitialType
        override def name = ""
        def getAccumulatedSubstitution = Substitution[FOLExpression]()
      }
    }
    def unapply(proof: ResolutionProof[Clause]) = if (proof.rule == InitialType) Some((proof.root)) else None
  }

  // left side is always resolved on positive literal and right on negative
  object Resolution {
    def apply(p1: RobinsonResolutionProof, p2: RobinsonResolutionProof,
              a1: FormulaOccurrence, a2: FormulaOccurrence, sub: Substitution[FOLExpression]): RobinsonResolutionProof = {
      val term1op = p1.root.succedent.find(_ == a1)
      val term2op = p2.root.antecedent.find(_ == a2)

      (term1op,term2op) match {
        case (Some(term1), Some(term2)) =>
          if (sub(term1.formula.asInstanceOf[FOLFormula]) != sub(term2.formula.asInstanceOf[FOLFormula]))
            throw new LKRuleCreationException("Formulas to be cut are not identical (modulo the given substitution)")
          else {
            new BinaryAGraph[Clause](Clause(
              createContext(p1.root.antecedent, sub) ++ createContext(p2.root.antecedent.filterNot(_ == term2), sub),
              createContext(p1.root.succedent.filterNot(_ == term1), sub) ++ createContext(p2.root.succedent, sub))
              , p1, p2)
              with BinaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with AuxiliaryFormulas with RobinsonResolutionProof {
              def rule = ResolutionType
              def aux = (term1::Nil)::(term2::Nil)::Nil
              def substitution = sub
              override def toString = "Res(" + root.toString + ", " + p1.toString + ", " + p2.toString + ", " + substitution.toString + ")"
              override def name = "res"
              def getAccumulatedSubstitution = substitution compose p1.getAccumulatedSubstitution compose p2.getAccumulatedSubstitution
            }
          }

        case _ =>
          throw new LKRuleCreationException("Auxiliary formulas are not contained in the correct part of the sequent (first argument positive, second negative)")
      }
    }
   def unapply(proof: ResolutionProof[Clause] with AppliedSubstitution[FOLExpression]) = if (proof.rule == ResolutionType) {
        val pr = proof.asInstanceOf[BinaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with AuxiliaryFormulas]
        Some((pr.root, pr.uProof1.asInstanceOf[RobinsonResolutionProof], pr.uProof2.asInstanceOf[RobinsonResolutionProof],
          pr.aux.head.head, pr.aux.tail.head.head, pr.substitution))
      }
      else None
/*
    def apply(p1: ResolutionProof[Clause], p2: ResolutionProof[Clause], a1: FormulaOccurrence, a2: FormulaOccurrence ): ResolutionProof[Clause] = {
      val unifiers = FOLUnificationAlgorithm.unify( a1.formula.asInstanceOf[FOLExpression], a2.formula.asInstanceOf[FOLExpression] )
      if ( unifiers.isEmpty )
        throw new LKRuleCreationException("Auxiliary formulas " + a1.formula + " and " + a2.formula + " are not unifiable!")
      apply( p1, p2, a1, a2, unifiers.head.asInstanceOf[Substitution[FOLFormula]] )
    }
*/
  }

  object Paramodulation {
    def apply(p1: RobinsonResolutionProof, p2: RobinsonResolutionProof, a1: Occurrence, a2: Occurrence, newLiteral: FOLFormula, sub: Substitution[FOLExpression]): RobinsonResolutionProof = {
      val term1op = p1.root.succedent.find(_ == a1)
      val term2opAnt = p2.root.antecedent.find(_ == a2)
      val term2opSuc = p2.root.succedent.find(_ == a2)

      (term1op, term2opAnt, term2opSuc) match {
        case (None, _ , _ ) => throw new LKRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
        case (_ ,None,None) => throw new LKRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
        case (Some(term1), Some(term2), _ ) =>
          val prinFormula = term2.factory.createFormulaOccurrence(sub(newLiteral).asInstanceOf[FOLFormula], term1::term2::Nil)
          new BinaryAGraph[Clause](Clause(
              createContext(p1.root.antecedent, sub) ++ createContext(p2.root.antecedent.filterNot(_ == term2), sub) :+ prinFormula,
              createContext(p1.root.succedent.filterNot(_ == term1), sub) ++ createContext(p2.root.succedent, sub))
            , p1, p2)
            with BinaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with AuxiliaryFormulas with RobinsonResolutionProof {
                def rule = ParamodulationType
                def aux = (term1::Nil)::(term2::Nil)::Nil
                def substitution = sub
                override def toString = "Para(" + root.toString + ", " + p1.toString + ", " + p2.toString + ", " + substitution.toString + ")"
                override def name = "pmod"
                def getAccumulatedSubstitution = substitution compose p1.getAccumulatedSubstitution compose p2.getAccumulatedSubstitution
            }

        case (Some(term1), _ , Some(term2)) =>
          val term2 = term2opSuc.get
          val prinFormula = term2.factory.createFormulaOccurrence(sub(newLiteral).asInstanceOf[FOLFormula], term1::term2::Nil)
          new BinaryAGraph[Clause](Clause(
              createContext(p1.root.antecedent, sub) ++ createContext(p2.root.antecedent, sub),
              createContext(p1.root.succedent.filterNot(_ == term1), sub) ++ createContext(p2.root.succedent.filterNot(_ == term2), sub)  :+ prinFormula)
            , p1, p2)
            with BinaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with AuxiliaryFormulas with RobinsonResolutionProof {
                def rule = ParamodulationType
                def aux = (term1::Nil)::(term2::Nil)::Nil
                def substitution = sub
                override def toString = "Para(" + root.toString + ", " + p1.toString + ", " + p2.toString + ", " + substitution.toString + ")"
                override def name = "pmod"
                def getAccumulatedSubstitution = substitution compose p1.getAccumulatedSubstitution compose p2.getAccumulatedSubstitution
            }
        }
    }
    
    def unapply(proof: ResolutionProof[Clause] with AppliedSubstitution[FOLExpression]) = if (proof.rule == ParamodulationType) {
      val p = proof.asInstanceOf[BinaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with AuxiliaryFormulas with RobinsonResolutionProof]
      if (p.aux.size != 2) throw new Exception("Unexpected number of auxiliary clauses during Paramodulation matching (aux.size != 2)!")
      if (p.aux(0).size != 1) throw new Exception("Unexpected number of auxiliary clauses during Paramodulation matching (aux(0).size != 1)!")
      if (p.aux(1).size != 1) throw new Exception("Unexpected number of auxiliary clauses during Paramodulation matching (aux(1).size != 1)!")

      Some( (p.root, p.uProof1.asInstanceOf[RobinsonResolutionProof], p.uProof2.asInstanceOf[RobinsonResolutionProof],
        p.aux(0)(0), p.aux(1)(0), p.substitution) )
    } else None
  }


  object Variant {
    def apply(p: RobinsonResolutionProof, sub: Substitution[FOLExpression]): RobinsonResolutionProof = {
      require( sub.isRenaming )
      val newCl = Clause( createContext( p.root.antecedent, sub ), createContext( p.root.succedent, sub ) )
      new UnaryAGraph[Clause](newCl, p)
          with UnaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with RobinsonResolutionProof {
            def rule = VariantType
            def substitution = sub
            override def toString = "Vr(" + root.toString + ", " + p.toString + ", " + substitution.toString + ")"
            override def name = "variant"
            def getAccumulatedSubstitution = substitution compose p.getAccumulatedSubstitution
          }
    }

    def apply(p: RobinsonResolutionProof): ResolutionProof[Clause] = {
      // TODO: refactor the following into Sequent.getFreeAndBoundVariables
      val vars = p.root.occurrences.foldLeft( HashSet[Var]() )( (m, f) => m ++ f.freeVariables.asInstanceOf[Set[FOLVar]] )
      // TODO: should not be necessary to pass argument Ti() here.
      // we return an actual variant only if there are free variables, otherwise we return the parent proof as it does not change
      if (vars.isEmpty) p
      else apply( p, Substitution( vars.map( v => (v, v.factory.createVar( FreshVariableSymbolFactory.getVariableSymbol, Ti()) ) ).toMap ).asInstanceOf[Substitution[FOLExpression]] )
    }

    def unapply(proof: ResolutionProof[Clause] with AppliedSubstitution[FOLExpression]) = if (proof.rule == VariantType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression]]
        Some((pr.root, pr.uProof.asInstanceOf[RobinsonResolutionProof], pr.substitution))
      }
      else None
  }


  object Factor {
    /* the substitution contains also the substitutions generated by the resolution step happening later. We apply it
     * now as it does not contain temporary substitutions for example:
     * we first resolve p(y), p(x), -p(f(y) with -p(a) to get p(y), -p(f(y)) with x -> a and then we look for possible
     * factors, like y -> x and get the factor p(x), -p(f(x)) with substitution y -> x and x -> a. but as we combine
     * the substitutions we cannot remove the substitution generated by the first step. This is not important as we
     * apply the same resolution step and therefore this substitution should be anyway generated.
     */

    /* creates a factorization of a single formula */
    def apply(p: RobinsonResolutionProof,
              a: FormulaOccurrence, occurrencesToRemove: Seq[FormulaOccurrence],
              sub: Substitution[FOLExpression]): RobinsonResolutionProof = {
      val r = p.root.removeFormulasAtOccurrences(occurrencesToRemove)
      val additional_ancestors = Map[FormulaOccurrence, List[FormulaOccurrence]]() + ((a,occurrencesToRemove))
      val newCl = Clause( createContext( r.antecedent, sub, additional_ancestors ), createContext( r.succedent, sub, additional_ancestors ))
      new UnaryAGraph[Clause](newCl, p)
        with UnaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with AuxiliaryFormulas with RobinsonResolutionProof {
          def rule = FactorType
          def substitution = sub
          def aux = (a::occurrencesToRemove.toList)::Nil
          override def toString = "Fac(" + root + ", " + p.toString + ", " + substitution.toString + ")"
          override def name = "factor"
          def getAccumulatedSubstitution = substitution compose p.getAccumulatedSubstitution
        }
    }

    /* creates a factorization of two formulas (intention: one positive and one negative) of the sequent */
    def apply(p: RobinsonResolutionProof,
              a: FormulaOccurrence, oc1: Seq[FormulaOccurrence],
              b: FormulaOccurrence, oc2: Seq[FormulaOccurrence],
              sub: Substitution[FOLExpression]): RobinsonResolutionProof = {
      val r = p.root.removeFormulasAtOccurrences(oc1 ++ oc2)
      val additional_ancestors = Map[FormulaOccurrence, List[FormulaOccurrence]]() ++ List((a,oc1), (b,oc2))
      val newCl = Clause( createContext( r.antecedent, sub, additional_ancestors ), createContext( r.succedent, sub, additional_ancestors ))
      new UnaryAGraph[Clause](newCl, p)
        with UnaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with AuxiliaryFormulas with RobinsonResolutionProof {
        def rule = FactorType
        def substitution = sub
        def aux = (a::oc1.toList)::(b::oc2.toList)::Nil
        override def toString = "Fac(" + root + ", " + p.toString + ", " + substitution.toString + ")"
        override def name = "factor"
        def getAccumulatedSubstitution = substitution compose p.getAccumulatedSubstitution
      }
    }

    /* decomposes to root clause, parent proof, aux formula and the substitution needed
     * aux contains the list of auxiliar formulas for each factored formula in the conclusion
     * (i.e. aux.size is either 1 or 2, each contained list has size >=1).  */
    def unapply(proof: ResolutionProof[Clause] with AppliedSubstitution[FOLExpression]) = if (proof.rule == FactorType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with AuxiliaryFormulas]
        Some((pr.root, pr.uProof.asInstanceOf[RobinsonResolutionProof], pr.aux, pr.substitution))
      }
      else None
  }


object Formatter {
  //TODO: replace this by the standard scala io
  def printToFile(f: java.io.File)(op: java.io.PrintWriter => Unit) {
    val p = new java.io.PrintWriter(f)
    try { op(p) } finally { p.close() }
  }

  def lst2string[T](fun:(T=>String), seperator: String, l:List[T]) : String = l match {
    case Nil => ""
    case List(x) => fun(x)
    case x::xs => fun(x)  + seperator + lst2string(fun, seperator, xs)
  }



  def apply(p: ResolutionProof[Clause]) : String = {
    apply("", p, createMap(p,1, Map[Clause, Int]())._1)
  }


  def asHumanReadableString(p:ResolutionProof[Clause]) = apply(p)

  def createMap(p : ResolutionProof[Clause], i : Int, map : Map[Clause, Int]) : (Map[Clause, Int], Int) = p match {
    case Resolution(clause, p1, p2, occ1, occ2, subst) =>
      val (m1,h1) = createMap(p1, i, map)
      val (m2,h2) = createMap(p2, h1, m1)
      if (m2 contains clause)
        (m2,h2)
      else
        (m2 + ((clause, h2+1)), h2+1)

    case Paramodulation(clause, p1, p2, occ1, occ2, subst) =>
      val (m1,h1) = createMap(p1, i, map)
      val (m2,h2) = createMap(p2, h1, m1)
      if (m2 contains clause)
        (m2,h2)
      else
        (m2 + ((clause, h2+1)), h2+1)
    case Factor(clause, p1, _, sub) =>
      val (m1,h1) = createMap(p1, i, map)
      if (m1 contains clause)
        (m1,h1)
      else
        (m1 + ((clause, h1+1)), h1+1)
    case Variant(clause, p1, sub) =>
      val (m1,h1) = createMap(p1, i, map)
      if (m1 contains clause)
        (m1,h1)
      else
        (m1 + ((clause, h1+1)), h1+1)

    case Instance(clause, p1, sub) =>
      val (m1,h1) = createMap(p1, i, map)
      if (m1 contains clause)
        (m1,h1)
      else
        (m1 + ((clause, h1+1)), h1+1)

    case InitialClause(clause) =>
      if (map contains clause)
        (map,i)
      else
        (map + ((clause, i+1)), i+1)

    case _ => throw new Exception("Unhandled Case!")
  }

  def asTex(p : ResolutionProof[Clause]) : String = {
    val ids = createMap(p,1, Map[Clause, Int]())._1
    """\documentclass[a4paper,8pt,usenames,dvipsnames]{article}
\ usepackage[utf8]{inputenc}
\ usepackage{amssymb}
\ usepackage{mathabx}
\ usepackage[T1]{fontenc}% Needed for Type1 Concrete
\ usepackage{bussproofs}

\renewcommand{\fCenter}{\ensuremath{\vdash} }
\newcommand{\AX}[2]{\AxiomC{\ensuremath{#1} \fCenter \ensuremath{#2}}}
\newcommand{\UI}[2]{\UnaryInfC{\ensuremath{#1} \fCenter \ensuremath{#2}}}
\newcommand{\BI}[2]{\BinaryInfC{\ensuremath{#1} \fCenter \ensuremath{#2}}}
\newcommand{\LL}[1]{\LeftLabel{\footnotesize \ensuremath{#1}}}
\newcommand{\RL}[1]{\RightLabel{\footnotesize \ensuremath{#1}}}

\begin{document}"""+
      tex(p, ids, List())._1 + "\n\\DisplayProof\n\\end{document}"
  }

  def escapeTex(s:String) = s.replaceAll("_","\\_")


  def tex(p : ResolutionProof[Clause], ids : Map[Clause, Int], edges : List[List[Int]] )
  : (String, List[List[Int]]) = {
    def f(l:Seq[FormulaOccurrence]) : String = lst2string( (x:FormulaOccurrence) => escapeTex(x.formula.toPrettyString), ",", l.toList)

    p match {
      case Resolution(clause, p1, p2, occ1, occ2, subst) =>
        val (str1, e1) = tex( p1, ids, edges)
        val (str2, e2) = tex( p2, ids, e1)
        (str1 + str2 + "\\RL{Resolve} \n\\BI{" + f(clause.negative) + "}{" + f(clause.positive) +"}",   e1)


      case Paramodulation(clause, p1, p2, occ1, occ2, subst) =>
        val (str1, e1) = tex( p1, ids, edges)
        val (str2, e2) = tex( p2, ids, e1)
        (str1 + str2 + "\\RL{Para} \n\\BI{" + f(clause.negative) + "}{" + f(clause.positive) +"}",   e1)

      case Factor(clause, p1, _, sub) =>
        val (str1, e1) = tex( p1, ids, edges)

        (str1 + "\\RL{Factor} \n\\UI{" + f(clause.negative) + "}{" + f(clause.positive) +"}",   e1)
      case Variant(clause, p1, sub) =>
        val (str1, e1) = tex( p1, ids, edges)

        (str1 + "\\RL{Variant} \n\\UI{" + f(clause.negative) + "}{" + f(clause.positive) +"}",   e1)

      case InitialClause(clause) => ("\\AX{" + f(clause.negative) + "}{"+ f(clause.positive) +"}\n", edges)

      case _ => ("", edges)
    }
  }

  def asGraphViz(p : ResolutionProof[Clause]) : String = {
    val ids = createMap(p,1, Map[Clause, Int]())._1

    "digraph resproof {\n graph [rankdir=TB]; node [shape=box];\n" +
      (ids.keys.foldLeft ("")((str, clause) => str+ "v" + ids(clause) +" [label=\""+clause+"\"];\n")) +
      gv(p, ids, List())._1 +
      "}\n"
  }
  def gv(p : ResolutionProof[Clause], ids : Map[Clause, Int], edges : List[List[Int]] )
  : (String, List[List[Int]]) = p match {
    case Resolution(clause, p1, p2, occ1, occ2, subst) =>
      val (str1, e1) = gv( p1, ids, edges)
      val (str2, e2) = gv( p2, ids, e1)
      val triple = List(ids(clause), ids(p1.vertex), ids(p2.vertex))
      if (e2 contains (triple))
        (str1 + str2, e2)
      else
        (str1 + str2 +
          "v"+ids(p1.vertex)+" -> v"+ids(clause) + "[label=\"Res "+ occ1 + "\"];\n" +
          "v"+ids(p2.vertex)+" -> v"+ids(clause) + "[label=\"Res "+ occ2 + "\"];\n\n",
          triple :: e2)


    case Paramodulation(clause, p1, p2, occ1, occ2, subst) =>
      val (str1, e1) = gv( p1, ids, edges)
      val (str2, e2) = gv( p2, ids, e1)
      val triple = List(ids(clause), ids(p1.vertex), ids(p2.vertex))
      if (e2 contains (triple))
        (str1 + str2, e2)
      else
        (str1 + str2 +
          "v"+ids(p1.vertex)+" -> v"+ids(clause) + "[label=\"Para "+ occ1 + "\"];\n" +
          "v"+ids(p2.vertex)+" -> v"+ids(clause) + "[label=\"Para "+ occ2 + "\"];\n\n",
          triple :: e2)

    case Factor(clause, p1, occs, sub) =>
      val (str1, e1) = gv( p1, ids, edges)
      val triple = List(ids(clause), ids(p1.vertex))
      if (e1 contains (triple))
        (str1, e1)
      else
        (str1 +
          "v"+ids(p1.vertex)+" -> v"+ids(clause) + "[label=\"Factor "+ occs.map(_.mkString(", ")).mkString("(","; ",")") + "\"];\n\n",
          triple :: e1)
    case Variant(clause, p1, sub) =>
      val (str1, e1) = gv( p1, ids, edges)
      val triple = List(ids(clause), ids(p1.vertex))
      if (e1 contains (triple))
        (str1, e1)
      else
        (str1 +
          "v"+ids(p1.vertex)+" -> v"+ids(clause) + "[label=\"Variant "+ sub.toString().replaceFirst("Map","") + "\"];\n\n",
          triple :: e1)

    case Instance(clause, p1, sub) =>
      val (str1, e1) = gv( p1, ids, edges)
      val triple = List(ids(clause), ids(p1.vertex))
      if (e1 contains (triple))
        (str1, e1)
      else
        (str1 +
          "v"+ids(p1.vertex)+" -> v"+ids(clause) + "[label=\"Instance "+ sub.toString().replaceFirst("Map","") + "\"];\n\n",
          triple :: e1)

    case InitialClause(clause) => ("", edges) //"v" + ids(clause) +" [label=\""+clause+"\"];\n\n"

    case _ => ("", edges)
  }

  def apply(indent : String, p : ResolutionProof[Clause], ids : Map[Clause, Int]) : String = p match {
    case Resolution(clause, p1, p2, occ1, occ2, subst) =>
      indent + "(" + ids(clause) +") Resolution(["+clause+"] aux1=["+ occ1.formula + "] aux2=["+occ2.formula + "] sub=" + subst + ")\n" +
        apply("  "+indent, p1, ids) + apply("  "+indent, p2, ids)
    case Paramodulation(clause, p1, p2, occ1, occ2, subst) =>
      indent + "(" + ids(clause) + ") Paramodulation(["+clause+"] aux1=["+ occ1.formula + "] aux2=["+occ2.formula + "])\n" +
        apply("  "+indent, p1, ids) + apply("  "+indent, p2, ids)
    case Factor(clause, p1, occs, sub) =>
      indent + "(" + ids(clause) + ") Factor(["+clause+"] auxs="+ occs.map(_.map((x:FormulaOccurrence) => x.formula)).mkString("[","; ","]") + ")\n" +
        apply("  "+indent, p1, ids)
    case Variant(clause, p1, sub) =>
      indent + "(" + ids(clause) + ") Variant(["+clause+"])\n" +
        apply("  "+indent, p1, ids)
    case Instance(clause, p1, sub ) =>
      indent + "(" + ids(clause) + ") Instance(["+clause+"] sub=" +sub+ ")\n" +
        apply("  "+indent, p1, ids)
    case InitialClause(clause) => indent+ "(" + ids(clause) +") InitialClause(["+clause+"])\n\n"

    case _ => indent + "(need to handle " + p.getClass + " -- " + "" + ")\n"
  }
}



}
