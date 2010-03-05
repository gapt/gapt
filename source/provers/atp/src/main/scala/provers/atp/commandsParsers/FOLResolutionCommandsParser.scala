/*
 * FOLResolutionCommandsParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.commandsParsers

import at.logic.provers.atp.commands._
import at.logic.algorithms.unification.UnificationAlgorithm
import at.logic.language.lambda.substitutions._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.calculi.resolution.base._
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._

trait FOLResolutionCommandsParser extends CommandsParser {
  var unifAlg: UnificationAlgorithm = at.logic.algorithms.unification.fol.FOLUnificationAlgorithm

  def parse(combinedCommand: Command, currentCommand: Command): Command = (combinedCommand, currentCommand) match {
    case (a, SetUnificationAlgorithmCom(alg)) => unifAlg = alg; a
    case (GotClausesPairCom((c1, c2)), CreateVariantCom) => GotClausesPairCom(Variant(c1), Variant(c2))
    // always put positive index first and negative index second
    case (GotClausesPairCom((c1, c2)), ApplyOnAllPolarizedLiteralPairsCom(commands)) => {
      AppendCommandsCom(
      (for (i <- 0 to c1.root.negative.size - 1; j <- 0 to c2.root.positive.size - 1) yield (j + c2.root.negative.size, i))
          .flatMap(x => ApplyOnLiteralPositionCom(x, (c2, c1)) :: commands) ++
        (for (i <- 0 to c1.root.positive.size - 1; j <- 0 to c2.root.negative.size - 1) yield (i + c1.root.negative.size,j))
          .flatMap(x => ApplyOnLiteralPositionCom(x, (c1, c2)) :: commands)
      )
    }
    // first terms is the certainly positive
    case (GotClausesPairCom((c1, c2)), ApplyOnAllPositiveEitherLiteralPairsCom(commands)) => {
      AppendCommandsCom(
        (for (i <- 0 to c1.root.positive.size - 1; j <- 0 to (c2.root.negative.size+c2.root.positive.size) - 1) yield (i + c1.root.negative.size,j))
          .flatMap(x => ApplyOnLiteralPositionCom(x, (c1, c2)) :: commands) ++
        (for (j <- 0 to c2.root.positive.size - 1; i <- 0 to (c1.root.negative.size+c1.root.positive.size) - 1) yield (j + c2.root.negative.size,i))
          .flatMap(x => ApplyOnLiteralPositionCom(x, (c2, c1)) :: commands)
      )
    }
    case (a @ ApplyOnLiteralPositionCom((i,j),(c1,c2)), IfFirstLiteralIsEqualityCom) => c1.root(i) match {
      case Atom(ConstantStringSymbol("="), _::_::Nil) => a
      case _ => NoParamodulantCom
    }
    case (NoParamodulantCom, ApplyOnAllSecondLiteralSubterms(commands)) => AppendCommandsCom(NoParamodulantCom::commands)
    case (NoParamodulantCom, ParamodulateCom) => NoParamodulantCom
    /*case (ApplyOnLiteralPositionCom((i,j),(c1,c2)), ApplyOnAllSecondLiteralSubterms(commands)) => {
      // compute all subterms of c2.root(j)
      AppendCommandsCom(
        (for (i <- 0 to c1.root.positive.size - 1; j <- 0 to (c2.root.negative.size+c2.root.positive.size) - 1) yield (i + c1.root.negative.size,j))
          .flatMap(x => ApplyOnLiteralPositionCom(x, (c2, c1)) :: commands) ++
        (for (j <- 0 to c2.root.positive.size - 1; i <- 0 to (c1.root.negative.size+c1.root.positive.size) - 1) yield (j + c2.root.negative.size,i))
          .flatMap(x => ApplyOnLiteralPositionCom(x, (c1, c2)) :: commands)
      )
    }*/
    // dummy for skipping the EmptyCom before applying to specific literals
    case (EmptyCom, a) => a
    case (ApplyOnLiteralPositionCom((i,j),(c1,c2)), ResolveCom) => {
      unifAlg.unify(c1.root(i), c2.root(j)) match {
        case None => NoResolventCom
        case Some(sub) => ResolventCom(Resolution(c1,c2,i,j,sub))
      }
    }
    /*case (ApplyOnLiteralPositionCom((i,j),(c1,c2)), ParamodulateOnLiteralCom()) => {
      if (i >= c1.root.negative.size) { // check the case that c1(i) is an equality and positive
        // for every subterm of c2(j) try to unify it which each of the terms in c1(i) = (t=s)
        AppendCommandsCom(
          (for (i <- 0 to (c1.root.negative.size+c1.root.positive.size) - 1; j <- 0 to (c2.root.negative.size+c2.root.positive.size) - 1) yield (i, j))
              .flatMap(x => ApplyOnLiteralPositionCom(x, (c1, c2)) :: commands)
          )
      } else if (j >= c2.root.negative.size) { // check the case that c2(j) is an equality and positive

      } else NoParamodulantCom
      /*unifAlg.unify(c1.root(i), c2.root(j)) match {
        case None => NoResolventCom
        case Some(sub) => ResolventCom(Resolution(c1,c2,i,j,sub))
      }*/
    }*/
    // generate all other resolvents that corresponds to two possible factors of the two parent clauses at the specific index
    case (r @ ResolventCom(Resolution(cls, pr1, pr2, id1Pos, id2, sub)), ApplyOnAllFactorsCom(commands)) => {
      val id1 = id1Pos - pr1.root.negative.size
      val cl1 = pr1.root.positive
      val cl1Ind = for (i <- cl1.indices; if i != id1) yield i
      val factors1 = computeFactors(cl1, cl1Ind, cl1(id1), sub, Nil)
      val cl2 = pr2.root.negative
      val cl2Ind = for (i <- cl2.indices; if i != id2) yield i
      val factors2 = computeFactors(cl2, cl2Ind, cl2(id2), sub, Nil)
      AppendCommandsCom((r::commands) ++
        (for {
          (ls1,sub1) <- (List(), Substitution())::factors1
          (ls2,sub2) <- (List(), Substitution())::factors2
          if !(ls1.isEmpty && ls2.isEmpty)
        } yield (ResolventCom(Resolution(Factor(pr1, ls1.map(x => pr1.root.negative.size + x), sub1),Factor(pr2, ls2, sub2), comInd(id1, ls1), comInd(id2, ls2), sub)))
          ).flatMap(x => x::commands))
    }
    case (NoResolventCom, ApplyOnAllFactorsCom(commands)) => AppendCommandsCom(NoResolventCom::commands)
    case _ => Console.println(combinedCommand + " - " + currentCommand); FailureCom
  }

  // computes factors, calling recursively to smaller sets
  // it is assumed in each call that the sub from the previous round is already applied to the formulas
  def computeFactors(lits: List[Formula], indices: List[Int], form: Formula, sub: Substitution, usedIndices: List[Int]): List[Tuple2[List[Int], Substitution]] = indices match {
    case Nil => Nil
    case x::Nil => unifAlg.unify(sub(lits(x)), sub(form)) match {
      case None => Nil
      case Some(sub2) => (x::usedIndices, (sub2 compose sub))::Nil
    }
    case x::ls => {
        val facts: List[Tuple2[List[Int], Substitution]] = computeFactors(lits, ls, form, sub, usedIndices)
        facts.foldLeft(Nil: List[Tuple2[List[Int], Substitution]])((ls,a) => ls
            ++ computeFactors(lits, x::Nil, form, a._2, a._1)) ++ facts ++ computeFactors(lits, x::Nil, form, sub, usedIndices)
    }
  }
  // compute the new index after removal of literals with indices in the given list
  private def comInd(id: Int, ids: List[Int]) = ids.foldLeft(id)((newId,x) => if (x < id) (newId - 1) else newId)
      /*
        computeFactors(ls, form)
    
      val cl = pr.root
      val clInd = if (id < cl.negative.size)
          (for (i <- cl.negative.indices; if i != id) yield i)
        else (for (i <- cl.positive.indices; if i != id) yield i)
      for ()
  }*/
}

/*
    case (ApplyOnLiteralPositionCom((i,j),(c1,c2)), FactorizeCom) => {
        // factorize each clause on all literals with regard to i and j and do it recursively so factorization
        // of more than one literal is possible
        // then call ApplyOnLiteralPositionCom on each of the new clauses and with new indices according to the deletion
        EmptyCom
    }
    */
