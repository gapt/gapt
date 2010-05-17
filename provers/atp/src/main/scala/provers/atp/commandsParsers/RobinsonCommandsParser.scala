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
import at.logic.calculi.resolution.robinson._
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.replacements._
import at.logic.language.fol.FOLExpression

package robinson {
  // commands for robinson resolution
  case object FactorCom extends Com
  case object ResolveCom extends Com
  case object ParamodulateCom extends Com
  case object ParamodulateOnLiteralCom extends Com

  case class ResolventReply(resolvent: ResolutionProof[Clause]) extends ResultedClauseReply(resolvent)
  case class ParamodulantReply(paramodulant: ResolutionProof[Clause]) extends ResultedClauseReply[Clause](paramodulant)

  case object NoResolventReply extends NoResultedClauseReply
    case object NoParamodulantReply extends NoResultedClauseReply

  case class ApplyOnAllFactorsCom(ls: List[Command]) extends Com
  //case class ApplyOnAllClausePairsOnLiteralPairs(ls: List[Command]) extends Command
  case object CreateVariantCom extends Com

// default commands streams
  object AutomatedFOLStream {
    def apply(timeLimit: Long,
              clausesList: List[Clause],
              refCreator: at.logic.utils.ds.PublishingBuffer[Clause] => at.logic.provers.atp.refinements.Refinement[Clause],
              subsumCreator: at.logic.utils.ds.PublishingBuffer[Clause] => at.logic.algorithms.subsumption.managers.SubsumptionManager): Stream[Command] =
      Stream.cons(SetTimeLimit(timeLimit),
      Stream.cons(SetClausesCom(clausesList),
      Stream.cons(SetRefinementCom(refCreator),
      Stream.cons(SetSubsumptionManagerCom(subsumCreator),
      Stream.cons(SetCommandsParserCom(RobinsonCommandsParser), rest)))))
    def rest: Stream[Command] = Stream(
      GetClausesCom, CreateVariantCom, AndCom(
        ApplyOnAllPolarizedLiteralPairsCom(ResolveCom::ApplyOnAllFactorsCom(IfNotTautologyCom::IfNotForwardSubsumedCom::BackwardSubsumptionCom::InsertCom::Nil)::Nil)::Nil,
        ApplyOnAllPositiveEitherLiteralPairsCom(IfFirstLiteralIsEqualityCom::ApplyOnAllSecondLiteralNonVarSubterms(ParamodulateCom::IfNotTautologyCom::IfNotForwardSubsumedCom::BackwardSubsumptionCom::InsertCom::Nil)::Nil)::Nil)
    ).append(rest)
  }
}

import robinson._

object RobinsonCommandsParser extends CommandsParser with at.logic.utils.logging.Logger {
  
  var unifAlg: UnificationAlgorithm[LambdaExpression] = at.logic.algorithms.unification.fol.FOLUnificationAlgorithm.asInstanceOf[UnificationAlgorithm[LambdaExpression]]

  def parse(combinedCommand: Command, currentCommand: Command): Command = (combinedCommand, currentCommand) match {
    case (a, SetUnificationAlgorithmCom(alg)) => unifAlg = alg; a
    case (GotClausesPairReply((c1, c2)), CreateVariantCom) => GotClausesPairReply((Variant(c1.asInstanceOf[ResolutionProof[Clause]]), Variant(c2.asInstanceOf[ResolutionProof[Clause]])))
    // always put positive index first and negative index second
    case (GotClausesPairReply((s1, s2)), ApplyOnAllPolarizedLiteralPairsCom(commands)) => {
      val c1 = s1.asInstanceOf[ResolutionProof[Clause]]
      val c2 = s2.asInstanceOf[ResolutionProof[Clause]]
      AppendCommandsCom(
      (for (i <- 0 to c1.root.negative.size - 1; j <- 0 to c2.root.positive.size - 1) yield (j + c2.root.negative.size, i))
          .flatMap(x => ApplyOnLiteralPositionCom(x, (c2, c1)) :: commands) ++
        (for (i <- 0 to c1.root.positive.size - 1; j <- 0 to c2.root.negative.size - 1) yield (i + c1.root.negative.size,j))
          .flatMap(x => ApplyOnLiteralPositionCom(x, (c1, c2)) :: commands)
      )
    }
    // first terms is the certainly positive
    case (GotClausesPairReply((s1, s2)), ApplyOnAllPositiveEitherLiteralPairsCom(commands)) => {
      val c1 = s1.asInstanceOf[ResolutionProof[Clause]]
      val c2 = s2.asInstanceOf[ResolutionProof[Clause]]
      AppendCommandsCom(
        (for (i <- 0 to c1.root.positive.size - 1; j <- 0 to (c2.root.negative.size+c2.root.positive.size) - 1) yield (i + c1.root.negative.size,j))
          .flatMap(x => ApplyOnLiteralPositionCom(x, (c1, c2)) :: commands) ++
        (for (j <- 0 to c2.root.positive.size - 1; i <- 0 to (c1.root.negative.size+c1.root.positive.size) - 1) yield (j + c2.root.negative.size,i))
          .flatMap(x => ApplyOnLiteralPositionCom(x, (c2, c1)) :: commands)
      )
    }
    case (a @ ApplyOnLiteralPositionCom((i,j),(c1,c2)), IfFirstLiteralIsEqualityCom) => c1.root(i) match {
      case Atom(ConstantStringSymbol("="), _::_::Nil) => a
      case _ => NoParamodulantReply
    }
    case (NoParamodulantReply, ApplyOnAllSecondLiteralNonVarSubterms(commands)) => AppendCommandsCom(NoParamodulantReply::commands)
    case (NoParamodulantReply, ParamodulateCom) => NoParamodulantReply
    case (ApplyOnLiteralPositionCom((i,j),(c1,c2)), ApplyOnAllSecondLiteralNonVarSubterms(commands)) => {
      // compute all subterms of c2.root(j)
      val t = c2.root(j)
      AppendCommandsCom(
        getAllPositions(t).flatMap(pos => ApplyOnSecondSubtermCom((i,j), (c1,c2), pos._1, pos._2) :: commands)
      )
    }
    // dummy for skipping the EmptyCom before applying to specific literals
    case (EmptyCom, a) => a
    case (ApplyOnLiteralPositionCom((i,j),(s1,s2)), ResolveCom) => {
      val c1 = s1.asInstanceOf[ResolutionProof[Clause]]
      val c2 = s2.asInstanceOf[ResolutionProof[Clause]]
      val mgus = unifAlg.unify(c1.root(i), c2.root(j))
      if (mgus.isEmpty) {
        NoResolventReply
      } else {
          val sub = mgus.first
          ResolventReply(Resolution(c1,c2,i,j,sub))
        //TODO: finitary unification
      }
    }
    case (ApplyOnSecondSubtermCom((i,j),(s1,s2), pos, t), ParamodulateCom) => {
      val c1 = s1.asInstanceOf[ResolutionProof[Clause]]
      val c2 = s2.asInstanceOf[ResolutionProof[Clause]]
      c1.root(i) match {
      // try to unify t and each of the sides of c1(i)
      case Atom(ConstantStringSymbol("="), a::b::Nil) =>
        val mgus = unifAlg.unify(a, t)
        if (mgus.isEmpty) {
          NoParamodulantReply
        } else {
          val sub = mgus.first
          ParamodulantReply(Paramodulation(c1,c2,i,j,Replacement(pos, b.asInstanceOf[HOLExpression]).apply(c2.root(j)).asInstanceOf[HOLFormula], sub))
        //TODO: finitary unification
        }

      case _ => NoParamodulantReply
    }}

    // generate all other resolvents that corresponds to two possible factors of the two parent clauses at the specific index
    case (r @ ResolventReply(Resolution(cls, pr1, pr2, id1Pos, id2, sub)), ApplyOnAllFactorsCom(commands)) => {
      val id1 = id1Pos - pr1.root.negative.size // computes the id of the positive resolvent id (the negative is just id2)
      val cl1 = pr1.root.positive // the set of all positive literals
      val cl1Ind = for (i <- cl1.indices; if i != id1) yield i // the set of all indices in the above set except the resolvent id
      val factors1 = computeFactors(cl1, cl1Ind, cl1(id1), sub.asInstanceOf[Substitution[LambdaExpression]], Nil) // all the factors in the positive literals of the first clause
      val cl2 = pr2.root.negative // the set of all negative literals of the second clause
      val cl2Ind = for (i <- cl2.indices; if i != id2) yield i // the set of their indices except the resolvent id
      val factors2 = computeFactors(cl2, cl2Ind, cl2(id2), sub.asInstanceOf[Substitution[LambdaExpression]], Nil) // all their factors
      AppendCommandsCom((r::commands) ++
        (for {
          (ls1,sub1) <- (List(), Substitution())::factors1
          (ls2,sub2) <- (List(), Substitution())::factors2
          if !(ls1.isEmpty && ls2.isEmpty)
        } yield (ResolventReply(
            {val r = Resolution(
              (if (ls1.isEmpty) pr1 else {debug("factor of " + pr1.root.toString + " without indices " + ls1.map(x => pr1.root.negative.size + x) + " and with substitution " + sub1);(Factor(pr1, ls1.map(x => pr1.root.negative.size + x), sub1))}),
              (if (ls2.isEmpty) pr2 else {debug("factor of " + pr2.root.toString + " without indices " + ls2 + " and with substitution " + sub2);(Factor(pr2, ls2, sub2))}),
              comInd(id1Pos, ls1), comInd(id2, ls2), sub)
            debug("resolvent of factors: " + r.root); r})
          )).flatMap(x => x::commands))
    }
    case (NoResolventReply, ApplyOnAllFactorsCom(commands)) => AppendCommandsCom(NoResolventReply::commands)
    case _ => Console.println(combinedCommand + " - " + currentCommand); FailureReply
  }

  // computes factors, calling recursively to smaller sets
  // it is assumed in each call that the sub from the previous round is already applied to the formulas
  def computeFactors[T <: LambdaExpression](lits: List[T], indices: List[Int], form: T, sub: Substitution[T], usedIndices: List[Int]): List[Tuple2[List[Int], Substitution[T]]] = indices match {
    case Nil => Nil
    case x::Nil =>
      val mgus = unifAlg.unify(sub(lits(x).asInstanceOf[T]), sub(form.asInstanceOf[T]))
      mgus match {
        case Nil => Nil
        case List(sub2 : Substitution[T]) =>
        val subst : Substitution[T] = (sub2 compose sub)
        List( (x::usedIndices, subst) )
        //todo: finitary unification
      }
    case x::ls => {
        val facts: List[Tuple2[List[Int], Substitution[T]]] = computeFactors(lits, ls, form, sub, usedIndices)
        facts.foldLeft(Nil: List[Tuple2[List[Int], Substitution[T]]])((ls,a) => ls
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
