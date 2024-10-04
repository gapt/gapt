package gapt.formats.lean

import gapt.expr._
import gapt.expr.formula._
import gapt.expr.formula.fol._
import gapt.expr.formula.hol.universalClosure
import gapt.proofs._
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules._
import gapt.proofs.resolution._

object LeanExporter {

  var LeanHypCounter = 0

  enum formulaPrinting:
    case none, commented, full

  /**
   * Exports a Lean tactics script from an LKProof of a sequent of the form
   * ∀ x_1 ... ∀ x_n E_1 :- E_2
   * where E_1 and E_2 are equations, E_1 contains only x_1, ..., x_n and
   * E_2 is variable-free.
   **/
  def apply(proof: LKProof): String = {
    initHypName()
    val LeanHyp = Sequent(Vector(newHypName()), Vector("target"))
    apply(proof, LeanHyp)
  }

  /**
   * Exports a Lean proof from a resolution proof
   **/
  // FIXME: currently this expands a dag to a tree -> keep dag form!
  // TODO refactor: separate the two differnt algorithms into different objects?
  def apply(proof: ResolutionProof, fp: formulaPrinting): String = {
    initHypName()

    val (initHyps, leanString, hypName) = apply_rec(proof, fp)

    val concEq = proof.conclusion(Suc(0))
    val concFreeVars = freeVariablesFromLToR(concEq)
    val concEqClosed = All.Block(concFreeVars, concEq)

    leanString + "  by exact " + hypName
  }

  /**
   * returns
   * 1. lean strings for hypotheses
   * 2. lean string for proof
   * 3. name of hypothesis of last step
   **/
  def apply_rec(proof: ResolutionProof, fp: formulaPrinting): (Set[String], String, String) = {
    val concEq = proof.conclusion(Suc(0))
    val concFreeVars = freeVariablesFromLToR(concEq)
    val concEqClosed = All.Block(concFreeVars, concEq)

    proof match {
      case AllR(subproof, idx, variable) => {
        // FIXME: this assumes that the entire proof uses only a single equation as assumption
        val str = "(h: " + exportFormulaWithG(concEqClosed, formulaPrinting.full) + ")"
        val hypName = newHypName()
        (Set(str), "  have " + hypName + " := h\n", hypName)
      }

      case Subst(subproof, subst) => {
        val premEq = subproof.conclusion(Suc(0))
        val premFreeVars = freeVariablesFromLToR(premEq)
        val instTerms = subst(premFreeVars).asInstanceOf[List[FOLTerm]] // FIXME

        val (initHyps, subLeanString, subHypName) = apply_rec(subproof, fp)

        val hypName = newHypName()
        val leanLine = "  have " + hypName + ": "
          + exportFormulaWithG(concEqClosed, fp) + " := "
          + "fun (" + concFreeVars.mkString(" ") + " : G) =>"
          + exportShowFormulaFromWithG(concEq, fp)
          + " " + subHypName + " "
          + instTerms.map(t => exportFOLTerm(t)).mkString(" ") + " -- subst\n"

        (initHyps, subLeanString + leanLine, hypName)
      }

      case Flip(subproof, idx) => {
        val premEq = subproof.conclusion(Suc(0))
        val premFreeVars = freeVariablesFromLToR(premEq)

        val (initHyps, subLeanString, subHypName) = apply_rec(subproof, fp)

        val hypName = newHypName()
        val leanLine = "  have " + hypName + ": "
          + exportFormulaWithG(concEqClosed, fp) + " := "
          + "fun (" + concFreeVars.mkString(" ") + " : G) =>"
          + exportShowFormulaFromWithG(concEq, fp)
          + " Eq.symm (" + subHypName + " "
          + premFreeVars.mkString(" ") + ") -- flip\n"

        (initHyps, subLeanString + leanLine, hypName)
      }

      case Paramod(leftProof, eqIdx, clockwise, rightProof, auxIdx, context) => {
        val rightEq = rightProof.conclusion(auxIdx)
        val rightFreeVars = freeVariablesFromLToR(rightEq)
        val leftEq = leftProof.conclusion(eqIdx)
        val leftFreeVars = freeVariablesFromLToR(leftEq)
        val eqsides = leftEq match { case FOLAtom("=", as) => as }
        val lhsLean = if (clockwise) eqsides(0) else eqsides(1)
        val rwpos = getRewritePositions(lhsLean, context.asInstanceOf[Abs]) // FIXME
        val rwposidcs = getPositiveIndices(rwpos)

        val (leftHyps, leftLeanString, leftHypName) = apply_rec(leftProof, fp)
        val (rightHyps, rightLeanString, rightHypName) = apply_rec(rightProof, fp)
        // assert( leftHyps == rightHyps ) // should come from the same unique equation

        val hypName = newHypName()
        val leanLine = "  have " + hypName + ": "
          + exportFormulaWithG(concEqClosed, fp) + " := "
          + "fun (" + concFreeVars.mkString(" ") + " : G) => "
          + "by (have " + rightHypName + "' := "
          + rightHypName + " " + rightFreeVars.mkString(" ") + ";"
          + " nth_rewrite " + rwposidcs.mkString(" ") + " "
          + "[" + (if (clockwise) "" else "←") + leftHypName + " " + leftFreeVars.mkString(" ") + "]"
          + " at " + rightHypName + "';"
          + " exact " + rightHypName + "') -- paramod\n"

        (leftHyps, leftLeanString + rightLeanString + leanLine, hypName)
      }

      case _ => (Set(), "unsupported inference rule has been used", "")
    }

  }

  /**
   * move chain of paramodulations (plus possibly a flip) from the rightmost branch to the left
   *
   * This terminates because the rightmost branch decreases in size with each call.
   **/
  def moveParamodsLeft(proof: ResolutionProof): ResolutionProof = {
    proof match {
      case Paramod(_, _, _, _, _, _)                => proof
      case Flip(_, _)                               => proof
      case Resolution(subProof1, idx1, Input(_), _) => subProof1
      case Resolution(subProof1, idx1, Flip(Input(_), _), _) => {
        moveParamodsLeft(Flip(subProof1, idx1))
      }
      case Resolution(leftProof, leftIdx, Paramod(middleProof, eqIdx, clockwise, rightProof, _, context), _) => {
        moveParamodsLeft(Resolution(Paramod(middleProof, eqIdx, !clockwise, leftProof, leftIdx, context), Suc(0), rightProof, Ant(0)))
      }
    }
  }

  /**
   * Exports a Lean tactics script from a simple equational LKProof
   * @param proof the LK proof to be exported
   * @param LeanHyp names of Lean hypotheses
   * @param level the current indentation level
   * @param mkDot make a dot (for a Lean case distinction)
   *
   * The invariant of the export is: at every call of apply, the current end-sequent
   * of proof is exactly the goal of the Lean script exported thus far (looking bottom-up).
   * LeanHyp maps SequentIndices of the antecedens of the end-sequent of p to the names of
   * Lean hypotheses (the succedent is always ("target")).
   **/
  def apply(proof: LKProof, LeanHyp: Sequent[String], level: Int = 1, mkDot: Boolean = false): String = {
    assert(LeanHyp.lengths == proof.endSequent.lengths)

    val indent = if (mkDot)
      "  " * (level - 1) + "· "
    else
      "  " * level

    val rec = proof match {
      case LogicalAxiom(a) =>
        "exact " + LeanHyp(Ant(0)) + " -- ax\n"

      case ReflexivityAxiom(a) =>
        "rfl -- refl\n"

      case p @ ForallLeftRule(subProof, aux, a: Formula, term: Expr, v: Var) => {
        val auxHypName = newHypName()
        val tacString = "have " + auxHypName + ": " + exportFormula(p.auxFormula)
          + " := by apply " + LeanHyp(proof.mainIndices(0)) + " -- ∀:l\n"
          + "  " * level + "clear " + LeanHyp(proof.mainIndices(0)) + "\n"

        val premLeanHyp = LeanHyp.updated(proof.mainIndices(0), auxHypName)
        tacString + apply(subProof, premLeanHyp, level)
      }

      case p @ ContractionLeftRule(subProof, aux1, aux2) => {
        val seqconn = p.getSequentConnector
        val midx = proof.mainIndices(0)

        val hypAux = newHypName()
        // FIXME: avoid DUMMY -- is not needed by parent
        // Note: p.aux1 could also be used - this is fully symmetric
        val premLeanHyp = seqconn.parent(LeanHyp, "DUMMY").updated(p.aux2, hypAux)

        "have " + hypAux + " := " + LeanHyp(midx) + " -- c:l\n"
          + apply(subProof, premLeanHyp, level)
      }

      case p @ WeakeningLeftRule(subProof, formula) => {
        val weakHypName = LeanHyp(proof.mainIndices(0))
        val premLeanHyp = p.getSequentConnector.parent(LeanHyp, "DUMMY") // FIXME: avoid DUMMY

        "clear " + weakHypName + " -- w:l\n" + apply(subProof, premLeanHyp, level)
      }

      case p @ EqualityLeftRule(subProof, eq, aux, replacementContext) => {
        val seqConn = p.occConnectors(0)
        val eqLeanHyp = LeanHyp(seqConn.child(eq))
        val auxLeanHyp = LeanHyp(seqConn.child(aux))
        val equation = subProof.endSequent(eq)
        val (tmpr, tmpl, clockwise) = equation match {
          case Eq(s, t) => {
            val insertS = BetaReduction.betaNormalize(App(replacementContext, s))
            val insertT = BetaReduction.betaNormalize(App(replacementContext, t))
            if (insertS == p.auxFormula) {
              (s, t, true)
            } else if (insertT == p.auxFormula) {
              (t, s, false)
            } else {
              assert(false)
            }
          }
        }
        // FIXME there must be a better way to do this
        val rhsLean = tmpr.asInstanceOf[FOLTerm]
        val lhsLean = tmpl.asInstanceOf[FOLTerm]

        val rwpos = getRewritePositions(lhsLean, replacementContext)
        val rwposidcs = getPositiveIndices(rwpos)
        val hypAuxParent = newHypName()
        val premLeanHyp = seqConn.parent(LeanHyp, "DUMMY").updated(aux, hypAuxParent) // FIXME: avoid DUMMY

        "have " + hypAuxParent + ": " + exportFormula(p.auxFormula) + " := by -- eq:l\n"
          + "  " * level + "  nth_rw " + getListString(rwposidcs) + " "
          + "[" + (if (clockwise) "←" else "") + eqLeanHyp + "] at " + auxLeanHyp + "\n"
          + "  " * level + "  exact " + auxLeanHyp + "\n"
          + apply(subProof, premLeanHyp, level)
      }

      case p @ EqualityRightRule(subProof, eq, aux, replacementContext) => {
        val auxisrefl = p.auxFormula match {
          case Eq(t, s) => if (s == t) true else false
          case _        => false
        }

        val seqConn = p.occConnectors(0)
        val eqLeanHyp = LeanHyp(seqConn.child(eq))
        val equation = subProof.endSequent(eq)
        // FIXME: don't copy this - refactor - generic equality handling for both eq rules
        val (tmpr, tmpl, clockwise) = equation match {
          case Eq(s, t) => {
            val insertS = BetaReduction.betaNormalize(App(replacementContext, s))
            val insertT = BetaReduction.betaNormalize(App(replacementContext, t))
            if (insertS == p.auxFormula) {
              (s, t, true)
            } else if (insertT == p.auxFormula) {
              (t, s, false)
            } else {
              assert(false)
            }
          }
        }
        // FIXME there must be a better way to do this
        val rhsLean = tmpr.asInstanceOf[FOLTerm]
        val lhsLean = tmpl.asInstanceOf[FOLTerm]

        val rwpos = getRewritePositions(lhsLean, replacementContext)
        val rwposidcs = getPositiveIndices(rwpos)

        "nth_rw " + getListString(rwposidcs) + " "
          + "[" + (if (clockwise) "←" else "") + eqLeanHyp + "] -- eq:r\n"
          + (if (auxisrefl) "" else apply(subProof, LeanHyp, level))
        // do not continue if auxisrefl because the nth_rw tactic will solve the goal already
      }

      case p @ CutRule(leftSubProof, aux1, rightSubProof, aux2) => {
        val hypCutFormula = newHypName()
        val lsocc = p.getLeftSequentConnector
        val leftLeanHyp = lsocc.parent(LeanHyp, "target")
        val rsocc = p.getRightSequentConnector
        val rightLeanHyp = rsocc.parent(LeanHyp, hypCutFormula)

        val head = "have " + hypCutFormula + ": " + exportFormula(p.cutFormula) + " -- cut\n"
        val left = apply(leftSubProof, leftLeanHyp, level + 1, true)
        val right = apply(rightSubProof, rightLeanHyp, level + 1, true)

        head + left + right
      }

      case _ =>
        "sorry -- unsupported inference rule has been used"
    }
    indent + rec
  }

  def exportShowFormulaFromWithG(f: Formula, fp: formulaPrinting): String = fp match {
    case formulaPrinting.none      => ""
    case formulaPrinting.commented => " show " + exportFormulaWithG(f, fp) + " from"
    case formulaPrinting.full      => " show " + exportFormulaWithG(f, fp) + " from"
  }

  def exportFormulaWithG(f: Formula, fp: formulaPrinting): String = f match {
    case All.Block(xs, FOLAtom("=", as)) => {
      val fstring = if (xs.isEmpty)
        exportFOLTerm(as(0)) + " = " + exportFOLTerm(as(1))
      else
        "∀ (" + xs.mkString(" ") + ": G), "
          + exportFOLTerm(as(0)) + " = " + exportFOLTerm(as(1))

      fp match {
        case formulaPrinting.none      => "_"
        case formulaPrinting.commented => "_ /- " + fstring + " -/"
        case formulaPrinting.full      => fstring
      }
    }
  }

  def exportFormula(f: Formula): String = f match {
    case All.Block(xs, FOLAtom("=", as)) => {
      if (xs.isEmpty)
        exportFOLTerm(as(0)) + " = " + exportFOLTerm(as(1))
      else
        "∀ " + getVarListString(xs) + ", " + exportFOLTerm(as(0)) + " = " + exportFOLTerm(as(1))
    }
  }

  def exportFOLTerm(t: FOLTerm): String = t match {
    case FOLFunction("f", as) =>
      "( " + exportFOLTerm(as(0)) + " ◇ " + exportFOLTerm(as(1)) + " )"
    case FOLVar(v) =>
      v
    case FOLConst(c) =>
      c
  }

  def initHypName() = {
    LeanHypCounter = 0
  }

  def newHypName(): String = {
    val hn = "h" + LeanHypCounter
    LeanHypCounter += 1
    hn
  }

  def getRewritePositions(lhs: FOLTerm, replCont: Abs): List[Boolean] = {
    replCont match {
      case Abs(v, f) => {
        f match {
          case FOLAtom("=", as) => {
            getRewritePositions(lhs, as(0), v) ++ getRewritePositions(lhs, as(1), v)
          }
        }
      }
    }
  }

  /**
   * returns List[Boolean] whose length is the number of occurrences of lhs + the number
   * of occurrences of v in replTerm. The i-th element of the return value is true
   * iff the i-th occurrence of either lhs or v is one of v.
   **/
  def getRewritePositions(lhs: FOLTerm, replTerm: FOLTerm, v: Var): List[Boolean] = {
    if (replTerm == lhs)
      List(false)
    else if (replTerm == v)
      List(true)
    else
      replTerm match {
        case FOLFunction("f", as) =>
          getRewritePositions(lhs, as(0), v) ++ getRewritePositions(lhs, as(1), v)
        case FOLConst(_) => List()
        case FOLVar(_)   => List()
      }
  }

  def getPositiveIndices(L: List[Boolean]): List[Int] = {
    // FIXME: there must be a better way to do this in Scala
    var rv = List[Int]()
    for (i <- 0 until L.length) {
      if (L(i)) rv = rv :+ (i + 1)
    }
    rv
  }

  def getListString(L: List[Int]): String = { // FIXME
    L.mkString(" ")
  }

  def getVarListString(L: List[Var]): String = { // FIXME
    L.mkString(" ")
  }

  def freeVariablesFromLToR(F: Formula): List[Var] = F match {
    case FOLAtom("=", as) => {
      var vars = freeVariablesFromLToR(as(0))
      val varsRight = freeVariablesFromLToR(as(1))

      for (i <- 0 until varsRight.length)
        if (!vars.contains(varsRight(i))) vars = vars :+ varsRight(i)

      vars
    }
  }

  def freeVariablesFromLToR(t: FOLTerm): List[Var] = t match {
    case FOLFunction("f", as) => {
      var vars = freeVariablesFromLToR(as(0))
      val varsRight = freeVariablesFromLToR(as(1))

      for (i <- 0 until varsRight.length)
        if (!vars.contains(varsRight(i))) vars = vars :+ varsRight(i)

      vars
    }
    case v @ FOLVar(_) => List(v)
    case FOLConst(c)   => List()
  }
}
