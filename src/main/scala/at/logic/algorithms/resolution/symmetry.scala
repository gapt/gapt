package at.logic.algorithms.resolution

import scala.collection.immutable.HashMap
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.resolution.robinson._
import at.logic.language.fol.{Equation => FOLEquation, FOLTerm, FOLFormula, FOLExpression, Substitution}
import at.logic.calculi.resolution.{FClause, Clause}
import at.logic.algorithms.lk.{applySubstitution => applySub, CleanStructuralRules, CloneLKProof}

/**
  Sometimes, we have a resolution refutation of a set of clauses C
  and want a refutation of a set C', such that C' is C modulo applications
  of symmetry. This algorithm transforms a refutation of C to a refutation
  of C'.
**/
object fixSymmetry {

  private def getSymmetryMap( to: FClause, from: FSequent ) = {
    var err = false

    def createMap( from: Seq[FOLFormula], to: Seq[FOLFormula] ) = {
      to.foldLeft( HashMap[FOLFormula, FOLFormula]() )( (map, to_f) => {
        val from_f = from.find( from_f => (from_f == to_f) || ( (from_f, to_f) match
        {
          case (FOLEquation(from_l, from_r), FOLEquation(to_l, to_r)) if from_l == to_r && from_r == to_l => true
          case _ => false
        }))

        if ( from_f != None )
          map + (( from_f.get, to_f ))
        else {
          err = true
          map 
        }}
      )
  }

    val avail_pos = from.succedent.map( f => f.asInstanceOf[FOLFormula] )
    val avail_neg = from.antecedent.map( f => f.asInstanceOf[FOLFormula] )

    val neg_map = createMap( avail_neg, to.neg.map(_.asInstanceOf[FOLFormula]) )
    val pos_map = createMap( avail_pos, to.pos.map(_.asInstanceOf[FOLFormula]) )

    if (err)
      None
    else
      Some((neg_map, pos_map))
  }

  private def canDeriveBySymmetry( to: FClause, from: FSequent ) = getSymmetryMap( to, from ) match {
    case Some(_) => true
    case None => false
  }

  private def applySymm( p: RobinsonResolutionProof, f: FOLFormula, pos: Boolean ) =
  {
    val (left, right) = f match {
      case FOLEquation(l, r) => (l, r)
    }
    val newe = FOLEquation(right, left)
    val refl = FOLEquation(left, left)
    val s = Substitution()

    if (pos)
    {
      val irefl = InitialClause(Nil, refl::Nil)
      Paramodulation( p, irefl, f, refl, newe, s, pos)
    } else {
      val init = InitialClause( newe::Nil, newe::Nil )
      val init2 = InitialClause( newe::Nil, newe::Nil )
      val eq1 = Paramodulation( init, p, newe, f, refl, s, pos )
      val eq2 = Paramodulation( init2, eq1, newe, refl, newe, s, pos)
      Factor( eq2, newe, 3, pos, s)
  }
  }

  private def deriveBySymmetry( to: FClause, from: FSequent ) = {
    val (neg_map, pos_map) = getSymmetryMap( to, from ).get

    val init = InitialClause(from.antecedent.map(_.asInstanceOf[FOLFormula]), from.succedent.map(_.asInstanceOf[FOLFormula]))
    val s_neg = neg_map.keySet.foldLeft(init)( (p, f) => f match {
        case FOLEquation(_, _) if neg_map(f) != f => applySymm(p, f, false)
        case _ => p
      })

    pos_map.keySet.foldLeft(s_neg)( (p, f) => f match {
        case FOLEquation(_, _) if pos_map(f) != f => applySymm(p, f, true)
        case _ => p
    })
  }

  private def handleInitialClause( cls: FClause, cs: Seq[FSequent] ) =
    cs.find( c => canDeriveBySymmetry( cls, c ) ) match {
      case None => {
        InitialClause(cls)
      }
      case Some( c ) => {
        deriveBySymmetry( cls, c )
      }
    }

  def apply( p: RobinsonResolutionProof, cs: Seq[FSequent] ) : RobinsonResolutionProof = {
    rec(p)(cs)
  }

  def rec( p: RobinsonResolutionProof)(implicit cs: Seq[FSequent] ) : RobinsonResolutionProof = {
    var fac = false
    val res = p match {
      case InitialClause(cls) => handleInitialClause( cls.toFClause, cs )
     
      case Factor(r, p, a, s) => {
        fac = true 
        a match {
          case lit1 :: Nil => {
            val pos = p.root.succedent.contains(lit1.head)
            Factor(rec(p), lit1.head.formula, lit1.size, pos, s)
          }
          case lit1::lit2::Nil =>
            Factor(rec(p), lit1.head.formula, lit1.size, lit2.head.formula, lit2.size, s)
          case _ => throw new Exception("Factor rule for "+p.root+" does not have one or two primary formulas!")
        }
      }
      case Variant(r, p, s) => Variant( rec( p  ), s )
      case Resolution(r, p1, p2, a1, a2, s) => 
	Resolution( rec( p1 ), rec( p2 ), a1.formula.asInstanceOf[FOLFormula], a2.formula.asInstanceOf[FOLFormula], s )
      case Paramodulation(r, p1, p2, a1, a2, p, s) => 
        Paramodulation( rec( p1 ), rec( p2 ), a1.formula.asInstanceOf[FOLFormula], a2.formula.asInstanceOf[FOLFormula], p.formula.asInstanceOf[FOLFormula], s, p2.root.succedent.contains(a2))
      // this case is applicable only if the proof is an instance of RobinsonProofWithInstance
      case Instance(_,p,s) => Instance(rec(p),s)
    }
    (res.root.positive ++ res.root.negative).foreach( fo => assert(fo.formula.isInstanceOf[FOLFormula]))
    res
  }
}
