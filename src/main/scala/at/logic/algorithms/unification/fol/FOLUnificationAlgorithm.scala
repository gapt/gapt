/*
 * FOLUnificationAlgorithm.scala
 *
 */

package at.logic.algorithms.unification.fol

import at.logic.algorithms.unification.UnificationAlgorithm
import at.logic.language.fol._
import at.logic.calculi.lk.base.{Sequent, FSequent}

object FOLUnificationAlgorithm extends UnificationAlgorithm {

  def unify(seq1: FSequent, seq2: FSequent) : List[Substitution] = {
    require( (seq1._1 ++ seq1._2 ++ seq2._1 ++ seq2._2).forall( _.isInstanceOf[FOLFormula] ) )

    val formseq1 = Or( ( seq1._1.map(x => Neg(x.asInstanceOf[FOLFormula])) ++ seq1._2.map(x => x.asInstanceOf[FOLFormula]) ).toList )
    val formseq2 = Or( ( seq2._1.map(x => Neg(x.asInstanceOf[FOLFormula])) ++ seq2._2.map(x => x.asInstanceOf[FOLFormula]) ).toList )

    unify( formseq1, formseq2 )
  }

  def unify(term1: FOLExpression, term2: FOLExpression) : List[Substitution] =
    unifySetOfTuples(Tuple2(term1.asInstanceOf[FOLExpression],term2.asInstanceOf[FOLExpression])::Nil,Nil) match {
      case Some((Nil,ls)) => List(Substitution(ls.map(x => (x._1.asInstanceOf[FOLVar],x._2))))
      case _ => Nil
    }

  def applySubToListOfPairs(l : List[Tuple2[FOLExpression, FOLExpression]], s : Substitution) : List[Tuple2[FOLExpression, FOLExpression]] = {
    return l.map(a => (s.apply(a._1), s.apply(a._2)))
  }

  def isSolvedVarIn(x : FOLVar, l : List[Tuple2[FOLExpression, FOLExpression]]) : Boolean = {
      for ( term <- ((l.map((a)=>a._1)) ::: (l.map((a)=>a._2))))
        if(getVars(term).contains(x))
            false
      true
  }

  def getVars(f: FOLExpression): List[FOLVar] = f match {
      case (FOLConst(c)) => Nil
      case FOLVar(x) => f.asInstanceOf[FOLVar]::Nil
      case Function(_, args) => args.flatMap( a => getVars(a) )
      case Atom(_, args) => args.flatMap( a => getVars(a) )
      case Neg(f) => getVars(f)
      case And(l, r) => getVars(l) ++ getVars(r)
      case Or(l, r) => getVars(l) ++ getVars(r)
      case Imp(l, r) => getVars(l) ++ getVars(r)
  }

  def unifySetOfTuples(s1: List[(FOLExpression, FOLExpression)], s2 : List[(FOLExpression, FOLExpression)]) : Option[(List[(FOLExpression, FOLExpression)], List[(FOLExpression, FOLExpression)])] = 
  (s1,s2) match {
    case (((a1,a2)::s), s2) if a1 == a2 => unifySetOfTuples(s, s2)

    case ((FOLConst (name1),FOLConst (name2))::s,s2) if name1 != name2 => None

    case (((Function(f1,args1), Function(f2, args2))::s), s2)
      if args1.length == args2.length && f1==f2  => unifySetOfTuples(args1.zip(args2) ::: s, s2)

    case (((Atom(f1,args1), Atom(f2, args2))::s), s2)
      if args1.length == args2.length && f1==f2  => unifySetOfTuples(args1.zip(args2) ::: s, s2)

    case (((Neg(f1), Neg(f2))::s), s2) => unifySetOfTuples((f1, f2)::s, s2)

    case (((x : FOLVar,v)::s), s2) if !getVars(v).contains(x) => {
      val sub = Substitution(x,v)
      unifySetOfTuples(applySubToListOfPairs(s,sub), (x,v)::applySubToListOfPairs(s2,sub))
    }

    case (((v, x : FOLVar)::s), s2) if !getVars(v).contains(x) =>{ 
      val sub = Substitution(x,v)
      unifySetOfTuples(applySubToListOfPairs(s,sub), (x,v)::applySubToListOfPairs(s2,sub))
    }

    case (Nil, s2) => Some((Nil, s2))

    case ( (And(l1, r1), And(l2, r2)) :: s, set2) => unifySetOfTuples((l1, l2)::(r1, r2)::s, set2)
    
    case ( (Or(l1, r1), Or(l2, r2)) :: s, set2) => unifySetOfTuples((l1, l2)::(r1, r2)::s, set2)
    
    case ( (Imp(l1, r1), Imp(l2, r2)) :: s, set2) => unifySetOfTuples((l1, l2)::(r1, r2)::s, set2)
    
    case _ => None
  }
}
