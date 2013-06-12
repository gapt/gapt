/*
 * FOLUnificationAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.unification.fol

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.algorithms.unification.UnificationAlgorithm
import at.logic.language.fol._
import at.logic.language.lambda.substitutions.Substitution
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.lk.base.types._
import collection.immutable.Seq

object FOLUnificationAlgorithm extends UnificationAlgorithm[FOLExpression] {

  def unify(seq1: FSequent, seq2: FSequent) : List[Substitution[FOLExpression]] = {
    require( (seq1._1 ++ seq1._2 ++ seq2._1 ++ seq2._2).forall( _.isInstanceOf[FOLFormula] ) )

    val seq1ord = new FSequent(seq1._1.sortBy(x => x.toString), seq1._2.sortBy(x => x.toString))
    val seq2ord = new FSequent(seq2._1.sortBy(x => x.toString), seq2._2.sortBy(x => x.toString))

    val formseq1 = Or(seq1._1.map(x => Neg(x.asInstanceOf[FOLFormula])) ++ seq1._2.map(x => x.asInstanceOf[FOLFormula]))
    val formseq2 = Or(seq2._1.map(x => Neg(x.asInstanceOf[FOLFormula])) ++ seq2._2.map(x => x.asInstanceOf[FOLFormula]))

    //unify( seq1.getOrderedSequent.toFormula.asInstanceOf[FOLFormula], seq2.getOrderedSequent.toFormula.asInstanceOf[FOLFormula] )
    unify( formseq1.asInstanceOf[FOLFormula], formseq2.asInstanceOf[FOLFormula] )
  }

  def unify(term1: FOLExpression, term2: FOLExpression) : List[Substitution[FOLExpression]] =
    unifySetOfTuples(Tuple2(term1.asInstanceOf[FOLExpression],term2.asInstanceOf[FOLExpression])::Nil,Nil) match {
      case Some((Nil,ls)) => List(Substitution[FOLExpression](ls.map(x => (x._1.asInstanceOf[FOLVar],x._2))))
      case _ => Nil
    }

  def applySubToListOfPairs(l : List[Tuple2[FOLExpression, FOLExpression]], s : Substitution[FOLExpression]) : List[Tuple2[FOLExpression, FOLExpression]] = {
  //  l.foldLeft(Nil)((Tuple2(x,v))=> (Tuple2(s.applyFOL(x),s.applyFOL(v))))
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
      case BinaryLogicSymbol(_, l, r) => getVars( l ) ++ getVars( r )
  }

  def unifySetOfTuples(s1: List[Tuple2[FOLExpression, FOLExpression]], s2 : List[Tuple2[FOLExpression, FOLExpression]]) : Option[(List[Tuple2[FOLExpression, FOLExpression]], List[Tuple2[FOLExpression, FOLExpression]])] = (s1,s2) match {
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

    // FIXME: this nested match is only necessary because of a scala bug:
    // if the case is put in the parent match, then the compiler refuses to
    // compile since the generated java code is too big!
    case _ => { (s1, s2) match {
      case (((BinaryLogicSymbol(s1, l1, r1), BinaryLogicSymbol(s2, l2, r2))::s), set2) if s1 == s2 => unifySetOfTuples((l1, l2)::(r1, r2)::s, set2)
      case _ => None
    }
    }
  }
}
