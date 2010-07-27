package at.logic.transformations.skolemization

// This package implements formula and proof Skolemization.

import at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.language.lambda.BetaReduction._
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._
import at.logic.utils.logging.Logger
import scala.collection.immutable.{Map,HashMap}
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.base.{LKProof,Sequent,SequentOccurrence,PrincipalFormulas}
import at.logic.language.hol._
import at.logic.language.lambda.types._
import at.logic.language.lambda._
import at.logic.language.lambda.substitutions._
import at.logic.algorithms.lk.getCutAncestors
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.algorithms.lk.applySubstitution

object skolemize {

  def apply(p: LKProof) : LKProof = 
  {
    val fos = p.root.antecedent ++ p.root.succedent
    val inst_map = fos.foldLeft(new HashMap[FormulaOccurrence, List[HOLExpression]]())( (m, fo) => m.updated(fo, Nil))

    val sk_s = skolemize( p.root )

    skolemize( p, sk_s._2, inst_map, sk_s._3 )._1
  }

  /*
  Idea of the algorithm: Going upwards in the prooftree, we remember the 
  instantiations of the weak quantifiers and replace EV's by Skolem terms.
  Going downwards, we apply the appropriate inferences (essentially 
  leaving out the strong quantifier inferences).

  TODO: check whether proof is Skolemizable (or maybe just QFC)

  TODO: have to distinguish cut-ancestors/ES-ancestors!
  */
  def skolemize(proof: LKProof, 
      symbol_map: Map[FormulaOccurrence, Stream[ConstantStringSymbol]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      form_map: Map[FormulaOccurrence, HOLFormula]) :
      (LKProof, Map[FormulaOccurrence, FormulaOccurrence]) = proof match
  {
    case Axiom(s) => {
      val ant = s.antecedent.toList
      val succ = s.succedent.toList
      val new_seq = Sequent( ant.map( fo => fo.formula ), succ.map( fo => fo.formula ) )
      val ax = Axiom( new_seq )
      var new_map = ant.zipWithIndex.foldLeft(new HashMap[FormulaOccurrence, FormulaOccurrence])( (m, p) => m.updated( p._1, ax._2._1( p._2 ) ))
      new_map = succ.zipWithIndex.foldLeft(new_map)((m, p) => m.updated( p._1, ax._2._2( p._2 )))
      (ax._1, new_map)
    }
    case ForallRightRule(p, _, _, m, v) => handleStrongQuantRule( proof, p, m, v, symbol_map, inst_map, form_map )
    case ExistsLeftRule(p, _, _, m, v) => handleStrongQuantRule( proof, p, m, v, symbol_map, inst_map, form_map )
    case ForallLeftRule(p, _, a, m, t) => handleWeakQuantRule( proof, p, a, m, t, ForallLeftRule.computeAux,
      ForallLeftRule.apply, symbol_map, inst_map, form_map )
    case ExistsRightRule(p, _, a, m, t) => handleWeakQuantRule( proof, p, a, m, t, ExistsRightRule.computeAux,
      ExistsRightRule.apply, symbol_map, inst_map, form_map )
    case WeakeningLeftRule(p, _, m) => handleWeakeningRule( proof, p, m, 
      WeakeningLeftRule.apply, symbol_map, inst_map, form_map )
    case WeakeningRightRule(p, _, m) => handleWeakeningRule( proof, p, m, 
      WeakeningRightRule.apply, symbol_map, inst_map, form_map )
  }

  def handleWeakQuantRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence, t: HOLExpression,
      computeAux: (HOLFormula, HOLExpression) => HOLFormula,
      constructor: (LKProof, FormulaOccurrence, HOLFormula, HOLExpression) => LKProof,
      symbol_map: Map[FormulaOccurrence, Stream[ConstantStringSymbol]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      form_map: Map[FormulaOccurrence, HOLFormula]
    ) = {
      val inst_list = inst_map( m )
      val new_inst_map = copyMapToAncestor( inst_map.updated( m, inst_list :+ t ) )
      val new_form = computeAux( form_map( m ), t )
      val new_form_map = copyMapToAncestor( form_map.updated( m, new_form ) )
      val new_proof = skolemize( p, copyMapToAncestor( symbol_map ), new_inst_map, new_form_map )
      val ret = constructor( new_proof._1, new_proof._2( a ), form_map( m ), t ) 
      ( ret, copyMapToDescendant( proof, ret, new_proof._2 ) )
  }


  def handleWeakeningRule( proof: LKProof, p: LKProof, m: FormulaOccurrence,
      constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas,
      symbol_map: Map[FormulaOccurrence, Stream[ConstantStringSymbol]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      form_map: Map[FormulaOccurrence, HOLFormula]
    ) = {
      val new_proof = skolemize( p, copyMapToAncestor( symbol_map - m ), 
        copyMapToAncestor( inst_map - m ), 
        copyMapToAncestor( form_map - m ) )
      val ret = constructor( new_proof._1, form_map( m ) )
      ( ret, copyMapToDescendant( proof, ret, new_proof._2 ) + ( m -> ret.prin.head ) )
  }

  def handleStrongQuantRule( proof: LKProof, p: LKProof, m: FormulaOccurrence, v: HOLVar,
      symbol_map: Map[FormulaOccurrence, Stream[ConstantStringSymbol]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      form_map: Map[FormulaOccurrence, HOLFormula]
    ) = {
      val sym_stream = symbol_map( m )
      val sym = sym_stream.head
      val skolem_term = Function( sym, inst_map( m ), v.exptype )
      val sub_proof = applySubstitution( p, Substitution( v, skolem_term ) )
      // invert the formula occurrence map.
      val inv_map = sub_proof._2.foldLeft(new HashMap[FormulaOccurrence, FormulaOccurrence])((m, p) => m.updated(p._2, p._1) )
      val new_symbol_map = copyMapToAncestor( symbol_map.updated( m, sym_stream.tail ) )
      val new_inst_map = copyMapToAncestor( inst_map )
      val new_form_map = copyMapToAncestor( form_map )
      val new_proof = skolemize( sub_proof._1, inv_map.mapValues( new_symbol_map ), 
        inv_map.mapValues( new_inst_map ), inv_map.mapValues( new_form_map ) )
      // FIXME: sub_proof._2 is mutable map, so we have to construct a new immutable one.
      val new_map = new HashMap() ++ ( sub_proof._2.mapValues( new_proof._2 ) )
      ( new_proof._1, copyMap( proof, new_proof._1, new_map ) )
  }

  def copyMapToAncestor[A]( map: Map[FormulaOccurrence, A] ) =
    map.map( p => (p._1.ancestors.head, p._2 ) )

  def copyMapToDescendant( old_p: LKProof, new_p: LKProof, 
                           map: Map[FormulaOccurrence, FormulaOccurrence] ) =
    map.map( p => (old_p.getDescendantInLowerSequent( p._1 ).get, 
      new_p.getDescendantInLowerSequent( p._2 ).get ) )

  def copyMap( old_p: LKProof, new_p: LKProof, map: Map[FormulaOccurrence, FormulaOccurrence] ) =
    map.map( p => (old_p.getDescendantInLowerSequent( p._1 ).get,
      p._2 ) )

  def skolemize(s: SequentOccurrence) : (Sequent, Map[FormulaOccurrence, Stream[ConstantStringSymbol]], Map[FormulaOccurrence, HOLFormula]) =
  {
    var stream = skolem_symbol_stream
    val fos = s.antecedent ++ s.succedent
    val symbol_map = fos.foldLeft(new HashMap[FormulaOccurrence, Stream[ConstantStringSymbol]]())( (m, fo) => {
        val s = even( stream )
        stream = odd( stream )
        m.updated( fo, s )
      })

    val sk_ant = s.antecedent.map( fo => (fo, apply( fo.formula, 1, symbol_map( fo ) ) ) )
    val sk_succ = s.succedent.map( fo => (fo, apply( fo.formula, 0, symbol_map( fo ) ) ) )

    (Sequent(sk_ant.map(_._2).toList, sk_succ.map(_._2).toList), symbol_map, sk_ant.toMap ++ sk_succ.toMap)
  }

  def skolem_symbol_stream_from(n: Int): Stream[ConstantStringSymbol] =
    Stream.cons(ConstantStringSymbol( "s_" + n ), skolem_symbol_stream_from( n + 1 ) )

  def skolem_symbol_stream = skolem_symbol_stream_from( 0 )

  def even[A]( s: Stream[A] ) : Stream[A] = Stream.cons( s.head, even(s.tail.tail) )

  def odd[A]( s: Stream[A] ) : Stream[A] = Stream.cons( s.tail.head, odd(s.tail.tail) )

  def invert( pol: Int ) = 
    if (pol == 0)
      1
    else
      0

  def apply(f: HOLFormula, pol: Int, symbols: Stream[ConstantStringSymbol]) = sk( f, pol, Nil, symbols )

  def sk(f: HOLFormula, pol: Int, vars: List[HOLVar], symbols: Stream[ConstantStringSymbol]) : HOLFormula = f match {
    case And(l, r) => And( sk( l , pol, vars, even( symbols ) ), sk( r, pol, vars, odd( symbols ) ) )
    case Or(l, r) => Or( sk( l , pol, vars, even( symbols ) ), sk( r, pol, vars, odd( symbols ) ) )
    case Imp(l, r) => Imp( sk( l , invert( pol ), vars, even( symbols ) ), sk( r, pol, vars, odd( symbols ) ) )
    case Neg(f) => Neg( sk( f, invert( pol ), vars, symbols ) )
    case ExVar(x, f) =>
      if (pol == 1)
      {
        val sub = Substitution(x, Function( symbols.head, vars, x.exptype ) )
        // TODO: should not be necessary to cast here, Formula is closed under substitution
        sk( sub( f ).asInstanceOf[HOLFormula], pol, vars, symbols.tail )
      }
      else // TODO: should not be necessary to cast! try to change it in hol.scala.
        ExVar(x, sk( f, pol, vars :+ x.asInstanceOf[HOLVar], symbols ) )
    case AllVar(x, f) =>
      if (pol == 0)
      {
        val sub = Substitution(x, Function( symbols.head, vars, x.exptype ) )
        // TODO: should not be necessary to cast here, Formula is closed under substitution
        sk( sub( f ).asInstanceOf[HOLFormula], pol, vars, symbols.tail )
      }
      else // TODO: should not be necessary to cast! try to change it in hol.scala.
        AllVar(x, sk( f, pol, vars :+ x.asInstanceOf[HOLVar], symbols ) )
    case Atom(_,_) => f
  }
}
