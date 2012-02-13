package at.logic.transformations.skolemization

// This package implements formula and proof Skolemization.

import at.logic.language.lambda.BetaReduction._
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._
import at.logic.utils.logging.Logger
import scala.collection.immutable.{Map,HashMap,HashSet}
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.base.{LKProof,Sequent,PrincipalFormulas}
import at.logic.language.hol._
import at.logic.language.lambda.types._
import at.logic.language.lambda._
import at.logic.language.lambda.substitutions._
import at.logic.algorithms.lk.getCutAncestors
import at.logic.language.hol.logicSymbols.ConstantSymbolA
import at.logic.algorithms.lk.applySubstitution
import at.logic.language.hol.skolemSymbols.SkolemSymbolFactory
import at.logic.utils.ds.streams.Definitions._
import scala.collection.immutable.Stream.Empty
import typedLambdaCalculus.{AbsInScope, App, Var, LambdaExpression}

/*
object skolemize {

  def apply(p: LKProof) : LKProof = 
  {
    val fos = p.root.antecedent ++ p.root.succedent
    val inst_map = fos.foldLeft(new HashMap[FormulaOccurrence, List[HOLExpression]]())( (m, fo) => m + (fo -> Nil))

    val sk_s = skolemize( p.root )

    skolemize( p, sk_s._2, inst_map, sk_s._3, new HashSet[FormulaOccurrence] )._1
  }

  /*
  Idea of the algorithm: Going upwards in the prooftree, we remember the 
  instantiations of the weak quantifiers (inst_map), replace EV's by Skolem terms (symbols chosen by symbol_map),
  and keep a copy of the new end-sequent (form_map).
  Going downwards, we apply the appropriate inferences (essentially 
  leaving out the strong quantifier inferences).

  TODO: check whether proof is Skolemizable (or maybe just QFC)

  TODO: maybe form_map not necessary: we can skolemize the auxiliary formulas on the fly (we should have all
    necessary information). This is done in Def, Eq-Rules anyways.
  */
  def skolemize(proof: LKProof, 
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      form_map: Map[FormulaOccurrence, HOLFormula],
      cut_ancs: Set[FormulaOccurrence]) :
      (LKProof, Map[FormulaOccurrence, FormulaOccurrence]) = {
    implicit val s_map = symbol_map
    implicit val i_map = inst_map
    implicit val f_map = form_map
    implicit val c_ancs = cut_ancs

    proof match
    {
      case Axiom(s) => {
        val ant = s.antecedent.toList
        val succ = s.succedent.toList
        val new_seq = Sequent( ant.map( fo => fo.formula ), succ.map( fo => fo.formula ) )
        val ax = Axiom( new_seq )
        var new_map = ant.zipWithIndex.foldLeft(new HashMap[FormulaOccurrence, FormulaOccurrence])( (m, p) => m + ( p._1 -> ax._2._1( p._2 ) ))
        new_map = succ.zipWithIndex.foldLeft(new_map)((m, p) => m + ( p._1 -> ax._2._2( p._2 )))
        (ax._1, new_map)
      }
      case ForallRightRule(p, _, a, m, v) => handleStrongQuantRule( proof, p, a, m, v, ForallRightRule.apply )
      case ExistsLeftRule(p, _, a, m, v) => handleStrongQuantRule( proof, p, a, m, v, ExistsLeftRule.apply )
      case ForallLeftRule(p, _, a, m, t) => handleWeakQuantRule( proof, p, a, m, t, ForallLeftRule.computeAux,
        ForallLeftRule.apply)
      case ExistsRightRule(p, _, a, m, t) => handleWeakQuantRule( proof, p, a, m, t, ExistsRightRule.computeAux,
        ExistsRightRule.apply)
      case WeakeningLeftRule(p, _, m) => handleWeakeningRule( proof, p, m, WeakeningLeftRule.apply)
      case WeakeningRightRule(p, _, m) => handleWeakeningRule( proof, p, m, WeakeningRightRule.apply)
      case ContractionLeftRule(p, _, a1, a2, _) => handleContractionRule( proof, p, a1, a2, ContractionLeftRule.apply)
      case ContractionRightRule(p, _, a1, a2, _) => handleContractionRule( proof, p, a1, a2, ContractionRightRule.apply)
      case AndRightRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1, a2, m, AndRightRule.computeLeftAux, AndRightRule.computeRightAux, AndRightRule.apply)
      case AndLeft1Rule(p, _, a, m) => handleUnary1Rule( proof, p, a, 
        form_map( m ) match { case And(_, w) => w }, m, AndLeft1Rule.computeAux, AndLeft1Rule.apply)
      case AndLeft2Rule(p, _, a, m) => handleUnary2Rule( proof, p, a,
        form_map( m ) match { case And(w, _) => w }, m, AndLeft2Rule.computeAux, AndLeft2Rule.apply)
      case OrLeftRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1, a2, m, OrLeftRule.computeLeftAux, OrLeftRule.computeRightAux, OrLeftRule.apply)
      case OrRight1Rule(p, _, a, m) => handleUnary1Rule( proof, p, a,
        form_map( m ) match { case Or(_, w) => w }, m, OrRight1Rule.computeAux, OrRight1Rule.apply)
      case OrRight2Rule(p, _, a, m) => handleUnary2Rule( proof, p, a,
        form_map( m ) match { case Or(w, _) => w }, m, OrRight2Rule.computeAux, OrRight2Rule.apply)
      case ImpLeftRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1, a2, m, ImpLeftRule.computeLeftAux, ImpLeftRule.computeRightAux, ImpLeftRule.apply)
      case ImpRightRule(p, _, a1, a2, m) => {
        val (na1, na2) = form_map(m) match { case Imp(l, r) => (l, r) }
        val new_proof = skolemize( p, 
          copyMapToAncestor(symbol_map).updated(a1, even(symbol_map( m ))).updated(a2, odd(symbol_map( m ))),
          copyMapToAncestor(inst_map),
          copyMapToAncestor(form_map).updated(a1, na1).updated(a2, na2), copySetToAncestor( cut_ancs ) )
        val ret = ImpRightRule( new_proof._1, new_proof._2( a1 ), new_proof._2( a2 ) )
        (ret, copyMapToDescendant( proof, ret, new_proof._2 ))
      }
      case NegLeftRule( p, _, a, m ) => handleNegRule( proof, p, a, m, NegLeftRule.computeAux, NegLeftRule.apply )
      case NegRightRule( p, _, a, m ) => handleNegRule( proof, p, a, m, NegLeftRule.computeAux, NegRightRule.apply )
      case DefinitionLeftRule( p, _, a, m ) => handleDefRule( proof, p, a, m, 1, DefinitionLeftRule.apply )
      case DefinitionRightRule( p, _, a, m ) => handleDefRule( proof, p, a, m, 0, DefinitionRightRule.apply )
      case EquationLeft1Rule( p1, p2, _, e, a, m ) => handleEqRule( proof, p1, p2, e, a, m, 1, EquationLeft1Rule.apply )
      case EquationLeft2Rule( p1, p2, _, e, a, m ) => handleEqRule( proof, p1, p2, e, a, m, 1, EquationLeft2Rule.apply )
      case EquationRight1Rule( p1, p2, _, e, a, m ) => handleEqRule( proof, p1, p2, e, a, m, 0, EquationRight1Rule.apply )
      case EquationRight2Rule( p1, p2, _, e, a, m ) => handleEqRule( proof, p1, p2, e, a, m, 0, EquationRight2Rule.apply )
      case CutRule( p1, p2, _, a1, a2 ) => {
        val new_symbol_map = copyMapToAncestor( symbol_map )
        val new_inst_map = copyMapToAncestor( inst_map )
        val new_form_map = copyMapToAncestor( form_map )
        val new_cut_ancs = copySetToAncestor( cut_ancs )
        // TODO: in principle, don't have to add stuff to symbol_map, inst_map because we don't care
        val new_p1 = skolemize( p1, new_symbol_map + (a1 -> Empty), new_inst_map + (a1 -> Nil), new_form_map + (a1 -> a1.formula), new_cut_ancs + a1 )
        val new_p2 = skolemize( p2, new_symbol_map + (a2 -> Empty), new_inst_map + (a2 -> Nil), new_form_map + (a2 -> a2.formula), new_cut_ancs + a2 )
        val ret = CutRule( new_p1._1, new_p2._1, new_p1._2( a1 ), new_p2._2( a2 ) )
        (ret, copyMapToDescendant( proof, ret, new_p1._2 ++ new_p2._2))
      }
    }
  }

  def handleEqRule( proof: LKProof, p1: LKProof, p2: LKProof, e: FormulaOccurrence, a: FormulaOccurrence, m: FormulaOccurrence,
    pol: Int, constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence, HOLFormula) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      form_map: Map[FormulaOccurrence, HOLFormula],
      cut_ancs: Set[FormulaOccurrence]
    ) = {
        val new_aux = if (!cut_ancs.contains( m ) ) sk( a.formula, pol, inst_map( m ), symbol_map( m ) ) else a.formula
        val new_symbol_map = copyMapToAncestor( symbol_map )
        val new_inst_map = copyMapToAncestor( inst_map )
        val new_form_map_left = copyMapToAncestor( form_map ).updated(e, e.formula)
        val new_form_map_right = copyMapToAncestor( form_map ).updated( a, new_aux )
        val new_cut_ancs = copySetToAncestor( cut_ancs )
        val new_p1 = skolemize( p1, new_symbol_map, new_inst_map, new_form_map_left, new_cut_ancs )
        val new_p2 = skolemize( p2, new_symbol_map, new_inst_map, new_form_map_right, new_cut_ancs )
        val ret = constructor( new_p1._1, new_p2._1, new_p1._2( e ), new_p2._2( a ), form_map ( m ) )
        (ret, copyMapToDescendant( proof, ret, new_p1._2 ++ new_p2._2 ))
  }

  def handleDefRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence, pol: Int,
      constructor: (LKProof, FormulaOccurrence, HOLFormula) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      form_map: Map[FormulaOccurrence, HOLFormula],
      cut_ancs: Set[FormulaOccurrence]

    ) = {
      //println("skolemizing def aux (pol: " + pol + "): " + a.formula.toStringSimple)
      val new_aux = if (!cut_ancs.contains( m ) ) sk( a.formula, pol, inst_map( m ), symbol_map( m ) ) else a.formula
      //println("result: " + new_aux.toStringSimple )
      val new_proof = skolemize( p, copyMapToAncestor(symbol_map), 
        copyMapToAncestor(inst_map), copyMapToAncestor(form_map).updated( a, new_aux ), copySetToAncestor( cut_ancs ) )
      val ret = constructor( new_proof._1, new_proof._2( a ), form_map( m ) )
      (ret, copyMapToDescendant( proof, ret, new_proof._2 ) )
    }


  def handleNegRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence,
      computeAux: HOLFormula => HOLFormula,
      constructor: (LKProof, FormulaOccurrence) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      form_map: Map[FormulaOccurrence, HOLFormula],
      cut_ancs: Set[FormulaOccurrence]

    ) = {
      val new_proof = skolemize( p, copyMapToAncestor(symbol_map), copyMapToAncestor(inst_map),
        copyMapToAncestor(form_map).updated(a, computeAux( form_map(m) ) ), copySetToAncestor( cut_ancs ) )
      val ret = constructor( new_proof._1, new_proof._2( a ) )
      (ret, copyMapToDescendant( proof, ret, new_proof._2 ))
  }

  def handleUnaryRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, weak: HOLFormula, m: FormulaOccurrence,
      computeAux: HOLFormula => HOLFormula,
      constructor: (LKProof, FormulaOccurrence, HOLFormula) => LKProof,
      partition: Stream[ConstantSymbolA] => Stream[ConstantSymbolA])(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      form_map: Map[FormulaOccurrence, HOLFormula],
      cut_ancs: Set[FormulaOccurrence]

    ) = {
      val new_proof = skolemize( p, 
        copyMapToAncestor(symbol_map).updated( a, partition( symbol_map( m ) ) ), 
        copyMapToAncestor(inst_map),
        copyMapToAncestor(form_map).updated(a, computeAux( form_map(m) ) ), copySetToAncestor( cut_ancs ) )
      val ret = constructor( new_proof._1, new_proof._2( a ), weak ) 
      (ret, copyMapToDescendant( proof, ret, new_proof._2 ))
  }

  // give even partition function
  def handleUnary1Rule( proof: LKProof, p: LKProof, a: FormulaOccurrence, weak: HOLFormula, m: FormulaOccurrence,
      computeAux: HOLFormula => HOLFormula,
      constructor: (LKProof, FormulaOccurrence, HOLFormula) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      form_map: Map[FormulaOccurrence, HOLFormula],
      cut_ancs: Set[FormulaOccurrence]
    ) = handleUnaryRule( proof, p, a, weak, m, computeAux, constructor, even)

  // switch the arguments of the constructor
  // give odd partition function
  def handleUnary2Rule( proof: LKProof, p: LKProof, a: FormulaOccurrence, weak: HOLFormula, m: FormulaOccurrence,
      computeAux: HOLFormula => HOLFormula,
      constructor: (LKProof, HOLFormula, FormulaOccurrence) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      form_map: Map[FormulaOccurrence, HOLFormula],
      cut_ancs: Set[FormulaOccurrence]
    ) = handleUnaryRule( proof, p, a, weak, m, computeAux,
      (p, fo, f) => constructor(p, f, fo), odd )

  def handleBinaryRule( proof: LKProof, p1: LKProof, p2: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence, m: FormulaOccurrence,
      computeLeftAux: HOLFormula => HOLFormula, computeRightAux: HOLFormula => HOLFormula,
      constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      form_map: Map[FormulaOccurrence, HOLFormula],
      cut_ancs: Set[FormulaOccurrence]

    ) = {
      val new_symbol_map_left = copyMapToAncestor(symbol_map).updated( a1, even( symbol_map( m ) ) )
      val new_symbol_map_right = copyMapToAncestor(symbol_map).updated( a2, odd( symbol_map( m ) ) )
      val new_inst_map = copyMapToAncestor(inst_map)
      val new_form_map_left = copyMapToAncestor(form_map).updated(a1, computeLeftAux( form_map(m) ) )
      val new_form_map_right = copyMapToAncestor(form_map).updated(a2, computeRightAux( form_map(m) ) )
      val new_cut_ancs = copySetToAncestor( cut_ancs )
      val new_p1 = skolemize( p1, new_symbol_map_left, new_inst_map, new_form_map_left, new_cut_ancs )
      val new_p2 = skolemize( p2, new_symbol_map_right, new_inst_map, new_form_map_right, new_cut_ancs )
      val ret = constructor( new_p1._1, new_p2._1, new_p1._2( a1 ), new_p2._2( a2 ) )
      (ret, copyMapToDescendant( proof, ret, new_p1._2 ++ new_p2._2 ))
  }


  def handleContractionRule( proof: LKProof, p: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence,
      constructor: (LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      form_map: Map[FormulaOccurrence, HOLFormula],
      cut_ancs: Set[FormulaOccurrence]

    ) = {
    val new_proof = skolemize( p, copyMapToAncestor(symbol_map), copyMapToAncestor(inst_map), copyMapToAncestor(form_map), copySetToAncestor( cut_ancs ) )
    val ret = constructor( new_proof._1, new_proof._2( a1 ), new_proof._2( a2 ) )
    (ret, copyMapToDescendant( proof, ret, new_proof._2 ) )
  }

  def handleWeakQuantRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence, t: HOLExpression,
      computeAux: (HOLFormula, HOLExpression) => HOLFormula,
      constructor: (LKProof, FormulaOccurrence, HOLFormula, HOLExpression) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      form_map: Map[FormulaOccurrence, HOLFormula],
      cut_ancs: Set[FormulaOccurrence]

    ) = {
      val inst_list = inst_map( m )
      val new_inst_map = copyMapToAncestor( inst_map ).updated( a, inst_list :+ t )
      val new_form_map = copyMapToAncestor( form_map ).updated( a, computeAux( form_map( m ), t ) )
      val new_proof = skolemize( p, copyMapToAncestor( symbol_map ), new_inst_map, new_form_map, copySetToAncestor( cut_ancs ) )
      //println("main formula for weak quant rule: " + form_map( m ).toStringSimple )
      val ret = constructor( new_proof._1, new_proof._2( a ), form_map( m ), t ) 
      ( ret, copyMapToDescendant( proof, ret, new_proof._2 ) )
  }


  def handleWeakeningRule( proof: LKProof, p: LKProof, m: FormulaOccurrence,
      constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      form_map: Map[FormulaOccurrence, HOLFormula],
      cut_ancs: Set[FormulaOccurrence]
    ) = {
      val new_proof = skolemize( p, copyMapToAncestor( symbol_map - m ), 
        copyMapToAncestor( inst_map - m ), 
        copyMapToAncestor( form_map - m ), copySetToAncestor( cut_ancs ) )
      val ret = constructor( new_proof._1, form_map( m ) )
      ( ret, copyMapToDescendant( proof, ret, new_proof._2 ) + ( m -> ret.prin.head ) )
  }

  def handleStrongQuantRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence, v: HOLVar,
      constructor: (LKProof, FormulaOccurrence, HOLFormula, HOLVar) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      form_map: Map[FormulaOccurrence, HOLFormula],
      cut_ancs: Set[FormulaOccurrence]
    ) = {
      if (!cut_ancs.contains( m ) )
      {
        val sym_stream = symbol_map( m )
        val sym = sym_stream.head
        //println("skolem symbol: " + sym)
        val skolem_term = Function( sym, inst_map( m ), v.exptype )
        val sub = Substitution( v, skolem_term )
        val sub_proof = applySubstitution( p, sub )
        //println("old es: " + p.root.getSequent.toStringSimple)
        //println("sub: " + sub )
        //println("after sub: " + sub_proof._1.root.getSequent.toStringSimple )
        // invert the formula occurrence map.
        val inv_map = sub_proof._2.foldLeft(new HashMap[FormulaOccurrence, FormulaOccurrence])((m, p) => m + (p._2 -> p._1) )
        val new_symbol_map = copyMapToAncestor( symbol_map ).updated( a, sym_stream.tail )
        val new_inst_map = copyMapToAncestor( inst_map )
        val new_form_map = copyMapToAncestor( form_map ).updated( a, sub_proof._2( a ).formula )
        val new_cut_ancs = copySetToAncestor( cut_ancs ).foldLeft(new HashSet[FormulaOccurrence])( (s, fo) => if (sub_proof._2.isDefinedAt( fo ) ) s + sub_proof._2( fo ) else s )
        //println("old aux: " + form_map( m ).toStringSimple )
        //println("new aux: " + new_form_map( a ).toStringSimple )
        val new_proof = skolemize( sub_proof._1, inv_map.mapValues( new_symbol_map ), 
          inv_map.mapValues( new_inst_map ),
          inv_map.mapValues( new_form_map ),
          new_cut_ancs )
        // FIXME: sub_proof._2 is mutable map, so we have to construct a new immutable one.
        val new_map = new HashMap() ++ ( sub_proof._2.mapValues( new_proof._2 ) )
        ( new_proof._1, copyMap( proof, new_proof._1, new_map ) )
    }
    else
    {
      val new_proof = skolemize( p, copyMapToAncestor(symbol_map), copyMapToAncestor(inst_map),
        copyMapToAncestor(form_map).updated(a, a.formula), copySetToAncestor( cut_ancs ) )
      val ret = constructor( new_proof._1, new_proof._2( a ), m.formula, v )
      (ret, copyMapToDescendant( proof, ret, new_proof._2 ))

    }
  }

  def copyMapToAncestor[A]( map: Map[FormulaOccurrence, A] ) =
    map.foldLeft(new HashMap[FormulaOccurrence, A])( (m, p) => m ++ p._1.ancestors.map( a => (a, p._2) ) )
 
  def copySetToAncestor( set: Set[FormulaOccurrence] ) = set.foldLeft( new HashSet[FormulaOccurrence] )( (s, fo) => s ++ fo.ancestors )

  def copyMapToDescendant( old_p: LKProof, new_p: LKProof, 
                           map: Map[FormulaOccurrence, FormulaOccurrence] ) =
    map.foldLeft(new HashMap[FormulaOccurrence, FormulaOccurrence])( (m, p) => {
        val desc = old_p.getDescendantInLowerSequent( p._1 )
        if (desc != None)
          m + (desc.get -> new_p.getDescendantInLowerSequent( p._2 ).get )
        else
          m
      } )

  def copyMap( old_p: LKProof, new_p: LKProof, map: Map[FormulaOccurrence, FormulaOccurrence] ) =
    map.map( p => (old_p.getDescendantInLowerSequent( p._1 ).get,
      p._2 ) )

  def skolemize(s: Sequent) : (Sequent, Map[FormulaOccurrence, Stream[ConstantSymbolA]], Map[FormulaOccurrence, HOLFormula]) = skolemize( s, SkolemSymbolFactory.getSkolemSymbols )

  def skolemize(s: Sequent, stream: Stream[ConstantSymbolA]) : (Sequent, Map[FormulaOccurrence, Stream[ConstantSymbolA]], Map[FormulaOccurrence, HOLFormula]) =
  {
    var cur_stream = stream
    val fos = s.antecedent ++ s.succedent
    val symbol_map = fos.foldLeft(new HashMap[FormulaOccurrence, Stream[ConstantSymbolA]])( (m, fo) => {
        val s = even( cur_stream )
        cur_stream = odd( cur_stream )
        m + ( fo -> s )
      })

    val sk_ant = s.antecedent.map( fo => (fo, skolemize( fo.formula, 1, symbol_map( fo ) ) ) )
    val sk_succ = s.succedent.map( fo => (fo, skolemize( fo.formula, 0, symbol_map( fo ) ) ) )

    (Sequent(sk_ant.map(_._2).toList, sk_succ.map(_._2).toList), symbol_map, sk_ant.toMap ++ sk_succ.toMap)
  }

  def invert( pol: Int ) = 
    if (pol == 0)
      1
    else
      0

  def apply(f: HOLFormula, pol: Int, symbols: Stream[ConstantSymbolA]) = skolemize( f, pol, symbols )

  def skolemize(f: HOLFormula, pol: Int, symbols: Stream[ConstantSymbolA]) = sk( f, pol, Nil, symbols )

  def sk(f: HOLFormula, pol: Int, terms: List[HOLExpression], symbols: Stream[ConstantSymbolA]) : HOLFormula = f match {
    case And(l, r) => And( sk( l , pol, terms, even( symbols ) ), sk( r, pol, terms, odd( symbols ) ) )
    case Or(l, r) => Or( sk( l , pol, terms, even( symbols ) ), sk( r, pol, terms, odd( symbols ) ) )
    case Imp(l, r) => Imp( sk( l , invert( pol ), terms, even( symbols ) ), sk( r, pol, terms, odd( symbols ) ) )
    case Neg(f) => Neg( sk( f, invert( pol ), terms, symbols ) )
    case ExVar(x, f) =>
      if (pol == 1)
      {
        assert( !f.getFreeAndBoundVariables._2.contains( x ) )
        val sub = Substitution(x, Function( symbols.head, terms, x.exptype ) )
        // TODO: should not be necessary to cast here, Formula is closed under substitution
        sk( sub( f ).asInstanceOf[HOLFormula], pol, terms, symbols.tail )
      }
      else // TODO: should not be necessary to cast! try to change it in hol.scala.
        ExVar(x, sk( f, pol, terms :+ x.asInstanceOf[HOLVar], symbols ) )
    case AllVar(x, f) =>
      if (pol == 0)
      {
        assert( !f.getFreeAndBoundVariables._2.contains( x ) )
        //println( "skolemizing AllQ")
        val sub = Substitution(x, Function( symbols.head, terms, x.exptype ) )
        //println( "substitution: " + sub )
        //println( f )
        //println( sub( f ) )
        // TODO: should not be necessary to cast here, Formula is closed under substitution
        val res = sk( sub( f ).asInstanceOf[HOLFormula], pol, terms, symbols.tail )
        //println( "result of skolemization: " + res )
        res
      }
      else // TODO: should not be necessary to cast! try to change it in hol.scala.
        AllVar(x, sk( f, pol, terms :+ x.asInstanceOf[HOLVar], symbols ) )
    case Atom(_,_) => f
  }
}
*/

// THE FOLLOWING VERSION DOES NOT WORK - IT FAILS ON A UNIT TEST.
// See stdout: The substitution is { y <- s_1(x) } is applied to
// R(x,y), and the result is again R(x,y) because the occurrence
// of y thinks it's bound!

object skolemize {

  def apply(p: LKProof) : LKProof = 
  {
    val fos = p.root.antecedent ++ p.root.succedent
    val inst_map = fos.foldLeft(new HashMap[FormulaOccurrence, List[HOLExpression]]())( (m, fo) => m + (fo -> Nil))

    // TODO: make this a parameter?
    var cur_stream = SkolemSymbolFactory.getSkolemSymbols
    val symbol_map = fos.foldLeft(new HashMap[FormulaOccurrence, Stream[ConstantSymbolA]])( (m, fo) => {
        val s = even( cur_stream )
        cur_stream = odd( cur_stream )
        m + ( fo -> s )
      })

    println("\n===== Start Skolemizing ====")

    skolemize( p, symbol_map, inst_map, new HashSet[FormulaOccurrence] )._1
  }

  /*
  Idea of the algorithm: Going upwards in the prooftree, we remember the 
  instantiations of the weak quantifiers (inst_map) and replace EV's by Skolem terms (symbols chosen by symbol_map).
  The skolemized formulas in the proof-tree are computed dynamically at every step.

  Going downwards, we apply the appropriate inferences (essentially 
  leaving out the strong quantifier inferences).

  TODO: check whether proof is Skolemizable (or maybe just QFC)
  */
  def skolemize(proof: LKProof, 
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      cut_ancs: Set[FormulaOccurrence]) :
      (LKProof, Map[FormulaOccurrence, FormulaOccurrence]) = {
    implicit val s_map = symbol_map
    implicit val i_map = inst_map
    implicit val c_ancs = cut_ancs
    println("=== Skolemizing: " + proof.root + " ===")
    proof match
    {
      case Axiom(s) => {
        val ant = s.antecedent
        val succ = s.succedent
/*        val new_seq = Sequent( ant.map( fo => fo.formula ), succ.map( fo => fo.formula ) ) */
        val new_seq = ( ant.map( fo => fo.formula ), succ.map( fo => fo.formula ) )
        val ax = Axiom( new_seq._1, new_seq._2 )
        println("Skolemization creates Axiom: " + ax.root.toStringSimple)
        var new_map = ant.zipWithIndex.foldLeft(new HashMap[FormulaOccurrence, FormulaOccurrence])( (m, p) => m + ( p._1 -> ax.root.antecedent( p._2 ) ))
        new_map = succ.zipWithIndex.foldLeft(new_map)((m, p) => m + ( p._1 -> ax.root.succedent( p._2 )))
        (ax, new_map)
      }
      case ForallRightRule(p, _, a, m, v) => debug("all,r",p,a::m::Nil, Nil, v::Nil); handleStrongQuantRule( proof, p, a, m, v, ForallRightRule.apply )
      case ExistsLeftRule(p, _, a, m, v) => debug("ex,l",p,a::m::Nil, Nil, v::Nil); handleStrongQuantRule( proof, p, a, m, v, ExistsLeftRule.apply )
      case ForallLeftRule(p, _, a, m, t) => debug("ex,r",p,a::m::Nil, Nil, t::Nil); handleWeakQuantRule( proof, p, a, m, t, 1, ForallLeftRule.computeAux,
        ForallLeftRule.apply)
      case ExistsRightRule(p, _, a, m, t) => debug("all,l",p,a::m::Nil, Nil, t::Nil); handleWeakQuantRule( proof, p, a, m, t, 0, ExistsRightRule.computeAux,
        ExistsRightRule.apply)
      case WeakeningLeftRule(p, _, m) => handleWeakeningRule( proof, p, m, 1, WeakeningLeftRule.apply)
      case WeakeningRightRule(p, _, m) => handleWeakeningRule( proof, p, m, 0, WeakeningRightRule.apply)
      case ContractionLeftRule(p, _, a1, a2, _) => handleContractionRule( proof, p, a1, a2, ContractionLeftRule.apply)
      case ContractionRightRule(p, _, a1, a2, _) => handleContractionRule( proof, p, a1, a2, ContractionRightRule.apply)
      case AndRightRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1, a2, m, AndRightRule.computeLeftAux, AndRightRule.computeRightAux, AndRightRule.apply)
      case AndLeft1Rule(p, _, a, m) => handleUnary1Rule( proof, p, a, m, 1, And.unapply, AndLeft1Rule.computeAux, AndLeft1Rule.apply)
      case AndLeft2Rule(p, _, a, m) => handleUnary2Rule( proof, p, a, m, 1, And.unapply, AndLeft2Rule.computeAux, AndLeft2Rule.apply)
      case OrLeftRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1, a2, m, OrLeftRule.computeLeftAux, OrLeftRule.computeRightAux, OrLeftRule.apply)
      case OrRight1Rule(p, _, a, m) => handleUnary1Rule( proof, p, a, m, 0, Or.unapply, OrRight1Rule.computeAux, OrRight1Rule.apply)
      case OrRight2Rule(p, _, a, m) => handleUnary2Rule( proof, p, a, m, 0, Or.unapply, OrRight2Rule.computeAux, OrRight2Rule.apply)
      case ImpLeftRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1, a2, m, ImpLeftRule.computeLeftAux, ImpLeftRule.computeRightAux, ImpLeftRule.apply)
      case ImpRightRule(p, _, a1, a2, m) => {
        val new_main = if (cut_ancs.contains( m )) m.formula else sk( m.formula, 0, inst_map( m ), symbol_map( m ) )
        val (na1, na2) = new_main match { case Imp(l, r) => (l, r) }
        val new_proof = skolemize( p, 
          copyMapToAncestor(symbol_map).updated(a1, even(symbol_map( m ))).updated(a2, odd(symbol_map( m ))),
          copyMapToAncestor(inst_map),
          copySetToAncestor(cut_ancs) )
        val ret = ImpRightRule( new_proof._1, new_proof._2( a1 ), new_proof._2( a2 ) )
        (ret, copyMapToDescendant( proof, ret, new_proof._2 ))
      }
      case NegLeftRule( p, _, a, m ) => handleNegRule( proof, p, a, m, NegLeftRule.computeAux, NegLeftRule.apply )
      case NegRightRule( p, _, a, m ) => handleNegRule( proof, p, a, m, NegLeftRule.computeAux, NegRightRule.apply )
      case DefinitionLeftRule( p, _, a, m ) => handleDefRule( proof, p, a, m, 1, DefinitionLeftRule.apply )
      case DefinitionRightRule( p, _, a, m ) => handleDefRule( proof, p, a, m, 0, DefinitionRightRule.apply )
      case EquationLeft1Rule( p1, p2, _, e, a, m ) => handleEqRule( proof, p1, p2, e, a, m, 1, EquationLeft1Rule.apply )
      case EquationLeft2Rule( p1, p2, _, e, a, m ) => handleEqRule( proof, p1, p2, e, a, m, 1, EquationLeft2Rule.apply )
      case EquationRight1Rule( p1, p2, _, e, a, m ) => handleEqRule( proof, p1, p2, e, a, m, 0, EquationRight1Rule.apply )
      case EquationRight2Rule( p1, p2, _, e, a, m ) => handleEqRule( proof, p1, p2, e, a, m, 0, EquationRight2Rule.apply )
      case CutRule( p1, p2, _, a1, a2 ) => {
        val new_symbol_map = copyMapToAncestor( symbol_map )
        val new_inst_map = copyMapToAncestor( inst_map )
        val new_cut_ancs = copySetToAncestor( cut_ancs )
        // TODO: in principle, don't have to add stuff to symbol_map, inst_map because we don't care
        val new_p1 = skolemize( p1, new_symbol_map + (a1 -> Stream.Empty), new_inst_map + (a1 -> Nil), new_cut_ancs + a1 )
        val new_p2 = skolemize( p2, new_symbol_map + (a2 -> Stream.Empty), new_inst_map + (a2 -> Nil), new_cut_ancs + a2 )
        val ret = CutRule( new_p1._1, new_p2._1, new_p1._2( a1 ), new_p2._2( a2 ) )
        (ret, copyMapToDescendant( proof, ret, new_p1._2 ++ new_p2._2))
      }
    }
  }
  
  def debug(msg: String,  proof : LKProof, aux : List[FormulaOccurrence], formulas : List[HOLFormula], terms: List[LambdaExpression]) = {
    println("====== DEBUG: "+ msg)
    println("== endsequent: "+proof.root.toStringSimple)
    println("== auxiliaries:")
    aux map  ((x:FormulaOccurrence) => println("== "+x.formula.toStringSimple))
    println("==")
    println("== formulas:")
    formulas map  ((x:HOLFormula) => println(x.toStringSimple))
    println("==")
    println("== terms:")
    terms map  ((x:LambdaExpression) => println("== "+x.toStringSimple))
    println()
  }

  def handleEqRule( proof: LKProof, p1: LKProof, p2: LKProof, e: FormulaOccurrence, a: FormulaOccurrence, m: FormulaOccurrence,
    pol: Int, constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence, HOLFormula) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      cut_ancs: Set[FormulaOccurrence]
    ) = {
        val (new_aux, new_main) = if (!cut_ancs.contains( m ) ) 
          (sk( a.formula, pol, inst_map( m ), symbol_map( m ) ), sk( m.formula, pol, inst_map( m ), symbol_map( m ) ))
        else 
          (a.formula, m.formula)
        val new_symbol_map = copyMapToAncestor( symbol_map )
        val new_inst_map = copyMapToAncestor( inst_map )
        val new_cut_ancs = copySetToAncestor( cut_ancs )
        val new_p1 = skolemize( p1, new_symbol_map, new_inst_map, new_cut_ancs )
        val new_p2 = skolemize( p2, new_symbol_map, new_inst_map, new_cut_ancs )
        val ret = constructor( new_p1._1, new_p2._1, new_p1._2( e ), new_p2._2( a ), new_main )
        (ret, copyMapToDescendant( proof, ret, new_p1._2 ++ new_p2._2 ))
  }

  def handleDefRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence, pol: Int,
      constructor: (LKProof, FormulaOccurrence, HOLFormula) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      cut_ancs: Set[FormulaOccurrence]

    ) = {
      //println("skolemizing def aux (pol: " + pol + "): " + a.formula.toStringSimple)
        val (new_aux, new_main) = if (!cut_ancs.contains( m ) ) 
          (sk( a.formula, pol, inst_map( m ), symbol_map( m ) ), sk( m.formula, pol, inst_map( m ), symbol_map( m ) ))
        else 
          (a.formula, m.formula)
      //println("result: " + new_aux.toStringSimple )
      val new_proof = skolemize( p, copyMapToAncestor(symbol_map), 
        copyMapToAncestor(inst_map), copySetToAncestor( cut_ancs ) )
      val ret = constructor( new_proof._1, new_proof._2( a ), new_main )
      (ret, copyMapToDescendant( proof, ret, new_proof._2 ) )
    }


  def handleNegRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence,
      computeAux: HOLFormula => HOLFormula,
      constructor: (LKProof, FormulaOccurrence) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      cut_ancs: Set[FormulaOccurrence]

    ) = {
      val new_proof = skolemize( p, copyMapToAncestor(symbol_map), copyMapToAncestor(inst_map),
        copySetToAncestor( cut_ancs ) )
      val ret = constructor( new_proof._1, new_proof._2( a ) )
      (ret, copyMapToDescendant( proof, ret, new_proof._2 ))
  }

  def handleUnaryRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, weak: HOLFormula, m: FormulaOccurrence,
      computeAux: HOLFormula => HOLFormula,
      constructor: (LKProof, FormulaOccurrence, HOLFormula) => LKProof,
      partition: Stream[ConstantSymbolA] => Stream[ConstantSymbolA])(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      cut_ancs: Set[FormulaOccurrence]

    ) = {
      val new_proof = skolemize( p, 
        copyMapToAncestor(symbol_map).updated( a, partition( symbol_map( m ) ) ), 
        copyMapToAncestor(inst_map),
        copySetToAncestor(cut_ancs) )
      val ret = constructor( new_proof._1, new_proof._2( a ), weak ) 
      (ret, copyMapToDescendant( proof, ret, new_proof._2 ))
  }

  // give even partition function
  // choose right subformula as weak subformula
  def handleUnary1Rule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence,
      pol: Int,
      mainConn: LambdaExpression => Option[(HOLFormula, HOLFormula)],
      computeAux: HOLFormula => HOLFormula,
      constructor: (LKProof, FormulaOccurrence, HOLFormula) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      cut_ancs: Set[FormulaOccurrence]
    ) = {
      val new_main = if (cut_ancs.contains( m )) m.formula else sk( m.formula, pol, inst_map( m ), symbol_map( m ) )
      val weak = mainConn(new_main) match { case Some((_, w)) => w }
      handleUnaryRule( proof, p, a, weak, m, computeAux, constructor, even)
    }

  // switch the arguments of the constructor
  // give odd partition function
  // choose left subformula as weak subformula
  def handleUnary2Rule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence,
      pol: Int,
      mainConn: LambdaExpression => Option[(HOLFormula, HOLFormula)],
      computeAux: HOLFormula => HOLFormula,
      constructor: (LKProof, HOLFormula, FormulaOccurrence) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      cut_ancs: Set[FormulaOccurrence]
    ) = {
      val new_main = if (cut_ancs.contains( m )) m.formula else sk( m.formula, pol, inst_map( m ), symbol_map( m ) )
      val weak = mainConn(new_main) match { case Some((w, _)) => w }
      handleUnaryRule( proof, p, a, weak, m, computeAux,
        (p, fo, f) => constructor(p, f, fo), odd )
    }

  def handleBinaryRule( proof: LKProof, p1: LKProof, p2: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence, m: FormulaOccurrence,
      computeLeftAux: HOLFormula => HOLFormula, computeRightAux: HOLFormula => HOLFormula,
      constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      cut_ancs: Set[FormulaOccurrence]

    ) = {
      val new_symbol_map_left = copyMapToAncestor(symbol_map).updated( a1, even( symbol_map( m ) ) )
      val new_symbol_map_right = copyMapToAncestor(symbol_map).updated( a2, odd( symbol_map( m ) ) )
      val new_inst_map = copyMapToAncestor(inst_map)
      val new_cut_ancs = copySetToAncestor( cut_ancs )
      val new_p1 = skolemize( p1, new_symbol_map_left, new_inst_map, new_cut_ancs )
      val new_p2 = skolemize( p2, new_symbol_map_right, new_inst_map, new_cut_ancs )
      val ret = constructor( new_p1._1, new_p2._1, new_p1._2( a1 ), new_p2._2( a2 ) )
      (ret, copyMapToDescendant( proof, ret, new_p1._2 ++ new_p2._2 ))
  }


  def handleContractionRule( proof: LKProof, p: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence,
      constructor: (LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      cut_ancs: Set[FormulaOccurrence]

    ) = {
    val new_proof = skolemize( p, copyMapToAncestor(symbol_map), copyMapToAncestor(inst_map), copySetToAncestor( cut_ancs ) )
    val ret = constructor( new_proof._1, new_proof._2( a1 ), new_proof._2( a2 ) )
    (ret, copyMapToDescendant( proof, ret, new_proof._2 ) )
  }

  def handleWeakQuantRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence, t: HOLExpression,
      pol: Int,
      computeAux: (HOLFormula, HOLExpression) => HOLFormula,
      constructor: (LKProof, FormulaOccurrence, HOLFormula, HOLExpression) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      cut_ancs: Set[FormulaOccurrence]

    ) = {
      println("\nentering weak quant rule for "+proof.root.toStringSimple)
      inst_map map println
      println
      symbol_map map println
      val new_main = if (cut_ancs.contains( m )) m.formula else sk( m.formula, pol, inst_map( m ), symbol_map( m ) )
      println("before: " + m.formula.toStringSimple)
      println("after: " + new_main.toStringSimple)
      val inst_list = inst_map( m )
      val new_inst_map = copyMapToAncestor( inst_map ).updated( a, inst_list :+ t )
      println("recursive call in weak quant rule")
      val new_proof = skolemize( p, copyMapToAncestor( symbol_map ), new_inst_map, copySetToAncestor( cut_ancs ) )

    println("===========!!!===============")
    println(new_proof._1)
    println(new_proof._2(a).formula)
    println(new_main.toStringSimple)
    println(t)

      val ret = constructor( new_proof._1, new_proof._2( a ), new_main, t )
      ( ret, copyMapToDescendant( proof, ret, new_proof._2 ) )
  }


  def handleWeakeningRule( proof: LKProof, p: LKProof, m: FormulaOccurrence,
      pol: Int,
      constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      cut_ancs: Set[FormulaOccurrence]
    ) = {
      val new_main = if (cut_ancs.contains( m )) m.formula else sk( m.formula, pol, inst_map( m ), symbol_map( m ) )
      val new_proof = skolemize( p, copyMapToAncestor( symbol_map - m ), 
        copyMapToAncestor( inst_map - m ), 
        copySetToAncestor( cut_ancs ) )
      val ret = constructor( new_proof._1, new_main )
      ( ret, copyMapToDescendant( proof, ret, new_proof._2 ) + ( m -> ret.prin.head ) )
  }

  def handleStrongQuantRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence, v: HOLVar,
      constructor: (LKProof, FormulaOccurrence, HOLFormula, HOLVar) => LKProof)(implicit
      symbol_map: Map[FormulaOccurrence, Stream[ConstantSymbolA]],
      inst_map: Map[FormulaOccurrence, List[HOLExpression]],
      cut_ancs: Set[FormulaOccurrence]
    ) = {
      println("\nentering strong quant rule for "+proof.root.toStringSimple)
      if (!cut_ancs.contains( m ) )
      {
        val sym_stream = symbol_map( m )
        val sym = sym_stream.head
        println("skolem symbol: " + sym)
        val skolem_term = Function( sym, inst_map( m ), v.exptype )
        val sub = Substitution( v, skolem_term )
        val sub_proof = applySubstitution( p, sub )
        println("old es: " + p.root)
        sub.map map (( x : (Var,HOLExpression) ) => println("sub: " + x._1 + " -> " + x._2.toStringSimple))
        println("after sub: " + sub_proof._1.root )
        // invert the formula occurrence map.
        val inv_map = sub_proof._2.foldLeft(new HashMap[FormulaOccurrence, FormulaOccurrence])((m, p) => m + (p._2 -> p._1) )
        val new_symbol_map = copyMapToAncestor( symbol_map ).updated( a, sym_stream.tail )
        val new_inst_map = copyMapToAncestor( inst_map )
        val new_cut_ancs = copySetToAncestor( cut_ancs ).foldLeft(new HashSet[FormulaOccurrence])( (s, fo) => if (sub_proof._2.isDefinedAt( fo ) ) s + sub_proof._2( fo ) else s )
        //println("old aux: " + form_map( m ).toStringSimple )
        //println("new aux: " + new_form_map( a ).toStringSimple )
        val new_proof = skolemize( sub_proof._1, inv_map.mapValues( new_symbol_map ), 
          inv_map.mapValues( new_inst_map ),
          new_cut_ancs )
        // FIXME: sub_proof._2 is mutable map, so we have to construct a new immutable one.
        val new_map = new HashMap() ++ ( sub_proof._2.mapValues( new_proof._2 ) )
        ( new_proof._1, copyMap( proof, new_proof._1, new_map ) )
    }
    else
    {
      //println("recursive call in strong quant rule")
      val new_proof = skolemize( p, copyMapToAncestor(symbol_map), copyMapToAncestor(inst_map),
        copySetToAncestor( cut_ancs ) )
      val ret = constructor( new_proof._1, new_proof._2( a ), m.formula, v )
      (ret, copyMapToDescendant( proof, ret, new_proof._2 ))

    }
  }

  def copyMapToAncestor[A]( map: Map[FormulaOccurrence, A] ) =
    map.foldLeft(new HashMap[FormulaOccurrence, A])( (m, p) => m ++ p._1.ancestors.map( a => (a, p._2) ) )
 
  def copySetToAncestor( set: Set[FormulaOccurrence] ) = set.foldLeft( new HashSet[FormulaOccurrence] )( (s, fo) => s ++ fo.ancestors )

  def copyMapToDescendant( old_p: LKProof, new_p: LKProof, 
                           map: Map[FormulaOccurrence, FormulaOccurrence] ) =
    map.foldLeft(new HashMap[FormulaOccurrence, FormulaOccurrence])( (m, p) => {
        val desc = old_p.getDescendantInLowerSequent( p._1 )
        if (desc != None)
          m + (desc.get -> new_p.getDescendantInLowerSequent( p._2 ).get )
        else
          m
      } )

  def copyMap( old_p: LKProof, new_p: LKProof, map: Map[FormulaOccurrence, FormulaOccurrence] ) =
    map.map( p => (old_p.getDescendantInLowerSequent( p._1 ).get,
      p._2 ) )

  def invert( pol: Int ) = 
    if (pol == 0)
      1
    else
      0

  def apply(f: HOLFormula, pol: Int) : HOLFormula = apply( f, pol, SkolemSymbolFactory.getSkolemSymbols )

  def apply(f: HOLFormula, pol: Int, symbols: Stream[ConstantSymbolA]) : HOLFormula = skolemize( f, pol, symbols )


  def skolemize(f: HOLFormula, pol: Int, symbols: Stream[ConstantSymbolA]) = sk( f, pol, Nil, symbols )

  def sk(f: HOLFormula, pol: Int, terms: List[HOLExpression], symbols: Stream[ConstantSymbolA]) : HOLFormula = f match {
    case And(l, r) => And( sk( l , pol, terms, even( symbols ) ), sk( r, pol, terms, odd( symbols ) ) )
    case Or(l, r) => Or( sk( l , pol, terms, even( symbols ) ), sk( r, pol, terms, odd( symbols ) ) )
    case Imp(l, r) => Imp( sk( l , invert( pol ), terms, even( symbols ) ), sk( r, pol, terms, odd( symbols ) ) )
    case Neg(f) => Neg( sk( f, invert( pol ), terms, symbols ) )
    case ExVar(x, f) =>
      if (pol == 1)
      {
        //println( "skolemizing ExQ")
        val sub = Substitution(x, Function( symbols.head, terms, x.exptype ) )

        //println( "substitution: " + sub )
        //println( "before: " + f )
        //println( "after: " + sub( f ) )
        // TODO: should not be necessary to cast here, Formula is closed under substitution
        sk( sub( f ).asInstanceOf[HOLFormula], pol, terms, symbols.tail )
      }
      else // TODO: should not be necessary to cast! try to change it in hol.scala.
        ExVar(x, sk( f, pol, terms :+ x.asInstanceOf[HOLVar], symbols ) )
    case AllVar(x, f) =>
      if (pol == 0)
      {
        //println( "skolemizing AllQ")
        val sub = Substitution(x, Function( symbols.head, terms, x.exptype ) )
        //println( "substitution: " + sub )
        //println( f )
        //println( sub( f ) )
        // TODO: should not be necessary to cast here, Formula is closed under substitution
        val res = sk( sub( f ).asInstanceOf[HOLFormula], pol, terms, symbols.tail )
        //println( "result of skolemization: " + res )
        res
      }
      else // TODO: should not be necessary to cast! try to change it in hol.scala.
        AllVar(x, sk( f, pol, terms :+ x.asInstanceOf[HOLVar], symbols ) )
    case Atom(_,_) => f
  }
}

