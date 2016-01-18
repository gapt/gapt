package at.logic.gapt.proofs

import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic.tactics._
import at.logic.gapt.proofs.lk.LKProof

package object gaptic {
  // LK Tactics

  def axiomLog( l: String ) = new LogicalAxiomTactic( Option( l ) )

  def axiomLog = new LogicalAxiomTactic()

  def axiomTop = TopAxiomTactic

  def axiomBot = BottomAxiomTactic

  def axiomRefl = ReflexivityAxiomTactic

  def axiomTh = TheoryAxiomTactic

  def axiom = AxiomTactic

  def negL( applyToLabel: String ) = new NegLeftTactic( Some( applyToLabel ) )

  def negL = new NegLeftTactic()

  def negR( applyToLabel: String ) = new NegRightTactic( Some( applyToLabel ) )

  def negR = new NegRightTactic()

  def andL( applyToLabel: String ) = new AndLeftTactic( Some( applyToLabel ) )

  def andL = new AndLeftTactic()

  def andR( applyToLabel: String ) = new AndRightTactic( Some( applyToLabel ) )

  def andR = new AndRightTactic()

  def orL( applyToLabel: String ) = new OrLeftTactic( Some( applyToLabel ) )

  def orL = new OrLeftTactic()

  def orR( applyToLabel: String ) = new OrRightTactic( Some( applyToLabel ) )

  def orR = new OrRightTactic()

  def impL( applyToLabel: String ) = new ImpLeftTactic( Some( applyToLabel ) )

  def impL = new ImpLeftTactic()

  def impR( applyToLabel: String ) = new ImpRightTactic( Some( applyToLabel ) )

  def impR = new ImpRightTactic()

  def exL( eigenVariable: Var, applyToLabel: String ) = new ExistsLeftTactic( Some( eigenVariable ), Some( applyToLabel ) )

  def exL( eigenVariable: Var ) = new ExistsLeftTactic( eigenVariable = Some( eigenVariable ) )

  def exL( applyToLabel: String ) = new ExistsLeftTactic( applyToLabel = Some( applyToLabel ) )

  def exL = new ExistsLeftTactic()

  def exR( term: LambdaExpression, instantiationLabel: String, applyToLabel: String ) = new ExistsRightTactic( term, instantiationLabel, Some( applyToLabel ) )

  def exR( term: LambdaExpression, instantiationLabel: String ) = new ExistsRightTactic( term, instantiationLabel )

  def allL( term: LambdaExpression, instantiationLabel: String, applyToLabel: String ) = new ForallLeftTactic( term, instantiationLabel, Some( applyToLabel ) )

  def allL( term: LambdaExpression, instantiationLabel: String ) = new ForallLeftTactic( term, instantiationLabel )

  def allR( eigenVariable: Var, applyToLabel: String ) = new ForallRightTactic( Some( eigenVariable ), Some( applyToLabel ) )

  def allR( eigenVariable: Var ) = new ForallRightTactic( eigenVariable = Some( eigenVariable ) )

  def allR( applyToLabel: String ) = new ForallRightTactic( applyToLabel = Some( applyToLabel ) )

  def allR = new ForallRightTactic()

  def cut( h: HOLFormula, c: String ) = CutTactic( h, c )

  def eqL( eq: String, fm: String ) = EqualityLeftTactic( eq, fm )

  def eqR( eq: String, fm: String ) = EqualityRightTactic( eq, fm )

  def defL( l: String, r: HOLFormula ) = DefinitionLeftTactic( l, r )

  def defR( l: String, r: HOLFormula ) = DefinitionRightTactic( l, r )

  // Meta

  def insert( proof: LKProof ) = InsertTactic( proof )

  def repeat( t: Tactical ) = RepeatTactic( t )

  // Complex

  def decompose = DecomposeTactic

  def destruct( l: String ) = new DestructTactic( Some( l ) )

  def destruct = new DestructTactic()

  def chain( h: String ) = ChainTactic( h )

  def prop = PropTactic

  def prover9 = Prover9Tactic

  def forget( l: String ) = ForgetTactic( l )

}
