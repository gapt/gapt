package at.logic.gapt.examples
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lkOld._

object inductionExamples extends Script {

  // Variables and constants
  val ( x, y, z ) = ( FOLVar( "x" ), FOLVar( "y" ), FOLVar( "z" ) )
  val ( a, b, c ) = ( FOLVar( "α" ), FOLVar( "β" ), FOLVar( "γ" ) )
  val zero = FOLConst( "0" )

  // Successor and addition
  def s( x: FOLTerm ) = FOLFunction( "s", List( x ) )

  def plus( x: FOLTerm, y: FOLTerm ) = FOLFunction( "+", List( x, y ) )

  // Instances of addition axioms
  def add0( v: FOLTerm ) = Eq( plus( v, zero ), v )

  def addS( u: FOLTerm, v: FOLTerm ) =
    Eq(
      plus( u, s( v ) ),
      s( plus( u, v ) )
    )

  // Instances of associativity and reflexivity
  def assoc( x: FOLTerm, y: FOLTerm, z: FOLTerm ) = Eq( plus( plus( x, y ), z ), plus( x, plus( y, z ) ) )

  def ref( t: FOLTerm ) = Eq( t, t )

  // Universally quantified equations
  val ForAllAssoc = All.Block( List( x, y, z ), assoc( x, y, z ) )
  val ForAllAdd0 = All( x, add0( x ) )
  val ForAllAddS = All.Block( List( x, y ), addS( x, y ) )

  val inductionBase1 =
    Axiom(
      Nil,
      List( ref( plus( a, b ) ) )
    )

  val inductionBase2 =
    EquationRightRule(
      inductionBase1,
      inductionBase1.root.succedent.head,
      add0( b ),
      Eq( plus( a, b ), plus( a, plus( b, zero ) ) )
    )

  val inductionBase3 =
    EquationRightRule(
      inductionBase2,
      inductionBase2.root.succedent.head,
      add0( plus( a, b ) ),
      assoc( a, b, zero )
    )

  val inductionBase4 =
    ForallLeftRule(
      inductionBase3,
      inductionBase3.root.antecedent.head,
      ForAllAdd0,
      plus( a, b )
    )

  val inductionBase5 = ContractionMacroRule(
    ForallLeftRule(
      inductionBase4,
      inductionBase4.root.antecedent.head,
      ForAllAdd0,
      b
    )
  )

  val inductionBase =
    ContractionMacroRule(
      ForallLeftRule(
        inductionBase4,
        inductionBase4.root.antecedent.head,
        ForAllAdd0,
        b
      )
    )

  val inductionStep1 =
    Axiom(
      Nil,
      List( ref( plus( plus( a, b ), s( c ) ) ) )
    )

  val inductionStep2 =
    ForallLeftBlock(
      EquationRightRule(
        inductionStep1,
        inductionStep1.root.succedent.head,
        addS( plus( a, b ), c ),
        Eq( plus( plus( a, b ), s( c ) ), s( plus( plus( a, b ), c ) ) )
      ),
      ForAllAddS,
      List( plus( a, b ), c )
    )

  val inductionStep3 =
    EquationRightRule(
      inductionStep2,
      inductionStep2.root.succedent.head,
      assoc( a, b, c ),
      Eq( plus( plus( a, b ), s( c ) ), s( plus( a, plus( b, c ) ) ) )
    )

  val inductionStep4 =
    ForallLeftBlock(
      EquationRightRule(
        inductionStep3,
        inductionStep3.root.succedent.head,
        addS( a, plus( b, c ) ),
        Eq( plus( plus( a, b ), s( c ) ), plus( a, s( plus( b, c ) ) ) )
      ),
      ForAllAddS,
      List( a, plus( b, c ) )
    )

  val inductionStep5 =
    ForallLeftBlock(
      EquationRightRule(
        inductionStep4,
        inductionStep4.root.succedent.head,
        addS( b, c ),
        Eq( plus( plus( a, b ), s( c ) ), plus( a, plus( b, s( c ) ) ) )
      ),
      ForAllAddS,
      List( b, c )
    )

  val inductionStep = ContractionMacroRule( inductionStep5 )

  val inductionProof =
    ForallRightBlock(
      InductionRule(
        inductionBase,
        inductionStep,
        assoc( a, b, zero ),
        assoc( a, b, c ),
        assoc( a, b, s( c ) ),
        c
      ),
      ForAllAssoc,
      List( a, b, c )
    )

}
