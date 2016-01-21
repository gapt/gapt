///*
// * Struct.scala
// *
// */
//
//package at.logic.gapt.proofs.ceres_omega.struct
//
//import at.logic.gapt.proofs.HOLSequent
//import at.logic.gapt.proofs.lk._
//import at.logic.gapt.proofs.lk.base._
//import at.logic.gapt.proofs.lksk.{ LabelledOccSequent, UnaryLKskProof, LabelledFormulaOccurrence }
//import at.logic.gapt.proofs.occurrences.{ defaultFormulaOccurrenceFactory, FormulaOccurrence }
//import at.logic.gapt.proofs.shlk._
//import at.logic.gapt.expr._
//import at.logic.gapt.expr.SymbolA
//import at.logic.gapt.utils.ds.Multisets.Multiset
//import at.logic.gapt.utils.ds.Multisets._
//import at.logic.gapt.utils.ds.trees._
//import at.logic.gapt.proofs.ceres_omega.clauseSets.StandardClauseSet._
//import at.logic.gapt.utils.logging.Logger
//import scala.math.max
//
//trait Struct {
//  def formula_equal( that: Struct ): Boolean
//  def size(): Int //total number of nodes
//  def alternations(): Int //number of alternations (includes duals)
//}
//
//// Times is done as an object instead of a case class since
//// it has a convenience constructor (with empty auxFOccs)
//object Times {
//  def apply( left: Struct, right: Struct, auxFOccs: List[FormulaOccurrence] ): Times =
//    new Times( left, right, auxFOccs )
//
//  def apply( left: Struct, right: Struct ): Times =
//    apply( left, right, Nil )
//
//  def unapply( s: Struct ) = s match {
//    case t: Times => Some( ( t.left, t.right, t.auxFOccs ) )
//    case _        => None
//  }
//}
//
//class Times( val left: Struct, val right: Struct, val auxFOccs: List[FormulaOccurrence] ) extends Struct {
//  override def toString(): String = "(" + left + " ⊗ " + right + ")"
//  override def formula_equal( s: Struct ) = s match {
//    case Times( x, y, aux ) => left.formula_equal( x ) && right.formula_equal( y ) &&
//      aux.diff( auxFOccs ).isEmpty && auxFOccs.diff( aux ).isEmpty
//    case _ => false
//  }
//
//  override def size() = 1 + left.size() + right.size()
//  override def alternations() = {
//    ( left, right ) match {
//      case ( Times( _, _, _ ), Times( _, _, _ ) ) => max( left.alternations(), right.alternations() )
//      case ( Times( _, _, _ ), _ )                => max( left.alternations(), 1 + right.alternations() )
//      case ( _, Times( _, _, _ ) )                => max( 1 + left.alternations(), right.alternations() )
//      case _                                      => 1 + max( left.alternations(), right.alternations() )
//    }
//  }
//
//}
//
//case class Plus( left: Struct, right: Struct ) extends Struct {
//  override def toString(): String = "(" + left + " ⊕ " + right + ")"
//  override def formula_equal( s: Struct ) = s match {
//    case Plus( x, y ) => left.formula_equal( x ) && right.formula_equal( y )
//    case _            => false
//  }
//  override def size() = 1 + left.size() + right.size()
//  override def alternations() = {
//    ( left, right ) match {
//      case ( Plus( _, _ ), Plus( _, _ ) ) => max( left.alternations(), right.alternations() )
//      case ( Plus( _, _ ), _ )            => max( left.alternations(), 1 + right.alternations() )
//      case ( _, Plus( _, _ ) )            => max( 1 + left.alternations(), right.alternations() )
//      case _                              => 1 + max( left.alternations(), right.alternations() )
//    }
//  }
//}
//case class Dual( sub: Struct ) extends Struct {
//  override def toString(): String = "~(" + sub + ")"
//  override def formula_equal( s: Struct ) = s match {
//    case Dual( x ) => sub.formula_equal( x )
//    case _         => false
//  }
//  override def size() = 1 + sub.size()
//  override def alternations() = {
//    sub match {
//      case Dual( _ ) => sub.alternations
//      case _         => 1 + sub.size
//    }
//  }
//}
//case class A( fo: FormulaOccurrence ) extends Struct { // Atomic Struct
//  override def toString(): String = fo.formula.toString
//  override def formula_equal( s: Struct ) = s match {
//    case A( x ) => fo.formula syntaxEquals ( x.formula )
//    case _      => false
//  }
//
//  override def size() = 1
//  override def alternations() = 0
//}
//case object EmptyTimesJunction extends Struct {
//  override def toString(): String = "ε⊗"
//  override def formula_equal( s: Struct ) = s match {
//    case EmptyTimesJunction => true
//    case _                  => false
//  }
//  override def size() = 1
//  override def alternations() = 0
//}
//case object EmptyPlusJunction extends Struct {
//  override def toString(): String = "ε⊕"
//  override def formula_equal( s: Struct ) = s match {
//    case EmptyPlusJunction => true
//    case _                 => false
//  }
//  override def size() = 1
//  override def alternations() = 0
//}
//
///* convenience object allowing to create and match a set of plus nodes */
//object PlusN {
//  def apply( l: List[Struct] ): Struct = l match {
//    case Nil      => EmptyPlusJunction
//    case x :: Nil => x
//    case x :: xs  => Plus( x, PlusN( xs ) )
//  }
//
//  def unapply( s: Struct ): Option[List[Struct]] = Some( unapply_( s ) )
//
//  def unapply_( s: Struct ): List[Struct] = s match {
//    case Plus( l, r ) => unapply_( l ) ++ unapply_( r )
//    case _            => s :: Nil
//  }
//}
//
//// since case classes may be DAGs, we give a method to convert to a tree
//// (for, e.g. displaying purposes)
//
//object structToExpressionTree {
//  def apply( s: Struct ): Tree[LambdaExpression] = s match {
//    case A( f )                  => LeafTree( f.formula )
//    case Dual( sub )             => UnaryTree( DualC(), apply( sub ) )
//    case Times( left, right, _ ) => BinaryTree( TimesC(), apply( left ), apply( right ) )
//    case Plus( left, right )     => BinaryTree( PlusC(), apply( left ), apply( right ) )
//    case EmptyTimesJunction      => LeafTree( EmptyTimesC() )
//    case EmptyPlusJunction       => LeafTree( EmptyPlusC() )
//  }
//
//  // constructs struct Tree without empty leaves.
//  def prunedTree( s: Struct ): Tree[LambdaExpression] = s match {
//    case A( f )      => LeafTree( f.formula )
//    case Dual( sub ) => UnaryTree( DualC(), prunedTree( sub ) )
//    case Times( left, right, _ ) =>
//      val l = prunedTree( left )
//      val r = prunedTree( right )
//      if ( l.isInstanceOf[LeafTree[LambdaExpression]] && ( l.vertex == EmptyTimesC || l.vertex == EmptyPlusC ) )
//        if ( r.isInstanceOf[LeafTree[LambdaExpression]] && ( r.vertex == EmptyTimesC || r.vertex == EmptyPlusC ) ) LeafTree( EmptyTimesC() )
//        else r
//      else if ( r.isInstanceOf[LeafTree[LambdaExpression]] && ( r.vertex == EmptyTimesC || r.vertex == EmptyPlusC ) ) l
//      else BinaryTree( TimesC(), l, r )
//    case Plus( left, right ) =>
//      val l = prunedTree( left )
//      val r = prunedTree( right )
//      if ( l.isInstanceOf[LeafTree[LambdaExpression]] && ( l.vertex == EmptyTimesC || l.vertex == EmptyPlusC ) )
//        if ( r.isInstanceOf[LeafTree[LambdaExpression]] && ( r.vertex == EmptyTimesC || r.vertex == EmptyPlusC ) ) LeafTree( EmptyPlusC() )
//        else r
//      else if ( r.isInstanceOf[LeafTree[LambdaExpression]] && ( r.vertex == EmptyTimesC || r.vertex == EmptyPlusC ) ) l
//      else BinaryTree( PlusC(), l, r )
//    case EmptyTimesJunction => LeafTree( EmptyTimesC() )
//    case EmptyPlusJunction  => LeafTree( EmptyPlusC() )
//  }
//
//  // We define some symbols that represent the operations of the struct
//
//  case object TimesSymbol extends SymbolA {
//    def unique = "TimesSymbol"
//    override def toString = "⊗"
//    def toCode = "TimesSymbol"
//  }
//
//  case object PlusSymbol extends SymbolA {
//    def unique = "PlusSymbol"
//    override def toString = "⊕"
//    def toCode = "PlusSymbol"
//  }
//
//  case object DualSymbol extends SymbolA {
//    def unique = "DualSymbol"
//    override def toString = "∼"
//    def toCode = "DualSymbol"
//  }
//
//  case object EmptyTimesSymbol extends SymbolA {
//    def unique = "EmptyTimesSymbol"
//    override def toString = "ε_⊗"
//    def toCode = "EmptyTimesSymbol"
//  }
//
//  case object EmptyPlusSymbol extends SymbolA {
//    def unique = "EmptyPlusSymbol"
//    override def toString = "ε_⊕"
//    def toCode = "EmptyPlusSymbol"
//  }
//
//  object TimesC extends MonomorphicLogicalC( TimesSymbol.toString, To -> ( To -> To ) )
//  object PlusC extends MonomorphicLogicalC( PlusSymbol.toString, To -> ( To -> To ) )
//  object DualC extends MonomorphicLogicalC( DualSymbol.toString, To -> To )
//  object EmptyTimesC extends MonomorphicLogicalC( EmptyTimesSymbol.toString, To )
//  object EmptyPlusC extends MonomorphicLogicalC( EmptyPlusSymbol.toString, To )
//}
//
///**
// * Returns s.toString with color coding of struct operators. When a big struct is loaded in the cli, the string truncation
// * can mess up the terminal, therefore this is not the default behaviour.
// */
//object coloredStructString {
//  def apply( s: Struct ) = s match {
//    case A( fo ) =>
//      fo.formula.toString
//    case Dual( sub ) =>
//      Console.GREEN + "~(" + Console.RESET + sub + Console.GREEN + ")" + Console.RESET
//    case Times( left, right, _ ) =>
//      Console.RED + "(" + Console.RESET + left + Console.RED + " ⊗ " + Console.RESET + right + Console.RED + ")" + Console.RESET
//    case Plus( left, right ) =>
//      Console.BLUE + "(" + Console.RESET + left + Console.BLUE + " ⊕ " + Console.RESET + right + Console.BLUE + ")" + Console.RESET
//    case EmptyPlusJunction  => Console.RED + "ε" + Console.RESET
//    case EmptyTimesJunction => Console.BLUE + "ε" + Console.RESET
//  }
//}
//
//// some stuff for schemata
//
//// cut configurations: one using multisets of formulas (to relate different proof definitions)
//// and one using FormulaOccurrences (if we are only considering a single proof definition)
//object TypeSynonyms {
//  type CutConfiguration = ( Multiset[HOLFormula], Multiset[HOLFormula] )
//  type CutOccurrenceConfiguration = Set[FormulaOccurrence]
//}
//object cutConfToString {
//  def apply( cc: TypeSynonyms.CutConfiguration ) = {
//    def str( m: Multiset[HOLFormula] ) = m.foldLeft( "" )( ( s, f ) => s + { if ( s != "" ) ", " else "" } + f.toString )
//    str( cc._1 ) + " | " + str( cc._2 )
//  }
//}
//
//// In the construction of schematized clause sets, we use symbols
//// that contain a name and a cut-configuration. This class represents
//// such symbols.
//class ClauseSetSymbol( val name: String, val cut_occs: TypeSynonyms.CutConfiguration ) extends SymbolA {
//
//  override def toString() = {
//    val nice_name: String = name match {
//      case "\\psi" | "psi"       => "ψ"
//      case "\\chi" | "chi"       => "χ"
//      case "\\varphi" | "varphi" => "φ"
//      case "\\phi" | "phi"       => "ϕ"
//      case "\\rho" | "rho"       => "ρ"
//      case "\\sigma" | "sigma"   => "σ"
//      case "\\tau" | "tau"       => "τ"
//      case _                     => name
//    }
//    "cl^{" + nice_name + ",(" + cutConfToString( cut_occs ) + ")}"
//  }
//}
//
//object StructCreators extends Logger {
//  def size( s: Struct ): Int = size( s, 0 )
//  //TODO:make tailrecursive
//  def size( s: Struct, n: Int ): Int = s match {
//    case A( _ )             => n
//    case Dual( x )          => size( x, n + 1 )
//    case Plus( l, r )       => size( l, size( r, n + 1 ) )
//    case Times( l, r, _ )   => size( l, size( r, n + 1 ) )
//    case EmptyPlusJunction  => n
//    case EmptyTimesJunction => n
//  }
//
//  val nLine = sys.props( "line.separator" )
//
//  def toFormula( s: Struct ): HOLFormula =
//    transformStructToClauseSet( s ).foldLeft[HOLFormula]( Top() )( ( f, c ) =>
//      And( f, c.toFormula ) )
//
//  // TODO this should really disappear.
//  def toOccurrence( f: HOLFormula, so: OccSequent ) =
//    {
//      defaultFormulaOccurrenceFactory.createFormulaOccurrence( f, Nil )
//    }
//
//  def extract( p: LKProof ): Struct = extract( p, getCutAncestors( p ) )
//  def extract( p: LKProof, predicate: HOLFormula => Boolean ): Struct = extract( p, getCutAncestors( p, predicate ) )
//
//  def extract( p: LKProof, cut_occs: Set[FormulaOccurrence] ): Struct = p match {
//    case Axiom( so ) => // in case of axioms of the form A :- A with labelled formulas, proceed as in Daniel's PhD thesis
//      {
//        debug( "0 " + cut_occs + "  " );
//        so match {
//          case lso: LabelledOccSequent if lso.l_antecedent.size == 1 && lso.l_succedent.size == 1 =>
//            handleLabelledAxiom( lso, cut_occs )
//          case _ => handleAxiom( so, cut_occs )
//        }
//      }
//    case UnaryLKProof( _, upperProof, _, _, _ ) => {
//      debug( "1 " + cut_occs + "  " );
//      handleUnary( upperProof, cut_occs )
//    }
//    case BinaryLKProof( _, upperProofLeft, upperProofRight, _, aux1, aux2, _ ) =>
//      debug( "2 " + cut_occs + "  " );
//      handleBinary( upperProofLeft, upperProofRight, aux1 :: aux2 :: Nil, cut_occs )
//    case UnaryLKskProof( _, upperProof, _, _, _ ) =>
//      debug( "3 " + cut_occs + "  " );
//      handleUnary( upperProof, cut_occs )
//    case _ => throw new Exception( "Missing rule in StructCreators.extract: " + p.rule )
//  }
//
//  def handleLabelledAxiom( lso: LabelledOccSequent, cut_occs: Set[FormulaOccurrence] ) = {
//    val left = lso.l_antecedent.toList.head
//    val right = lso.l_succedent.toList.head
//    val ant = if ( cut_occs.contains( left ) )
//      Dual( A( new LabelledFormulaOccurrence( left.formula, Nil, right.skolem_label ) ) ) :: Nil
//    else
//      Nil
//    val suc = if ( cut_occs.contains( right ) )
//      A( new LabelledFormulaOccurrence( right.formula, Nil, left.skolem_label ) ) :: Nil
//    else
//      Nil
//    makeTimesJunction( ant ::: suc, Nil )
//  }
//
//  def handleAxiom( so: OccSequent, cut_occs: Set[FormulaOccurrence] ) = {
//    val cutAncInAntecedent = so.antecedent.toList.filter( x => cut_occs.contains( x ) ).map( x => Dual( A( x ) ) ) //
//    val cutAncInSuccedent = so.succedent.toList.filter( x => cut_occs.contains( x ) ).map( x => A( x ) )
//    makeTimesJunction( cutAncInAntecedent ::: cutAncInSuccedent, Nil )
//  }
//
//  def handleUnary( upperProof: LKProof, cut_occs: Set[FormulaOccurrence] ) =
//    extract( upperProof, cut_occs )
//
//  def handleBinary( upperProofLeft: LKProof, upperProofRight: LKProof, l: List[FormulaOccurrence], cut_occs: Set[FormulaOccurrence] ) = {
//    if ( cut_occs.contains( l.head ) )
//      Plus( extract( upperProofLeft, cut_occs ), extract( upperProofRight, cut_occs ) )
//    else
//      Times( extract( upperProofLeft, cut_occs ), extract( upperProofRight, cut_occs ), l )
//  }
//
//  def makeTimesJunction( structs: List[Struct], aux: List[FormulaOccurrence] ): Struct = structs match {
//    case Nil        => EmptyTimesJunction
//    case s1 :: Nil  => s1
//    case s1 :: tail => Times( s1, makeTimesJunction( tail, aux ), aux )
//  }
//}
//
