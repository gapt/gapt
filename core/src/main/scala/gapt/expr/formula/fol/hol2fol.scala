package gapt.expr.formula.fol

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.expr.formula.constants.AndC
import gapt.expr.formula.constants.ExistsC
import gapt.expr.formula.constants.ForallC
import gapt.expr.formula.constants.ImpC
import gapt.expr.formula.constants.NegC
import gapt.expr.formula.constants.OrC
import gapt.expr.formula.hol.HOLFunction
import gapt.expr.formula.hol._
import gapt.expr.subst.Substitution
import gapt.expr.ty.FunctionType
import gapt.expr.ty.To
import gapt.expr.ty.Ty
import gapt.expr.util
import gapt.expr.util.freeVariables
import gapt.proofs.HOLSequent
import gapt.proofs.context.Context

object reduceHolToFol extends reduceHolToFol
/**
 * Creates a FOL formula from a HOL formula, but applies transformations which do _not_ preserve validity!
 * Transformations applied:
 *
 *  - Replace all subterms (\x.t[v]) by a function q_n(v). The scope parameter is needed to pass existing term-constant
 *    mappings.
 *  - Change the type of constants and variables s.t. they are first order (i.e. Const("c", To->Ti) is mapped to
 *    FOLConst("c",Ti)
 *  - Logical operators inside the term structure are replaced by first order terms
 *
 * @note Make sure you need all of these tricks. To only replace abstraction subterms, use [[replaceAbstractions]].
 *
 */
class reduceHolToFol {

  private def folexp2term( exp: FOLExpression ) = exp match {
    case e: FOLTerm => exp.asInstanceOf[FOLTerm]
    case _          => throw new Exception( "Cannot cast " + exp + " to a fol term!" + exp.getClass )
  }

  /**
   * Apply method for a formula when scope needs to passed on in a recursion.
   * @param formula the formula to convert
   * @return a pair of the reduced formula and the updated scope
   */
  def apply( formula: Formula )( implicit definition: Hol2FolDefinitions ): FOLFormula =
    convertHolFormulaToFolFormula( replaceAbstractions( formula ) )

  /**
   * Apply method for a an expression when scope needs to passed on in a recursion.
   * @param term the expression to convert
   * @return a pair of the reduced expression and the updated scope
   */
  def apply( term: Expr )( implicit definition: Hol2FolDefinitions ): FOLExpression =
    ( replaceAbstractions( term ) ) match {
      case f: Formula => convertHolFormulaToFolFormula( f )
      case t          => convertHolTermToFolTerm( t )
    }

  /**
   * Assumes we are on the logical level of the hol formula - all types are
   * mapped to i, i>o or i>i>o respectively
   */
  private def convertHolFormulaToFolFormula( formula: Formula ): FOLFormula = {
    formula match {
      case Top()    => Top()
      case Bottom() => Bottom()
      case Neg( f ) =>
        Neg( convertHolFormulaToFolFormula( f ) )
      case And( f1, f2 ) =>
        And(
          convertHolFormulaToFolFormula( f1 ),
          convertHolFormulaToFolFormula( f2 ) )
      case Or( f1, f2 ) =>
        Or(
          convertHolFormulaToFolFormula( f1 ),
          convertHolFormulaToFolFormula( f2 ) )
      case Imp( f1, f2 ) =>
        Imp(
          convertHolFormulaToFolFormula( f1 ),
          convertHolFormulaToFolFormula( f2 ) )
      case All( v: Var, f ) =>
        All(
          convertHolVariableToFolVariable( v ),
          convertHolFormulaToFolFormula( f ) )
      case Ex( v: Var, f ) =>
        Ex(
          convertHolVariableToFolVariable( v ),
          convertHolFormulaToFolFormula( f ) )
      case Const( n, To, _ ) =>
        FOLAtom( n, Nil )
      case Atom( Const( n, _, _ ), as ) =>
        FOLAtom( n, as.map { convertHolTermToFolTerm } )
      case Atom( Var( n, _ ), as ) =>
        FOLAtom( n, as.map { convertHolTermToFolTerm } )
      case HOLFunction( Const( n, _, _ ), as ) =>
        FOLAtom( n, as.map { convertHolTermToFolTerm } )
      case HOLFunction( Var( n, _ ), as ) =>
        FOLAtom( n, as.map { convertHolTermToFolTerm } )
    }
  }

  private def convertHolVariableToFolVariable( v: Var ): FOLVar =
    FOLVar( v.name )

  //if we encountered an atom, we need to convert logical formulas to the term level too
  private def convertHolTermToFolTerm( term: Expr ): FOLTerm = {
    term match {
      case e: FOLTerm       => e // if it's already FOL - great, we are done.
      case Var( n, _ )      => FOLVar( n )
      case Const( n, _, _ ) => FOLConst( n )
      //we cannot use the logical symbols directly because they are treated differently by the Function matcher
      case Neg( n )         => FOLFunction( NegC.name, List( convertHolTermToFolTerm( n ) ) )
      case And( n1, n2 )    => FOLFunction( AndC.name, List( convertHolTermToFolTerm( n1 ), convertHolTermToFolTerm( n2 ) ) )
      case Or( n1, n2 )     => FOLFunction( OrC.name, List( convertHolTermToFolTerm( n1 ), convertHolTermToFolTerm( n2 ) ) )
      case Imp( n1, n2 )    => FOLFunction( ImpC.name, List( convertHolTermToFolTerm( n1 ), convertHolTermToFolTerm( n2 ) ) )
      case All( v: Var, n ) =>
        FOLFunction( ForallC.name, List( convertHolTermToFolTerm( v ).asInstanceOf[FOLVar], convertHolTermToFolTerm( n ) ) )
      case Ex( v: Var, n ) =>
        FOLFunction( ExistsC.name, List( convertHolTermToFolTerm( v ).asInstanceOf[FOLVar], convertHolTermToFolTerm( n ) ) )
      case Atom( head, ls ) =>
        FOLFunction( head.toString, ls.map( x => folexp2term( convertHolTermToFolTerm( x ) ) ) )
      case HOLFunction( Const( name, _, _ ), ls ) =>
        FOLFunction( name, ls.map( x => folexp2term( convertHolTermToFolTerm( x ) ) ) )
      case _ =>
        throw new IllegalArgumentException(
          // for cases of higher order atoms and functions
          "Cannot reduce hol term: " + term.toString + " to fol as it is a higher order variable function or atom" )
    }
  }

}

object invertBijectiveMap {
  def apply[A, B]( map: Map[A, B] ): Map[B, A] =
    map.map[B, A] { _.swap }
}

/**
 * Definitions of the form cₜ(x₁,...,xₙ) := t(x₁,...,xₙ), where c is a constant
 * and t is a term having as only free variables x₁,...,xₙ.
 * @param context The context with respect to which these definitions are made.
 * In particular the context defines the already used names.
 */
class Hol2FolDefinitions( implicit val context: Context = Context.default ) {

  type Definiendum = Expr
  type Definiens = Expr

  private var definitions: Map[Definiendum, Definiens] = Map()

  private val nameGenerator = context.newNameGenerator

  /**
   * Looks up the defined expression.
   * @param expression An expression t(s₁,...,sₙ).
   * @return The defined expression cₜ(s₁,...,sₙ).
   * If there is no definition of the form cₜ(x₁,...,xₙ) ↔ t(x₁,...,xₙ),
   * then such a definition is created where cₜ is a new constant that does
   * not intersect the context.
   */
  def getDefinedExpression( expression: Definiens ): Definiendum = {
    addDefinitionIfNecessary( expression )
    val Some( ( e, m ) ) = getMatchingDefiniens( expression )
    m( invertBijectiveMap( definitions )( e ) )
  }

  private def addDefinitionIfNecessary( expression: Definiens ): Unit = {
    getMatchingDefiniens( expression ) match {
      case None =>
        val freeVars = freeVariables( expression ).toList
        val constant = Const(
          freshConstantName,
          Abs.Block( freeVars, expression ).ty )
        definitions += Apps( constant, freeVars ) -> expression
      case _ =>
    }
  }

  def getDefiningExpression( expression: Definiendum ): Option[Definiens] = {
    for {
      ( c, m ) <- getMatchingDefiniendum( expression )
      d <- definitions.get( c )
    } yield {
      m( d )
    }
  }

  private def getMatchingDefiniendum( expression: Expr ): Option[( Expr, Substitution )] = {
    definitions.keys.view
      .map { e => e -> util.syntacticMatching( e, expression ) }
      .collectFirst { case ( e, Some( m ) ) => ( e, m ) }
  }

  private def getMatchingDefiniens( expression: Expr ): Option[( Expr, Substitution )] = {
    definitions.values.view
      .map { e => e -> util.syntacticMatching( e, expression ) }
      .collectFirst { case ( e, Some( m ) ) => ( e, m ) }
  }

  // FIXME This test is currently useless
  override def equals( obj: Any ): Boolean =
    obj match {
      case o: Hol2FolDefinitions => o.definitions == definitions
      case _                     => false
    }

  private def freshConstantName: String =
    nameGenerator.freshWithIndex { n => s"q_{${n + 1}}" }

  // FIXME These methods only exist to maintain compatibility with legacy

  def toMap: Map[Expr, Expr] = definitions

  def toLegacyMap: Map[Expr, String] = definitions.map {
    case ( Apps( Const( n, _, _ ), _ ), e ) => e -> n
  }

  def lookupByName( name: String ): Option[Expr] =
    definitions
      .find { case ( Apps( c: Const, _ ), _ ) => c.name == name }
      .map { _._2 }
}

object replaceAbstractions {

  def apply( expression: Expr )( implicit definitions: Hol2FolDefinitions ): Expr =
    new replaceAbstractions( definitions )( expression )

  def apply( formula: Formula )( implicit definitions: Hol2FolDefinitions ): Formula =
    ( new replaceAbstractions( definitions ) )( formula )
}

/**
 * Replace lambda-abstractions by constants.
 *
 * Each abstraction in an [[gapt.proofs.HOLSequent]] is replaced by a separate constant symbol; the used
 * constants are returned in a Map.
 */
class replaceAbstractions( private val definitions: Hol2FolDefinitions ) {

  def apply( formula: Formula ): Formula =
    this.apply( formula.asInstanceOf[Expr] ).asInstanceOf[Formula]

  def apply( expression: Expr ): Expr = expression match {
    // leave quantifiers intact
    case Ex( v, f ) =>
      Ex( v, this.apply( f ) )
    case All( v, f ) =>
      All( v, this.apply( f ) )
    case App( e1, e2 ) =>
      App( this.apply( e1 ), this.apply( e2 ) )
    case _: Abs =>
      abstractExpression( expression )
    case _ => expression
  }

  private def abstractExpression( expression: Expr ): Expr = {
    definitions.getDefinedExpression( expression )
  }
}

/**
 * Replaces the constants introduced by [[replaceAbstractions]] with the
 * original lambda-abstractions.
 *
 * Two lambda abstractions that are matching may have the same abstracting
 * constant. However no effort is made to detect matching lambda abstractions in
 * order to minimize the number of definitions.
 */
object undoReplaceAbstractions {

  def apply( sequent: HOLSequent, definitions: Hol2FolDefinitions ): HOLSequent =
    sequent.map { undoReplaceAbstractions( _, definitions ) }

  def apply( f: Formula, definitions: Hol2FolDefinitions ): Formula =
    apply( f.asInstanceOf[Expr], definitions ).asInstanceOf[Formula]

  /**
   * Replace all occurrences of defined constants by their abstractions.
   *
   * @param expression The expression in which definitions are unfolded.
   * @param definitions The definition to be be unfolded.
   * @return An expression obtained from `expression` by unfolding all the
   * constants defined in `h2fDefinitions` by their defining term.
   */
  def apply( expression: Expr, definitions: Hol2FolDefinitions ): Expr = {
    HOLPosition.getPositions( expression ).foldLeft( expression ) {
      ( e, p ) =>
        expression( p ) match {
          case Apps( _: Const, _ ) =>
            definitions.getDefiningExpression( expression( p ) ).map {
              e.replace( p, _ )
            }.getOrElse( e )
          case _ => e
        }
    }
  }
}

/**
 * Introducing abstractions and converting to fol changes more complex types to fol compatible ones. With changeTypeIn
 * you can change them back.
 */
object changeTypeIn {

  type TypeMap = Map[String, Ty]

  /**
   * Maps types of constants and variables to the given types.
   *
   * @param expression The expression in which the types are to be replaced.
   * @param typeMap Specifies the names of constants and variables whose type
   *                is to be replaced by the associated type.
   * @return An expression obtained from `expression` by replacing the types of leaf-occurrences of variables and
   *         constants by the given types. The types of inner constants and variables are changed according
   *         to the new types of their arguments.
   */
  def apply( expression: Expr, typeMap: TypeMap ): Expr = expression match {
    case v @ Var( n, _ ) =>
      typeMap.get( n ).map { Var( n, _ ) }.getOrElse( v )
    case c @ Const( n, _, _ ) =>
      typeMap.get( n ).map { Const( n, _ ) }.getOrElse( c )
    case HOLFunction( Const( f, FunctionType( r, _ ), _ ), as ) =>
      val newAs = as.map { changeTypeIn( _, typeMap ) }
      val newTs = newAs.map { _.ty }
      HOLFunction( Const( f, FunctionType( r, newTs ) ), newAs )
    case HOLFunction( Var( x, FunctionType( r, _ ) ), as ) =>
      val newAs = as.map { changeTypeIn( _, typeMap ) }
      val newTs = newAs.map { _.ty }
      HOLFunction( Var( x, FunctionType( r, newTs ) ), newAs )
    case Atom( Const( f, FunctionType( r, _ ), _ ), as ) =>
      val newAs = as.map { changeTypeIn( _, typeMap ) }
      val newTs = newAs.map { _.ty }
      Atom( Const( f, FunctionType( r, newTs ) ), newAs )
    case Atom( Var( f, FunctionType( r, _ ) ), as ) =>
      val newAs = as.map { changeTypeIn( _, typeMap ) }
      val newTs = newAs.map { _.ty }
      Atom( Const( f, FunctionType( r, newTs ) ), newAs )
    case Neg( x ) =>
      Neg( changeTypeIn( x, typeMap ) )
    case And( s, t ) =>
      And( changeTypeIn( s, typeMap ), changeTypeIn( t, typeMap ) )
    case Or( s, t ) =>
      Or( changeTypeIn( s, typeMap ), changeTypeIn( t, typeMap ) )
    case Imp( s, t ) =>
      Imp( changeTypeIn( s, typeMap ), changeTypeIn( t, typeMap ) )
    case All( x, f ) =>
      val newX = typeMap.get( x.name ).map { Var( x.name, _ ) }.getOrElse( x )
      All( newX, changeTypeIn( f, typeMap ) )
    case Ex( x, f ) =>
      val newX = typeMap.get( x.name ).map { Var( x.name, _ ) }.getOrElse( x )
      Ex( newX, changeTypeIn( f, typeMap ) )
    case Abs( x, t ) =>
      val newX = typeMap.get( x.name ).map { Var( x.name, _ ) }.getOrElse( x )
      Abs( newX, changeTypeIn( t, typeMap ) )
    case App( s, t ) =>
      App( changeTypeIn( s, typeMap ), changeTypeIn( t, typeMap ) )
    case _ =>
      throw new Exception( "Unhandled case of a HOL Formula! " + expression )
  }

  /**
   * @see `changeTypeIn.apply( Expr, TypeMap )`.
   */
  def apply( e: Formula, tmap: TypeMap ): Formula =
    changeTypeIn( e.asInstanceOf[Expr], tmap ).asInstanceOf[Formula]

  def apply( fs: HOLSequent, tmap: TypeMap ): HOLSequent = HOLSequent(
    fs.antecedent.map( x => changeTypeIn( x, tmap ) ),
    fs.succedent.map( x => changeTypeIn( x, tmap ) ) )
}

