package at.logic.gapt.expr.fol

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.expr.schema._
import at.logic.gapt.proofs.HOLSequent

object reduceHolToFol extends reduceHolToFol
/**
 * Creates a FOL formula from a HOL formula, but applies transformations which do _not_ preserve validity!
 * Transformations applied:
 *
 *  - Replace all subterms (\x.t) by a constant. The scope parameter is needed to pass existing term-constant mappings.
 *  - Change the type of constants and variables s.t. they are first order (i.e. Const("c", To->Ti) is mapped to FOLConst("c",Ti)
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
   * Convenience method when only a single expression is converted. Multiple expressions need to pass a scope which
   * holds the replacements which happened so far.
   * @param term a HOL expression to convert
   * @return the reduced FOL expression
   */
  def apply( term: LambdaExpression ): FOLExpression = {
    val counter = new { private var state = 0; def nextId = { state = state + 1; state } }
    val emptymap = Map[LambdaExpression, StringSymbol]()
    apply( term, emptymap, counter )._1
  }

  /**
   * Convenience method when only a single formula is converted. Multiple expressions need to pass a scope which
   * holds the replacements which happened so far.
   * @param formula a HOL formula to convert
   * @return the reduced FOL formula
   */
  def apply( formula: HOLFormula ): FOLFormula =
    //inner cast needed to call the correct apply method
    reduceHolToFol( formula.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLFormula]

  /**
   * Convenience method when only a single fsequent is converted. Multiple expressions need to pass a scope which
   * holds the replacements which happened so far.
   * @param fs an fsequent to convert
   * @return the reduced fsequent
   */
  def apply( fs: HOLSequent ): HOLSequent = {
    val counter = new { private var state = 0; def nextId = { state = state + 1; state } }
    val emptymap = Map[LambdaExpression, StringSymbol]()
    apply( fs, emptymap, counter )._1
  }

  /**
   * Convenience method when a single  list of fsequents is converted. Multiple expressions need to pass a scope which
   * holds the replacements which happened so far.
   * @param fs an fsequent to convert
   * @return the reduced fsequent
   */
  def apply( fs: List[HOLSequent] ): List[HOLSequent] = {
    val counter = new { private var state = 0; def nextId = { state = state + 1; state } }
    val emptymap = Map[LambdaExpression, StringSymbol]()
    apply( fs, emptymap, counter )._1
  }

  /**
   * Apply method for a formula when scope needs to passed on in a recursion.
   * @param formula the formula to convert
   * @param scope a mapping of replaced subterms to the constant names which replaced them. you need this for chained applications, like
   *              sequents or lists of formulas.
   * @param id an object with a function which nextId, which provides new numbers.
   * @return a pair of the reduced formula and the updated scope
   */
  def apply( formula: HOLFormula, scope: Map[LambdaExpression, StringSymbol], id: { def nextId: Int } ): ( FOLFormula, Map[LambdaExpression, StringSymbol] ) = {
    val ( scope_, qterm ) = replaceAbstractions( formula, scope, id )
    ( apply_( qterm ).asInstanceOf[FOLFormula], scope_ )
  }

  /**
   * Apply method for a an expression when scope needs to passed on in a recursion.
   * @param term the expression to convert
   * @param scope a mapping of replaced subterms to the constant names which replaced them. you need this for chained applications, like
   *              sequents or lists of formulas.
   * @param id an object with a function which nextId, which provides new numbers.
   * @return a pair of the reduced expression and the updated scope
   */
  def apply( term: LambdaExpression, scope: Map[LambdaExpression, StringSymbol], id: { def nextId: Int } ) = {
    val ( scope_, qterm ) = replaceAbstractions( term, scope, id )
    ( apply_( qterm ), scope_ )
  }

  /**
   * Apply method for a an FSequent when scope needs to passed on in a recursion.
   * @param s the fsequent to convert
   * @param scope a mapping of replaced subterms to the constant names which replaced them. you need this for chained applications, like
   *              sequents or lists of formulas.
   * @param id an object with a function which nextId, which provides new numbers.
   * @return a pair of the reduced expression and the updated scope
   */
  def apply( s: HOLSequent, scope: Map[LambdaExpression, StringSymbol], id: { def nextId: Int } ): ( HOLSequent, Map[LambdaExpression, StringSymbol] ) = {
    val ( scope1, ant ) = s.antecedent.foldLeft( ( scope, List[HOLFormula]() ) )( ( r, formula ) => {
      val ( scope_, f_ ) = replaceAbstractions( formula, r._1, id )
      ( scope_, f_.asInstanceOf[HOLFormula] :: r._2 )
    } )
    val ( scope2, succ ) = s.succedent.foldLeft( ( scope1, List[HOLFormula]() ) )( ( r, formula ) => {
      val ( scope_, f_ ) = replaceAbstractions( formula, r._1, id )
      ( scope_, f_.asInstanceOf[HOLFormula] :: r._2 )
    } )

    ( HOLSequent( ant.reverse map apply_, succ.reverse map apply_ ), scope ++ scope2 )
  }

  /**
   * Apply method for a an FSequent when scope needs to passed on in a recursion.
   * @param fss the fsequent to convert
   * @param scope a mapping of replaced subterms to the constant names which replaced them. you need this for chained applications, like
   *              sequents or lists of formulas.
   * @param id an object with a function which nextId, which provides new numbers.
   * @return a pair of the reduced expression and the updated scope
   */
  def apply( fss: List[HOLSequent], scope: Map[LambdaExpression, StringSymbol], id: { def nextId: Int } ): ( List[HOLSequent], Map[LambdaExpression, StringSymbol] ) = {
    fss.foldRight( ( List[HOLSequent](), scope ) )( ( fs, pair ) => {
      val ( list, scope ) = pair
      val ( fs_, scope_ ) = apply( fs, scope, id )
      ( fs_ :: list, scope_ )
    } )

  }

  private def apply_( f: HOLFormula ): FOLFormula =
    apply_( f.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLFormula]

  //assumes we are on the logical level of the hol formula - all types are mapped to i, i>o or i>i>o respectively
  private def apply_( term: LambdaExpression ): FOLExpression = {
    term match {
      case e: FOLExpression            => e // if it's already FOL - great, we are done.
      case indexedFOVar( name, index ) => FOLVar( name ++ intTermLength( index.asInstanceOf[IntegerTerm] ).toString )
      case foVar( name )               => FOLVar( name )
      case foConst( name )             => FOLConst( name )
      case Const( n, To )              => FOLAtom( n, Nil )
      case Var( n, _ )                 => FOLVar( n )
      case Const( n, _ )               => FOLConst( n )
      case Top()                       => Top()
      case Bottom()                    => Bottom()
      case Neg( n )                    => Neg( apply_( n ).asInstanceOf[FOLFormula] )
      case And( n1, n2 )               => And( apply_( n1 ), apply_( n2 ) )
      case Or( n1, n2 )                => Or( apply_( n1 ), apply_( n2 ) )
      case Imp( n1, n2 )               => Imp( apply_( n1 ), apply_( n2 ) )
      case All( v: Var, n )            => All( apply_( v ).asInstanceOf[FOLVar], apply_( n ) )
      case Ex( v: Var, n )             => Ex( apply_( v ).asInstanceOf[FOLVar], apply_( n ) )
      case HOLAtom( Const( n, _ ), ls ) =>
        FOLAtom( n, ls.map( x => folexp2term( apply_termlevel( x ) ) ) )
      case HOLAtom( Var( n, _ ), ls ) =>
        FOLAtom( n, ls.map( x => folexp2term( apply_termlevel( x ) ) ) )
      case HOLFunction( Const( n, _ ), ls ) =>
        FOLFunction( n, ls.map( x => folexp2term( apply_( x ) ) ) )
      case HOLFunction( Var( n, _ ), ls ) =>
        FOLFunction( n, ls.map( x => folexp2term( apply_( x ) ) ) )

      //this case is added for schema
      case App( func, arg ) => {
        func match {
          case Var( sym, _ ) =>
            val new_arg = apply_( arg ).asInstanceOf[FOLTerm]
            return FOLFunction( sym, new_arg :: Nil )

          case _ =>
            println( "WARNING: FO schema term: " + term )
            throw new Exception( "Probably unrecognized object from schema!" )
        }
      }
      case _ => throw new IllegalArgumentException( "Cannot reduce hol term: " + term.toString + " to fol as it is a higher order variable function or atom" ) // for cases of higher order atoms and functions
    }
  }

  //if we encountered an atom, we need to convert logical formulas to the term level too
  private def apply_termlevel( term: LambdaExpression ): FOLTerm = {
    term match {
      case e: FOLTerm                  => e // if it's already FOL - great, we are done.
      case indexedFOVar( name, index ) => FOLVar( name ++ intTermLength( index.asInstanceOf[IntegerTerm] ).toString )
      case foVar( name )               => FOLVar( name.toString )
      case foConst( name )             => FOLConst( name.toString )
      case Var( n, _ )                 => FOLVar( n )
      case Const( n, _ )               => FOLConst( n )
      //we cannot use the logical symbols directly because they are treated differently by the Function matcher
      case Neg( n )                    => FOLFunction( NegC.name, List( apply_termlevel( n ) ) )
      case And( n1, n2 )               => FOLFunction( AndC.name, List( apply_termlevel( n1 ), apply_termlevel( n2 ) ) )
      case Or( n1, n2 )                => FOLFunction( OrC.name, List( apply_termlevel( n1 ), apply_termlevel( n2 ) ) )
      case Imp( n1, n2 )               => FOLFunction( ImpC.name, List( apply_termlevel( n1 ), apply_termlevel( n2 ) ) )
      case All( v: Var, n ) =>
        FOLFunction( ForallC.name, List( apply_termlevel( v ).asInstanceOf[FOLVar], apply_termlevel( n ) ) )
      case Ex( v: Var, n ) =>
        FOLFunction( ExistsC.name, List( apply_termlevel( v ).asInstanceOf[FOLVar], apply_termlevel( n ) ) )
      case HOLAtom( head, ls ) =>
        FOLFunction( head.toString, ls.map( x => folexp2term( apply_termlevel( x ) ) ) )
      case HOLFunction( Const( name, _ ), ls ) =>
        FOLFunction( name, ls.map( x => folexp2term( apply_termlevel( x ) ) ) )

      //this case is added for schema
      /*
      case App(func,arg) => {
        val nLine = sys.props("line.separator")
      
        func match {
          case Var(sym,_) => {
            val new_arg = apply_(arg).asInstanceOf[FOLTerm]
            return at.logic.gapt.language.fol.Function(new ConstantStringSymbol(sym.toString), new_arg::Nil)
          }
          case _ => println( nLine + "WARNING: FO schema term!" + nLine)
        }
        throw new Exception( nLine + "Probably unrecognized object from schema!" + nLine)
      }
      */

      // This case replaces an abstraction by a function term.
      //
      // the scope we choose for the variant is the Abs itself as we want all abs identical up to variant use the same symbol
      //
      // TODO: at the moment, syntactic equality is used here... This means that alpha-equivalent terms may be replaced
      // by different constants, which is undesirable.
      /*
      case a @ Abs(v, exp) => {
        val sym = scope.getOrElseUpdate(a.variant(new VariantGenerator(new {var idd = 0; def nextId = {idd = idd+1; idd}}, "myVariantName")), ConstantStringSymbol("q_{" + id.nextId + "}"))
        val freeVarList = a.getFreeVariables.toList.sortWith((x,y) => x.toString < y.toString).map(x => apply(x.asInstanceOf[LambdaExpression],scope,id))
        if (freeVarList.isEmpty) FOLConst(sym) else Function(sym, freeVarList.asInstanceOf[List[FOLTerm]])
      }
      */
      case _ => throw new IllegalArgumentException( "Cannot reduce hol term: " + term.toString + " to fol as it is a higher order variable function or atom" ) // for cases of higher order atoms and functions
    }
  }

  //transforms a ground integer term to Int
  private def intTermLength( t: IntegerTerm ): Int = t match {
    case IntZero()  => 0
    case Succ( t1 ) => 1 + intTermLength( t1 )
    case _          => throw new Exception( sys.props( "line.separator" ) + "Error in reduceHolToFol.length(...) !" + sys.props( "line.separator" ) )
  }
}

object replaceAbstractions extends replaceAbstractions

/**
 * Replace lambda-abstractions by constants.
 *
 * Each abstraction in an [[at.logic.gapt.proofs.HOLSequent]] is replaced by a separate constant symbol; the used
 * constants are returned in a Map.
 */
class replaceAbstractions {
  type ConstantsMap = Map[LambdaExpression, StringSymbol]

  def apply( l: List[HOLSequent] ): ( ConstantsMap, List[HOLSequent] ) = {
    val counter = new { private var state = 0; def nextId = { state = state + 1; state } }
    l.foldLeft( ( Map[LambdaExpression, StringSymbol](), List[HOLSequent]() ) )( ( rec, el ) => {
      val ( scope_, f ) = rec
      val ( nscope, rfs ) = replaceAbstractions( el, scope_, counter )
      ( nscope, rfs :: f )

    } )
  }

  def apply( f: HOLSequent, scope: ConstantsMap, id: { def nextId: Int } ): ( ConstantsMap, HOLSequent ) = {
    val ( scope1, ant ) = f.antecedent.foldLeft( ( scope, List[HOLFormula]() ) )( ( rec, formula ) => {
      val ( scope_, f ) = rec
      val ( nscope, nformula ) = replaceAbstractions( formula, scope_, id )
      ( nscope, nformula.asInstanceOf[HOLFormula] :: f )
    } )
    val ( scope2, succ ) = f.succedent.foldLeft( ( scope1, List[HOLFormula]() ) )( ( rec, formula ) => {
      val ( scope_, f ) = rec
      val ( nscope, nformula ) = replaceAbstractions( formula, scope_, id )
      ( nscope, nformula.asInstanceOf[HOLFormula] :: f )
    } )

    ( scope2, HOLSequent( ant.reverse, succ.reverse ) )
  }

  def apply( e: LambdaExpression ): LambdaExpression = {
    val counter = new {
      private var state = 0;

      def nextId = {
        state = state + 1; state
      }
    }
    apply( e, Map[LambdaExpression, StringSymbol](), counter )._2
  }

  def apply( formula: HOLFormula ): HOLFormula =
    apply( formula.asInstanceOf[LambdaExpression] ).asInstanceOf[HOLFormula]

  // scope and id are used to give the same names for new functions and constants between different calls of this method
  def apply( e: LambdaExpression, scope: ConstantsMap, id: { def nextId: Int } ): ( ConstantsMap, LambdaExpression ) = e match {
    case Var( _, _ ) =>
      ( scope, e )
    case Const( _, _ ) =>
      ( scope, e )
    //quantifiers should be kept
    case All( x, f ) =>
      val ( scope_, e_ ) = replaceAbstractions( f, scope, id )
      ( scope_, All( x, e_.asInstanceOf[HOLFormula] ) )
    case Ex( x, f ) =>
      val ( scope_, e_ ) = replaceAbstractions( f, scope, id )
      ( scope_, Ex( x, e_.asInstanceOf[HOLFormula] ) )
    case App( s, t ) =>
      val ( scope1, s1 ) = replaceAbstractions( s, scope, id )
      val ( scope2, t1 ) = replaceAbstractions( t, scope1, id )
      ( scope2, App( s1, t1 ) )
    // This case replaces an abstraction by a function term.
    // the scope we choose for the variant is the Abs itself as we want all abs identical up to variant use the same symbol
    case Abs( v, exp ) =>
      //systematically rename free variables for the index
      //val normalizeda = e.variant(new VariantGenerator(new {var idd = 0; def nextId = {idd = idd+1; idd}}, "myVariantName"))
      //TODO: check if variable renaming is really what we want
      val ( normalizeda, mapping ) = normalizeFreeVariables( e )
      //println("e: "+e)
      //println("norm: "+normalizeda)
      //update scope with a new constant if neccessary
      //println(scope)
      val scope_ = if ( scope contains normalizeda ) scope else scope + ( ( normalizeda, StringSymbol( "q_{" + id.nextId + "}" ) ) )
      //println(scope_)
      val sym = scope_( normalizeda )
      val freeVarList = freeVariables( e ).toList.sortBy( _.toString ).asInstanceOf[List[LambdaExpression]]
      if ( freeVarList.isEmpty )
        ( scope_, Const( sym, e.exptype ) )
      else {
        val c = Const( sym, FunctionType( e.exptype, freeVarList.map( _.exptype ) ) )
        ( scope_, HOLFunction( c, freeVarList ) )
      }
    case _ =>
      throw new Exception( "Unhandled case in abstraction replacement!" + e )

  }
}

object undoReplaceAbstractions extends undoReplaceAbstractions
/**
 * Replaces the constants introduced by [[replaceAbstractions]] with the original lambda-abstractions.
 */
class undoReplaceAbstractions {
  import at.logic.gapt.expr.fol.replaceAbstractions.ConstantsMap

  def apply( fs: HOLSequent, map: ConstantsMap ): HOLSequent = HOLSequent(
    fs.antecedent.map( apply( _, map ) ),
    fs.succedent.map( apply( _, map ) )
  )
  def apply( f: HOLFormula, map: ConstantsMap ): HOLFormula = apply( f.asInstanceOf[LambdaExpression], map ).asInstanceOf[HOLFormula]
  def apply( e: LambdaExpression, map: ConstantsMap ): LambdaExpression = {
    val stringsmap = map.map( x => ( x._2.toString(), x._1 ) ) //inverting the map works because the symbols are unique
    HOLPosition.getPositions( e ).foldLeft( e )( ( exp, position ) =>
      //we check if the position is a constant with an abstraction symbol
      e( position ) match {
        case Const( name, _ ) if stringsmap.contains( name ) =>
          //if yes, we replace it by the original expression
          exp.replace( position, stringsmap( name ) )
        case _ => exp
      } )
  }
}

/**
 * Introducing abstractions and converting to fol changes more complex types to fol compatible ones. With changeTypeIn
 * you can change them back.
 */
object changeTypeIn {
  type TypeMap = Map[String, Ty]

  /* TODO: this broken, since e.g. for (a b) q with type(q)=alpha, type(b)=beta then type(a)=beta > (alpha > gamma)
     we need to actually change the type of a when changing the type of q
    */
  /*
  def oldapply(e:LambdaExpression, tmap : TypeMap) : LambdaExpression = e match {
    case Var(name, ta) =>
      if (tmap.contains(name.toString()))
        e.factory.createVar(name, tmap(name.toString()))
      else
        e
    case App(s,t) => s.factory.createApp(oldapply(s,tmap), oldapply(t,tmap))
    case Abs(x,t) => t.factory.createAbs(oldapply(x,tmap).asInstanceOf[Var], oldapply(t,tmap))
  } */

  //Remark: this only works for changing the type of leaves in the term tree!
  def apply( e: LambdaExpression, tmap: TypeMap ): LambdaExpression = e match {
    case Var( name, ta ) => if ( tmap contains name.toString() ) Var( name, tmap( name.toString() ) ) else
      Var( name, ta )
    case Const( name, ta ) => if ( tmap contains name.toString() ) Const( name, tmap( name.toString() ) ) else
      Const( name, ta )
    case HOLFunction( Const( f, exptype ), args ) =>
      val args_ = args.map( x => apply( x, tmap ) )
      val freturntype = exptype match { case FunctionType( r, _ ) => r }
      val f_ = Const( f, FunctionType( freturntype, args.map( _.exptype ) ) )
      HOLFunction( f_, args_ )
    case HOLFunction( Var( f, exptype ), args ) =>
      val args_ = args.map( x => apply( x, tmap ) )
      val freturntype = exptype match { case FunctionType( r, _ ) => r }
      val f_ = Var( f, FunctionType( freturntype, args.map( _.exptype ) ) )
      HOLFunction( f_, args_ )
    case HOLAtom( Const( f, exptype ), args ) =>
      val args_ = args.map( x => apply( x, tmap ) )
      val f_ = Const( f, FunctionType( To, args.map( _.exptype ) ) )
      HOLAtom( f_, args_ )
    case HOLAtom( Var( f, exptype ), args ) =>
      val args_ = args.map( x => apply( x, tmap ) )
      val f_ = Var( f, FunctionType( To, args.map( _.exptype ) ) )
      HOLAtom( f_, args_ )
    case Neg( x )    => Neg( apply( x, tmap ) )
    case And( s, t ) => And( apply( s, tmap ), apply( t, tmap ) )
    case Or( s, t )  => Or( apply( s, tmap ), apply( t, tmap ) )
    case Imp( s, t ) => Imp( apply( s, tmap ), apply( t, tmap ) )
    case All( x, t ) => All( apply( x.asInstanceOf[Var], tmap ).asInstanceOf[Var], apply( t, tmap ) )
    case Ex( x, t )  => Ex( apply( x.asInstanceOf[Var], tmap ).asInstanceOf[Var], apply( t, tmap ) )
    case Abs( x, t ) => Abs( apply( x.asInstanceOf[Var], tmap ).asInstanceOf[Var], apply( t, tmap ) )
    case App( s, t ) => App( apply( s, tmap ), apply( t, tmap ) )
    case _           => throw new Exception( "Unhandled case of a HOL Formula! " + e )

  }
  def apply( e: FOLTerm, tmap: TypeMap ): FOLTerm = apply( e.asInstanceOf[LambdaExpression], tmap ).asInstanceOf[FOLTerm]
  def apply( e: HOLFormula, tmap: TypeMap ): HOLFormula = apply( e.asInstanceOf[LambdaExpression], tmap ).asInstanceOf[HOLFormula]
  def apply( e: FOLFormula, tmap: TypeMap ): FOLFormula = apply( e.asInstanceOf[LambdaExpression], tmap ).asInstanceOf[FOLFormula]
  def apply( fs: HOLSequent, tmap: TypeMap ): HOLSequent = HOLSequent(
    fs.antecedent.map( x => apply( x, tmap ) ),
    fs.succedent.map( x => apply( x, tmap ) )
  )

  //different names bc of type erasure
  private def holsub( s: Substitution, tmap: TypeMap ): Substitution = Substitution(
    s.map.map( x =>
      ( apply( x._1, tmap ).asInstanceOf[Var], apply( x._2, tmap ) ) )
  )

  private def folsub( s: FOLSubstitution, tmap: TypeMap ): FOLSubstitution = FOLSubstitution( s.folmap.map( x =>
    ( apply( x._1, tmap ).asInstanceOf[FOLVar], apply( x._2, tmap ) ) ) )
}

