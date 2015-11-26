package at.logic.gapt.expr.fol

import at.logic.gapt.expr._
import at.logic.gapt.expr.StringSymbol
import at.logic.gapt.expr.{ Ty, Ti, To }
import at.logic.gapt.utils.logging.Logger

/**
 * This is implements some heuristics to convert a fol formula obtained by
 * [[at.logic.gapt.language.fol.algorithms.replaceAbstractions]] and [[at.logic.gapt.language.fol.algorithms.reduceHolToFol]] back to its original signature.
 * Sometimes, types have to be guessed and the code is poorly tested, so it is unclear
 * how general it is. It works (and is necessary) during the acnf creation of the n-tape proof.
 *
 * To extract a signature, use the [[undoHol2Fol.getSignature]], to to the back translation use
 * [[undoHol2Fol.backtranslate]].
 */
object undoHol2Fol extends Logger {
  override def loggerName = "HOL2FOLLogger"
  /**
   * Translate the fol formula e to a hol formula over the given signature for constants and variables.
   * @param e the fol formula.
   * @param sig_vars a mapping fol name to hol var with appropriate type
   * @param sig_consts a mapping fol name to hol const with appropriate type
   * @param abssymbol_map a mapping fol constant name to a lambda expression (obtained by replaceAbstractions)
   * @return the changed formula
   */
  def backtranslate(
    e:             LambdaExpression,
    sig_vars:      Map[String, List[Var]],
    sig_consts:    Map[String, List[Const]],
    abssymbol_map: Map[String, LambdaExpression]
  ): HOLFormula =
    backtranslate( e.asInstanceOf[LambdaExpression], sig_vars, sig_consts, abssymbol_map, Some( To ) ).asInstanceOf[HOLFormula]
  /**
   * We do some dirty stuff in here to translate a prover9 term back to the richer type signature of hol proofs, undoing
   * replace abstractions at the same time.
   */
  def backtranslate(
    e:             LambdaExpression,
    sig_vars:      Map[String, List[Var]],
    sig_consts:    Map[String, List[Const]],
    abssymbol_map: Map[String, LambdaExpression],
    expected_type: Option[Ty]
  ): LambdaExpression = {
    e match {
      // --------------- logical structure ------------------------
      case HOLAtom( Const( name, _ ), args ) if sig_consts contains name.toString =>
        val args_ = args.map( backtranslate( _, sig_vars, sig_consts, abssymbol_map, None ) )
        val head = sig_consts( name.toString )( 0 )
        HOLAtom( head, args_ )
      /* case Equation(s, t) =>
      Equation(backtranslate( s, sig_vars, sig_consts, abssymbol_map, None ) ,
      backtranslate( t, sig_vars, sig_consts, abssymbol_map, None ) )
      */
      case Neg( f )    => Neg( backtranslate( f, sig_vars, sig_consts, abssymbol_map ) )
      case And( f, g ) => And( backtranslate( f, sig_vars, sig_consts, abssymbol_map ), backtranslate( g, sig_vars, sig_consts, abssymbol_map ) )
      case Or( f, g )  => Or( backtranslate( f, sig_vars, sig_consts, abssymbol_map ), backtranslate( g, sig_vars, sig_consts, abssymbol_map ) )
      case Imp( f, g ) => Imp( backtranslate( f, sig_vars, sig_consts, abssymbol_map ), backtranslate( g, sig_vars, sig_consts, abssymbol_map ) )
      case All( x, f ) =>
        val f_ = backtranslate( f, sig_vars, sig_consts, abssymbol_map )
        val xcandidates = freeVariables( f_ ).toList.filter( _.name == x.name )
        xcandidates match {
          case Nil        => All( Var( x.sym, x.exptype ).asInstanceOf[Var], f_ )
          case List( x_ ) => All( x_, f_ )
          case _          => throw new Exception( "We have not more than one free variable with name " + x.name + xcandidates.mkString( ": (", ", ", ")" ) )
        }
      case Ex( x, f ) =>
        val f_ = backtranslate( f, sig_vars, sig_consts, abssymbol_map )
        val xcandidates = freeVariables( f_ ).toList.filter( _.name == x.name )
        xcandidates match {
          case Nil        => Ex( Var( x.sym, x.exptype ).asInstanceOf[Var], f_ )
          case List( x_ ) => Ex( x_, f_ )
          case _          => throw new Exception( "We have not more than one free variable with name " + x.name + xcandidates.mkString( ": (", ", ", ")" ) )
        }
      // --------------- term structure ------------------------
      //cases for term replacement
      case Const( name, _ ) if abssymbol_map.contains( name ) =>
        val qterm_ = abssymbol_map( name )
        val qterm: LambdaExpression = freeVariables( qterm_ ).toList.foldRight( qterm_ )( ( v, term ) => Abs( v, term ) )
        expected_type match {
          case Some( expt ) =>
            require( qterm.exptype == expt, "We did a replacement of the symbol " + name + " by " + qterm + " but the type " + qterm.exptype + " is not the expected type " + expected_type )
            qterm
          case None =>
            qterm
        }

      case HOLFunction( Const( name, _ ), args ) if abssymbol_map.contains( name ) =>
        val qterm_ = abssymbol_map( name )
        val qterm: LambdaExpression = freeVariables( qterm_ ).toList.foldRight( qterm_ )( ( v, term ) => Abs( v, term ) )
        val btargs = args.map( x => backtranslate( x.asInstanceOf[LambdaExpression], sig_vars, sig_consts, abssymbol_map, None ) )
        val r = btargs.foldLeft( qterm )( ( term, nextarg ) => App( term, nextarg ) )
        expected_type match {
          case Some( expt ) =>
            require( qterm.exptype == expt, "We did a replacement of the symbol " + name + " by " + qterm + " but the type " + qterm.exptype + " is not the expected type " + expected_type )
            r
          case None =>
            r
        }
      //normal ones
      case HOLFunction( Const( name, _ ), args ) if sig_consts contains name =>
        val btargs = args.map( x => backtranslate( x.asInstanceOf[LambdaExpression], sig_vars, sig_consts, abssymbol_map, None ) )
        val head = sig_consts( name )( 0 ) //we have to pick a candidate somehow, lets go for the first
        HOLFunction( head, btargs )
      case Var( name, Ti ) if sig_vars contains name =>
        val head = sig_vars( name )( 0 ) //we have to pick a candidate somehow, lets go for the first
        head
      case Const( name, Ti ) if sig_consts contains name =>
        val head = sig_consts( name )( 0 ) //we have to pick a candidate somehow, lets go for the first
        head
      case Var( ivy_varname( name ), Ti ) =>
        trace( "Guessing that the variable " + name + " comes from ivy, assigning type i." )
        Var( StringSymbol( name ), Ti ).asInstanceOf[Var]
      case Var( name, Ti ) =>
        throw new Exception( "No signature information for variable " + e )
      case Const( name, _ ) =>
        throw new Exception( "No signature information for const " + e )
      case _ =>
        throw new Exception( "Could not convert subterm " + e )
    }
  }
  val ivy_varname = """(v[0-9]+)""".r
  def getSignature( fs: List[LambdaExpression] ): ( Map[String, Set[Const]], Map[String, Set[Var]] ) =
    fs.foldLeft( ( Map[String, Set[Const]](), Map[String, Set[Var]]() ) )( ( maps, e ) => {
      //println("next "+maps._1.size+":"+maps._2.size)
      getSignature( e, maps._1, maps._2 )
    } )
  def getSignature( e: LambdaExpression, csig: Map[String, Set[Const]], vsig: Map[String, Set[Var]] ): ( Map[String, Set[Const]], Map[String, Set[Var]] ) = e match {
    case v: Var =>
      val name = v.name
      vsig.get( name ) match {
        case Some( list ) if list contains v =>
          ( csig, vsig )
        case Some( list ) =>
          ( csig, vsig + ( ( name, list + v ) ) )
        case None =>
          ( csig, vsig + ( ( name, Set( v ) ) ) )
      }
    case c: Const =>
      val name = c.name
      csig.get( name ) match {
        case Some( list ) if list contains c =>
          ( csig, vsig )
        case Some( list ) =>
          ( csig + ( ( name, list + c ) ), vsig )
        case None =>
          ( csig + ( ( name, Set( c ) ) ), vsig )
      }
    case App( s, t ) =>
      val ( cm1, vm1 ) = getSignature( s, csig, vsig )
      val ( cm2, vm2 ) = getSignature( t, cm1, vm1 )
      val cmtotal = ( cm1.toList ++ cm2.toList ).foldLeft( Map[String, Set[Const]]() )( ( map, elem ) =>
        map.get( elem._1 ) match {
          case None         => map + elem
          case Some( list ) => map + ( ( elem._1, list ++ elem._2 ) )
        } )
      val vmtotal = ( vm1.toList ++ vm2.toList ).foldLeft( Map[String, Set[Var]]() )( ( map, elem ) =>
        map.get( elem._1 ) match {
          case None         => map + elem
          case Some( list ) => map + ( ( elem._1, list ++ elem._2 ) )
        } )
      ( cmtotal, vmtotal )
    case Abs( x @ Var( name, _ ), s ) =>
      val ( cm1, vm1 ) = getSignature( s, csig, vsig )
      vm1.get( name ) match {
        case None =>
          ( cm1, vm1 + ( ( name, Set( x.asInstanceOf[Var] ) ) ) )
        case Some( list ) =>
          ( cm1, vm1 + ( ( name, list + x.asInstanceOf[Var] ) ) )
      }
  }
}
