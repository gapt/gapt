package gapt.expr.formula.fol

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.hol.HOLFunction
import gapt.expr.ty.Ti
import gapt.expr.util.freeVariables
import gapt.expr.ty.To
import gapt.expr.ty.Ty
import gapt.proofs.SequentProof
import gapt.utils.Logger

/**
 * This is implements some heuristics to convert a fol formula obtained by
 * [[gapt.expr.formula.fol.replaceAbstractions]] and [[gapt.expr.formula.fol.reduceHolToFol]] back to its original signature.
 * Sometimes, types have to be guessed and the code is poorly tested, so it is unclear
 * how general it is. It works (and is necessary) during the acnf creation of the n-tape proof.
 *
 * To extract a signature, use the `undoHol2Fol.getSignature`, to to the back translation use
 * `undoHol2Fol.backtranslate`.
 */
object undoHol2Fol {
  val logger = Logger( "undoHol2fol" )

  type Signature = ( Map[String, Set[Const]], Map[String, Set[Var]] )

  /**
   * Translate the fol formula e to a hol formula over the given signature for constants and variables.
   *
   * @param e the fol formula.
   * @param sig_vars a mapping fol name to hol var with appropriate type
   * @param sig_consts a mapping fol name to hol const with appropriate type
   * @param abssymbol_map a mapping fol constant name to a lambda expression (obtained by replaceAbstractions)
   * @return the changed formula
   */
  def backtranslate(
    e:             Expr,
    sig_vars:      Map[String, List[Var]],
    sig_consts:    Map[String, List[Const]],
    abssymbol_map: Map[String, Expr] ): Formula =
    backtranslate( e.asInstanceOf[Expr], sig_vars, sig_consts, abssymbol_map, Some( To ) ).asInstanceOf[Formula]
  /**
   * We do some dirty stuff in here to translate a prover9 term back to the richer type signature of hol proofs, undoing
   * replace abstractions at the same time.
   */
  def backtranslate(
    e:             Expr,
    sig_vars:      Map[String, List[Var]],
    sig_consts:    Map[String, List[Const]],
    abssymbol_map: Map[String, Expr],
    expected_type: Option[Ty] ): Expr = {
    e match {
      // --------------- logical structure ------------------------
      case Atom( Const( name, _, _ ), args ) if sig_consts contains name.toString =>
        val args_ = args.map( backtranslate( _, sig_vars, sig_consts, abssymbol_map, None ) )
        val head = sig_consts( name.toString )( 0 )
        Atom( head, args_ )
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
          case Nil        => All( Var( x.name, x.ty ).asInstanceOf[Var], f_ )
          case List( x_ ) => All( x_, f_ )
          case _          => throw new Exception( "We have not more than one free variable with name " + x.name + xcandidates.mkString( ": (", ", ", ")" ) )
        }
      case Ex( x, f ) =>
        val f_ = backtranslate( f, sig_vars, sig_consts, abssymbol_map )
        val xcandidates = freeVariables( f_ ).toList.filter( _.name == x.name )
        xcandidates match {
          case Nil        => Ex( Var( x.name, x.ty ).asInstanceOf[Var], f_ )
          case List( x_ ) => Ex( x_, f_ )
          case _          => throw new Exception( "We have not more than one free variable with name " + x.name + xcandidates.mkString( ": (", ", ", ")" ) )
        }
      // --------------- term structure ------------------------
      //cases for term replacement
      case Const( name, _, _ ) if abssymbol_map.contains( name ) =>
        val qterm_ = abssymbol_map( name )
        val qterm: Expr = freeVariables( qterm_ ).toList.foldRight( qterm_ )( ( v, term ) => Abs( v, term ) )
        expected_type match {
          case Some( expt ) =>
            require( qterm.ty == expt, "We did a replacement of the symbol " + name + " by " + qterm + " but the type " + qterm.ty + " is not the expected type " + expected_type )
            qterm
          case None =>
            qterm
        }

      case HOLFunction( Const( name, _, _ ), args ) if abssymbol_map.contains( name ) =>
        val qterm_ = abssymbol_map( name )
        val qterm: Expr = freeVariables( qterm_ ).toList.foldRight( qterm_ )( ( v, term ) => Abs( v, term ) )
        val btargs = args.map( x => backtranslate( x.asInstanceOf[Expr], sig_vars, sig_consts, abssymbol_map, None ) )
        val r = btargs.foldLeft( qterm )( ( term, nextarg ) => App( term, nextarg ) )
        expected_type match {
          case Some( expt ) =>
            require( qterm.ty == expt, "We did a replacement of the symbol " + name + " by " + qterm + " but the type " + qterm.ty + " is not the expected type " + expected_type )
            r
          case None =>
            r
        }
      //normal ones
      case HOLFunction( Const( name, _, _ ), args ) if sig_consts contains name =>
        val btargs = args.map( x => backtranslate( x.asInstanceOf[Expr], sig_vars, sig_consts, abssymbol_map, None ) )
        val head = sig_consts( name )( 0 ) //we have to pick a candidate somehow, lets go for the first
        HOLFunction( head, btargs )
      case Var( name, Ti ) if sig_vars contains name =>
        val head = sig_vars( name )( 0 ) //we have to pick a candidate somehow, lets go for the first
        head
      case Const( name, Ti, _ ) if sig_consts contains name =>
        val head = sig_consts( name )( 0 ) //we have to pick a candidate somehow, lets go for the first
        head
      case Var( ivy_varname( name ), Ti ) =>
        logger.debug( "Guessing that the variable " + name + " comes from ivy, assigning type i." )
        Var( name, Ti ).asInstanceOf[Var]
      case Var( name, Ti ) =>
        throw new Exception( "No signature information for variable " + e )
      case Const( name, _, _ ) =>
        throw new Exception( "No signature information for const " + e )
      case _ =>
        throw new Exception( "Could not convert subterm " + e )
    }
  }

  val ivy_varname = """(v[0-9]+)""".r

  def getSignature[F, T <: SequentProof[F, T]]( proof: SequentProof[F, T], extract: F => Expr ): Signature = {
    val exprs = for ( p <- proof.subProofs; f <- p.conclusion.elements map extract ) yield f
    getSignature( exprs.toList )
  }

  def getSignature( fs: List[Expr] ): Signature =
    fs.foldLeft( ( Map[String, Set[Const]](), Map[String, Set[Var]]() ) )( ( maps, e ) => {
      //println("next "+maps._1.size+":"+maps._2.size)
      getSignature( e, maps._1, maps._2 )
    } )
  def getSignature( e: Expr, csig: Map[String, Set[Const]], vsig: Map[String, Set[Var]] ): ( Map[String, Set[Const]], Map[String, Set[Var]] ) = e match {
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
