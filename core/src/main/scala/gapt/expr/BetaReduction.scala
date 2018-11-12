package gapt.expr

import gapt.expr.hol.universalClosure
import gapt.proofs.Context

import scala.annotation.tailrec
import scala.collection.mutable

case class ReductionRule( lhs: Expr, rhs: Expr ) {
  require( lhs.ty == rhs.ty )
  require(
    freeVariables( rhs ).subsetOf( freeVariables( lhs ) ),
    s"Right-hand side of rule contains variables ${
      freeVariables( rhs ) -- freeVariables( lhs ) mkString ", "
    } which are not in the left hand side:\n"
      + ( lhs === rhs ) )

  val Apps( lhsHead @ Const( lhsHeadName, _, _ ), lhsArgs ) = lhs
  val lhsArgsSize = lhsArgs.size

  val isNonLinear: Boolean = {
    val seen = mutable.Set[Var]()
    def go( e: Expr ): Boolean =
      e match {
        case App( a, b )      => go( a ) || go( b )
        case Abs( _, _ )      => true
        case Const( _, _, _ ) => false
        case v: Var =>
          seen( v ) || { seen += v; false }
      }
    go( lhs )
  }

  val nonVarArgs: Set[Int] =
    lhsArgs.zipWithIndex.filterNot( _._1.isInstanceOf[Var] ).map( _._2 ).toSet

  val structuralRecArgs: Set[Int] =
    lhsArgs.zipWithIndex.collect {
      case ( Apps( _: Const, vs ), i ) if vs.forall( _.isInstanceOf[Var] ) =>
        i
    }.toSet

  val normalizeArgs: Set[Int] =
    if ( isNonLinear ) lhsArgs.indices.toSet else nonVarArgs -- structuralRecArgs

  val whnfArgs: Set[Int] =
    structuralRecArgs -- normalizeArgs
}
object ReductionRule {
  implicit def apply( rule: ( Expr, Expr ) ): ReductionRule =
    ReductionRule( rule._1, rule._2 )

  implicit def apply( atom: Formula ): ReductionRule = {
    val Eq( lhs, rhs ) = atom
    ReductionRule( lhs, rhs )
  }
}

case class Normalizer( rules: Set[ReductionRule] ) {
  val headMap = Map() ++ rules.groupBy( _.lhsHeadName ).mapValues { rs =>
    val normalizeArgs = rs.flatMap( _.normalizeArgs )
    val whnfArgs = rs.flatMap( _.whnfArgs ) -- normalizeArgs
    ( rs, whnfArgs, normalizeArgs )
  }

  def +( rule: ReductionRule ): Normalizer =
    Normalizer( rules + rule )

  def toFormula = And( rules.map { case ReductionRule( lhs, rhs ) => universalClosure( lhs === rhs ) } )

  def replaceTy( ty: Ty, oldTy: Ty, newTy: Ty ): Ty = {
    ty match {
      case ty if ty == oldTy => newTy
      case TArr( tyA, tyB )  => TArr( replaceTy( tyA, oldTy, newTy ), replaceTy( tyB, oldTy, newTy ) )
      case ty                => ty
    }
  }

  def commute( block: Expr, appOrArg: Either[Expr, Expr] ): Expr = {
    block match {
      case Apps( Const( "handle", ty, params ), as ) =>
        val newCatchB = appOrArg match {
          case Left( app_ )  => app_( as( 1 ) )
          case Right( arg_ ) => as( 1 )( arg_ )
        }
        //val handle = hoc"handle{?a ?c}: exn > ?c > (?a > ?c)"
        val App( f, arg ) = newCatchB
        val a = params( 0 )
        val c = newCatchB.ty
        val newTy = ty"exn" ->: c ->: ( a ->: c )
        //val newParams = params.map( replaceTy( _, params( 1 ), newCatchB.ty ) )
        val newParams = List( a, c )
        val newHandle = Const( "handle", newTy, newParams )

        Apps( newHandle, Seq( as( 0 ), newCatchB ) )

      case Abs( v, arg ) =>
        appOrArg match {
          case Left( app_ )  => Abs( v, app_( arg ) )
          case Right( arg_ ) => Abs( v, arg( arg_ ) )
        }
    }
  }

  object SplitEfq {
    def unapply( xs: List[Expr] ): Option[( List[Expr], Expr, List[Expr] )] = {
      val index = xs.indexWhere {
        case Apps( Const( "efq", _, _ ), _ ) => true
        case _                               => false
      }
      if ( index == -1 ) {
        None
      } else {
        val ( front, efq :: back ) = xs.splitAt( index )
        Some( ( front, efq, back ) )
      }
    }
  }
  object SplitTryCatch {
    def unapply( xs: List[Expr] ): Option[( List[Expr], Expr, List[Expr] )] = {
      val index = xs.indexWhere {
        case Apps( Const( "tryCatch", _, _ ), _ ) => true
        case _                                    => false
      }
      if ( index == -1 ) {
        None
      } else {
        val ( front, tc :: back ) = xs.splitAt( index )
        Some( ( front, tc, back ) )
      }
    }
  }

  def normalize( expr: Expr ): Expr = {
    //println( s"normalize $expr" )
    val res = whnf( expr ) match {
      case Apps( hd_, as_ ) =>
        as_ match {

          // Commuting conversion (left) for try/catch
          case SplitTryCatch( front, Apps( Const( "tryCatch", ty, params ), tryCatchBlocks ), back ) if hd_.toUntypedAsciiString != "handle" =>
            println( s"cc left: commuting ${hd_( front )}" )
            println( s"before cc left: tryCatch.ty: $ty" )
            //println( s"input:\n$expr" )
            //println( s"commuting:\n${hd_( front )}" )

            //val tryCatch = hoc"tryCatch{?a ?c}: ((?a > exn) > ?c) > (?a > ?c) > ?c"
            val tryCatchBlocksCommuted = tryCatchBlocks.map( commute( _, Left( hd_( front ) ) ) )
            val ( aTry ->: _ ) ->: cTry = tryCatchBlocksCommuted( 0 ).ty
            val ( aCatch ->: cCatch ) = tryCatchBlocksCommuted( 1 ).ty
            assert( aTry == aCatch )
            assert( cTry == cCatch )
            val a = aTry
            val c = cTry
            val tmpTy = ( ( a ->: ty"exn" ) ->: c ) ->: ( a ->: c ) ->: c
            //val tmpParams = params.map( replaceTy( _, params( 1 ), tryBlock.ty ) )
            val tmpParams = List( a, c )
            val newTryCatch = Const( "tryCatch", tmpTy, tmpParams )
            val res = Apps( newTryCatch, tryCatchBlocksCommuted ++ back )
            println( s"after cc left: tryCatch.ty: $tmpTy" )
            normalize( res )
          // raise left
          case SplitEfq( front, Apps( Const( "efq", _, params ), as2_ ), back ) =>
            println( "raise left" )
            val newEfq = Const( "efq", as2_( 0 ).ty ->: expr.ty, List( expr.ty ) )
            val res = normalize( newEfq( as2_( 0 ) ) )
            res
          case _ =>
            val nHd = hd_ match {
              case Abs.Block( xs, e ) if xs.nonEmpty =>
                Abs.Block( xs, normalize( e ) )
              case _ =>
                hd_
            }
            val nArgs = as_.map( normalize )
            println( s"hd: $hd_" )
            //println( s"args: ${as_.mkString( "\nnextarg:\n" )}" )
            println( s"nHd: $nHd" )
            //println( s"nArgs: $nArgs" )

            // raise idem
            // efq(efq(V))
            if ( nArgs.length > 0 ) {
              ( hd_, nArgs( 0 ) ) match {
                case ( Const( "efq", _, _ ), Apps( Const( "efq", _, _ ), innerArgs ) ) =>
                  println( "raise idem" )
                  //nArgs( 0 )
                  hd_( innerArgs )
                case _ =>
                  Apps( nHd, nArgs )
              }
            } else
              Apps( nHd, nArgs )
        }
    }
    // subject reduction property
    if ( expr.ty != res.ty )
      throw new Exception( s"subject reduction property violated: ${expr.ty} != ${res.ty} (expr: $expr, res: $res" )
    //println( s"result of normalizing $expr\n$res" )
    res
  }

  @tailrec
  final def whnf( expr: Expr ): Expr =
    reduce1( expr ) match {
      case Some( expr_ ) => whnf( expr_ )
      case None          => expr
    }

  def reduce1( expr: Expr ): Option[Expr] = {
    val Apps( hd, as ) = expr
    hd match {
      case Abs.Block( vs, hd_ ) if vs.nonEmpty && as.nonEmpty =>
        val n = math.min( as.size, vs.size )
        Some( Apps( Substitution( vs.take( n ) zip as.take( n ) )( Abs.Block( vs.drop( n ), hd_ ) ), as.drop( n ) ) )
      // raise right
      case Const( "efq", _, _ ) if as.size > 1 =>
        println( "raise right" )
        val newEfq = Const( "efq", as( 0 ).ty ->: expr.ty, List( expr.ty ) )
        Some( newEfq( as( 0 ) ) )
      //Some( hd( as( 0 ) ) )
      case Const( "efq", _, _ ) if as.size == 1 =>
        // If normalize(as(0)) reduces to a tryCatch, it means that that the tryCatch returns an exception
        // variable, we thus know that handle simp and handle/raise didn't apply, hence we commute efq
        normalize( as( 0 ) ) match {
          case Apps( Const( "tryCatch", _, _ ), tryCatchBlocks ) =>
            // raise/handle
            println( "raise/handle" )
            val tryCatchBlocksCommuted = tryCatchBlocks.map( commute( _, Left( hd ) ) )
            val ( aTry ->: _ ) ->: cTry = tryCatchBlocksCommuted( 0 ).ty
            val ( aCatch ->: cCatch ) = tryCatchBlocksCommuted( 1 ).ty
            assert( aTry == aCatch )
            assert( cTry == cCatch )
            val a = aTry
            val c = cTry
            val tmpTy = ( ( a ->: ty"exn" ) ->: c ) ->: ( a ->: c ) ->: c
            //val tmpParams = params.map( replaceTy( _, params( 1 ), tryBlock.ty ) )
            val tmpParams = List( a, c )
            val newTryCatch = Const( "tryCatch", tmpTy, tmpParams )
            Some( Apps( newTryCatch, tryCatchBlocksCommuted ) )
          case _ =>
            println( s"raise other: efq const: $hd" )
            //Some( normalize(hd(normalize(as(0))) ))
            None
        }
      // Commuting conversion (right) for try/catch
      case Const( "tryCatch", ty, params ) if as.size >= 3 =>
        println( s"cc right: commuting ${as( 2 )}" )
        println( s"before cc right: tryCatch.ty: $ty" )
        //println( s"input:\n$expr" )
        //println( s"commuting:\n${as( 2 )}" )
        //val tryB = commute( normalize( as( 0 ) ), Right( normalize( as( 2 ) ) ) )
        val tryB = commute( as( 0 ), Right( as( 2 ) ) )
        //val catchB = commute( normalize( as( 1 ) ), Right( normalize( as( 2 ) ) ) )
        val catchB = commute( as( 1 ), Right( as( 2 ) ) )
        val Abs( _, arg ) = tryB
        val newTryCatch = Const( "tryCatch", replaceTy( ty, params( 1 ), arg.ty ), params.map( replaceTy( _, params( 1 ), arg.ty ) ) )
        val res = Apps( newTryCatch, List( tryB, catchB ) ++ as.drop( 3 ) )
        println( s"cc right: res:\n$res" )
        println( s"after cc right: tryCatch.ty: ${newTryCatch.ty}" )
        //Some( normalize( res ) )
        Some( res )
      case Const( "tryCatch", ty, params ) =>
        val tryB = as( 0 )
        val Abs( exnV, arg ) = tryB
        if ( !freeVariables( arg ).contains( exnV ) ) {
          // handle simp
          println( s"handle simp" )
          Some( arg )
        } else {
          // TODO: make sure not to reduce here before all commuting conversions are done, as.size >= 3 case for cc right is before this case. what about cc left?
          println( "handle/raise" )
          // handle/raise
          println( s"free vars: ${freeVariables( arg )}" )
          val res = normalize( arg ) match {
            case ntb @ App( Const( "efq", _, _ ), App( thrownExn, thrownVal ) ) =>
              val App( App( Const( "handle", _, _ ), App( caughtExn, exnVar ) ), catchB ) = as( 1 )
              println( s"thrown exn: $thrownExn" )
              println( s"caught exn: $caughtExn" )
              if ( thrownExn == caughtExn ) {
                println( s"caught exception $caughtExn" )
                Some( le"(^${exnVar.asInstanceOf[Var]} $catchB)$thrownVal" )
              } else {
                // TODO throw further
                println( s"throw further: normalized try block: $ntb" )
                //Some( tryB )
                Some( ntb )
              }
            case t =>
              // Exception var y in FV(V), but not raised
              // Expecting a raise in try block. Do not reduce and keep $expr. Should be handled by raise/handle case. I.e., at some point the exception in the block will be raised due to soundness of the proof system..
              println( s"Expecting a raise in try block. Is $t\ndo not reduce and keep $expr. Should be handled by raise/handle case. I.e., at some point the exception in the block will be raised due to soundness of the proof system." )
              assert( params( 1 ) == ty"exn" )
              None
            //throw new Exception( s"Expecting a raise in try block. Is $t" )
          }
          res
        }
      case hd @ Const( c, _, _ ) =>
        if ( c == "existsElim" ) {
          println( "reducing existsElim" )
        }
        headMap.get( c ).flatMap {
          case ( rs, whnfArgs, normalizeArgs ) =>
            val as_ = as.zipWithIndex.map {
              case ( a, i ) if whnfArgs( i )      => whnf( a )
              case ( a, i ) if normalizeArgs( i ) => normalize( a )
              case ( a, _ )                       => a
            }
            rs.view.flatMap { r =>
              syntacticMatching( r.lhs, Apps( hd, as_.take( r.lhsArgsSize ) ) ).map { subst =>
                Apps( subst( r.rhs ), as_.drop( r.lhsArgsSize ) )
              }
            }.headOption
        }
      case _ =>
        None
    }
    //}
  }

  def isDefEq( a: Expr, b: Expr ): Boolean =
    normalize( a ) == normalize( b )
}

object Normalizer {
  def apply( rules: Traversable[ReductionRule] ): Normalizer =
    Normalizer( rules.toSet )

  def apply( rules: ReductionRule* ): Normalizer =
    Normalizer( rules )
}

object normalize {
  def apply( expr: Expr )( implicit ctx: Context = null ): Expr =
    if ( ctx == null ) BetaReduction.normalize( expr )
    else ctx.normalizer.normalize( expr )
}

object BetaReduction extends Normalizer( Set() ) {
  def betaNormalize( expression: Expr ): Expr =
    normalize( expression )

  def betaNormalize( f: Formula ): Formula =
    betaNormalize( f: Expr ).asInstanceOf[Formula]
}
