package gapt.expr

import java.lang.ClassCastException

import gapt.expr.hol.universalClosure
import gapt.proofs.context.Context
import gapt.utils.Logger

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
  val logger = Logger( "BetaReduction" ); import logger._

  val headMap = Map() ++ rules.groupBy( _.lhsHeadName ).mapValues { rs =>
    val normalizeArgs = rs.flatMap( _.normalizeArgs )
    val whnfArgs = rs.flatMap( _.whnfArgs ) -- normalizeArgs
    ( rs, whnfArgs, normalizeArgs )
  }

  def +( rule: ReductionRule ): Normalizer =
    Normalizer( rules + rule )

  def toFormula = And( rules.map { case ReductionRule( lhs, rhs ) => universalClosure( lhs === rhs ) } )

  def commute( block: Expr, appOrArg: Either[Expr, Expr] ): Expr = {
    debug( "in commute" )
    appOrArg match {
      case Left( app_ )  => app_( block )
      case Right( arg_ ) => block( arg_ )
    }
  }

  object SplitEfq {
    def unapply( xs: List[Expr] ): Option[( List[Expr], Expr, List[Expr] )] = {
      val index = xs.indexWhere {
        case Apps( Const( "efq", _, _ ), _ ) => true
        //case Apps( Const( "exception", _, _ ), _ ) => true
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
    debug( s"normalize begin $expr" )
    val res = whnf( expr ) match {
      case Apps( hd_, as_ ) =>
        as_ match {

          // Commuting conversion (left) for try/catch
          case SplitTryCatch( front, Apps( Const( "tryCatch", ty, params ), tryCatchArgs ), back ) =>

            //debug( s"cc left: commuting ${hd_( front )}" )
            debug( s"cc left" )
            debug( s"before cc left: tryCatch.ty: $ty" )
            val exnVs = tryCatchArgs.take( 2 )
            val tryCatchBlocks = tryCatchArgs.drop( 2 ).take( 2 )
            debug( s"@@@@@@ tryCatch exnVs: $exnVs" )
            //debug( s"input:\n$expr" )
            println( s"commuting:\n${hd_( front )}" )

            //val tryCatch = hoc"tryCatch{?a ?c}: ((?a > exn) > ?c) > (?a > ?c) > ?c"
            val tryCatchBlocksCommuted = tryCatchBlocks.map( commute( _, Left( hd_( front ) ) ) )
            val a = exnVs( 0 ).ty
            val b = exnVs( 1 ).ty
            val c = tryCatchBlocksCommuted( 0 ).ty
            val tmpTy = a ->: b ->: c ->: c ->: c
            //val tmpParams = params.map( replaceTy( _, params( 1 ), tryBlock.ty ) )
            val tmpParams = List( a, b, c )
            val newTryCatch = Const( "tryCatch", tmpTy, tmpParams )
            val res = Apps( newTryCatch, exnVs ++ tryCatchBlocksCommuted ++ back )
            debug( s"after cc left: tryCatch.ty: $tmpTy" )
            normalize( res )
          // raise left
          // TODO: what if efq without exception?
          //       what if we had other EM1, i.e., All x. P |- C  -All x. P |- C
          //case SplitEfq( front, e @ Apps( Const( "exception", TArr(ty1_, TArr(ty2_,_)), params ), as2_ ), back ) =>
          case SplitEfq( front, Apps( Const( "efq", _, params ), as2_ ), back ) =>
            debug( "raise left" )
            val newEfq = Const( "efq", as2_( 0 ).ty ->: expr.ty, List( expr.ty ) )
            val res = normalize( newEfq( as2_( 0 ) ) )
            //val newEfq = Const( "exception", ty1_ ->: ty2_ ->: expr.ty, List( expr.ty ) )
            //val res = normalize( newEfq( as2_) )
            res
          case _ =>
            val nHd = hd_ match {
              case Abs.Block( xs, e ) if xs.nonEmpty =>
                Abs.Block( xs, normalize( e ) )
              case _ =>
                hd_
            }
            val nArgs = as_.map( normalize )
            //debug( s"hd: $hd_" )
            //debug( s"args: ${as_.mkString( "\nnextarg:\n" )}" )
            //debug( s"nHd: $nHd" )
            //debug( s"nArgs: $nArgs" )

            // raise idem
            // efq(efq(V))
            /*
            if ( nArgs.length > 0 ) {
              ( hd_, nArgs( 0 ) ) match {
                case ( Const( "efq", _, _ ), Apps( Const( "efq", _, _ ), innerArgs ) ) =>
                  debug( "raise idem" )
                  //nArgs( 0 )
                  hd_( innerArgs )
                case _ =>
                  Apps( nHd, nArgs )
              }
            } else
            */
            Apps( nHd, nArgs )
        }
    }
    // subject reduction property
    if ( expr.ty != res.ty )
      throw new Exception( s"subject reduction property violated: ${expr.ty} != ${res.ty} (expr: $expr, res: $res" )
    //debug( s"normalize end $res" )
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
        debug( s"beta reduction: ${vs.take( n )}" )
        Some( Apps( Substitution( vs.take( n ) zip as.take( n ) )( Abs.Block( vs.drop( n ), hd_ ) ), as.drop( n ) ) )
      case Const( "try", _, _ ) if as.size > 2 =>
        println( expr )
        val All( alpha, p ) = as( 0 )
        val pPrime = Substitution( alpha, as( 2 ) )( p )
        println( freeVariables( pPrime ) )
        println( normalize( pPrime ) )
        if ( freeVariables( pPrime ).isEmpty && normalize( pPrime ) == hof"true" )
          Some( hof"true" )
        else if ( freeVariables( pPrime ).isEmpty && normalize( pPrime ) == hof"false" ) {
          // TODO: return ${Some(try(n))}, i.e., an exception carrying ${as(2)}, which can be unwrapped in
          //       tryCatch of type ${expr.ty}
          //       exception(n) should be treated like efq in deGroote
          //val res = Some(as(1)(as(2)))
          val res = Some( Const( "exception", as( 1 ).ty ->: as( 2 ).ty ->: expr.ty, List( expr.ty ) )( as( 1 ) )( as( 2 ) ) )
          res

        } else
          None
      case Const( "catch", _, _ ) if as.size == 2 =>
        val Ex( alpha, p ) = as( 0 )
        as( 1 ) match {
          case exp @ Apps( Const( "expair", _, _ ), as_ ) =>
            //assert(normalize(Substitution(alpha, as_(0))(p)) == hof"true")
            Some( exp )
          case _ =>
            None //throw new Exception("error reducing in catch")
        }

      // raise right
      case Const( "exception", _, _ ) if as.size > 2 =>
        debug( "raise right" )
        val newEfq = Const( "exception", as( 0 ).ty ->: as( 1 ).ty ->: expr.ty, List( expr.ty ) )
        Some( newEfq( as( 0 ) )( as( 1 ) ) )
      //Some( hd( as( 0 ) ) )

      /*
      case Const( "efq", _, _ ) if as.size == 1 =>
        // If normalize(as(0)) reduces to a tryCatch, it means that that the tryCatch returns an exception
        // variable, we thus know that handle simp and handle/raise didn't apply, hence we commute efq
        val r = normalize( as( 0 ) )
        debug( s"result of normalize efq arg:\n$r" )
        r match {
          case Apps( Const( "tryCatch", _, _ ), tryCatchBlocks ) =>
            // raise/handle
            debug( "raise/handle" )
            val tryCatchBlocksCommuted = tryCatchBlocks.drop( 1 ).map( commute( _, Left( hd ) ) )
            val exnV = tryCatchBlocks( 0 )
            val aExn ->: _ = exnV.ty
            val cTry = tryCatchBlocksCommuted( 0 ).ty
            val ( aCatch ->: cCatch ) = tryCatchBlocksCommuted( 1 ).ty
            assert( aExn == aCatch )
            assert( cTry == cCatch )
            val a = aExn
            val c = cTry
            val tmpTy = ( a ->: ty"exn" ) ->: c ->: ( a ->: c ) ->: c
            //val tmpParams = params.map( replaceTy( _, params( 1 ), tryBlock.ty ) )
            val tmpParams = List( a, c )
            val newTryCatch = Const( "tryCatch", tmpTy, tmpParams )
            Some( Apps( newTryCatch, exnV :: tryCatchBlocksCommuted ) )
          case _ =>
            debug( s"raise other: efq const: $hd" )
            //Some( normalize(hd(normalize(as(0))) ))
            None
        }
      */
      // Commuting conversion (right) for try/catch
      // (tryCatch v0 v1 tryBlock catchBlock) extraArgs
      case Const( "tryCatch", ty, _ ) if as.size > 4 =>
        println( s"cc right: commuting ${as( 2 )}" )
        debug( s"cc right" )
        debug( s"before cc right: tryCatch.ty: $ty" )
        val exnVs = as.take( 2 )
        debug( s"@@@@@@ tryCatch exnVs: $exnVs" )
        val tryCatchBlocks = as.drop( 2 ).take( 2 )
        val tryCatchBlocksCommuted = tryCatchBlocks.map( commute( _, Right( as( 4 ) ) ) )
        val a = exnVs( 0 ).ty
        val b = exnVs( 1 ).ty
        val c = tryCatchBlocksCommuted( 0 ).ty
        val tmpTy = a ->: b ->: c ->: c ->: c
        //val tmpParams = params.map( replaceTy( _, params( 1 ), tryBlock.ty ) )
        val tmpParams = List( a, b, c )
        val newTryCatch = Const( "tryCatch", tmpTy, tmpParams )
        val res = Apps( newTryCatch, exnVs ++ tryCatchBlocksCommuted ++ as.drop( 5 ) )
        debug( s"cc right: res:\n$res" )
        debug( s"after cc right: tryCatch.ty: ${newTryCatch.ty}" )
        Some( res )

      /*
        debug( s"cc right: commuting ${as( 2 )}" )
        debug( s"before cc right: tryCatch.ty: $ty" )
        //debug( s"input:\n$expr" )
        //debug( s"commuting:\n${as( 2 )}" )
        //val tryB = commute( normalize( as( 0 ) ), Right( normalize( as( 2 ) ) ) )
        val tryB = commute( as( 0 ), Right( as( 2 ) ) )
        //val catchB = commute( normalize( as( 1 ) ), Right( normalize( as( 2 ) ) ) )
        val catchB = commute( as( 1 ), Right( as( 2 ) ) )
        val Abs( _, arg ) = tryB
        val newTryCatch = Const( "tryCatch", replaceTy( ty, params( 1 ), arg.ty ), params.map( replaceTy( _, params( 1 ), arg.ty ) ) )
        val res = Apps( newTryCatch, List( tryB, catchB ) ++ as.drop( 3 ) )
        debug( s"cc right: res:\n$res" )
        debug( s"after cc right: tryCatch.ty: ${newTryCatch.ty}" )
        //Some( normalize( res ) )
        Some( res )
        */
      case Const( "tryCatch", ty, params ) =>
        val exnVs = as.take( 2 ).map( _.asInstanceOf[Var] )
        val tryB = normalize( as( 2 ) )
        val catchB = normalize( as( 3 ) )
        println( freeVariables( tryB ) )
        if ( !freeVariables( tryB ).contains( exnVs( 0 ) ) ) {
          // handle simp
          debug( s"handle simp" )
          Some( tryB )
        } else {
          // TODO: distribute inl over try/exception? otherwise need a second normalize here, which is not right
          val tmp1 = normalize( tryB )
          val tmp2 = normalize( normalize( tryB ) )
          tmp1 match {
            case Const( "true", _, _ ) =>
              Some( le"true" )
            case App( Const( "efq", _, _ ), Apps( Const( "exception", _, _ ), as_ ) ) =>
              assert( as_( 0 ) == exnVs( 0 ) )
              val TBase( _, tyParams ) = exnVs( 1 ).ty
              val expair = Const( "expair", as_( 1 ).ty ->: To ->: exnVs( 1 ).ty, tyParams )
              // TODO: replace the whole catch term, not just exnVs(1)
              //       or reduce catch without free variable to its argument maybe?
              Some( normalize( Substitution( exnVs( 1 ), expair( as_( 1 ), le"true" ) )( catchB ) ) )
            case term =>
              Some( term )
          }
        }
      case hd @ Const( c, _, _ ) =>
        c match {
          case "matchSum" =>
            debug( "reducing matchSum" )
          case "natRec" =>
            debug( "reducing natRec" )
          case "existsElim" =>
            debug( "reducing existsElim" )
          /*
          case "+" | "-" | "*" | "pow2" =>
            debug( s"reducing arithmetic op $c" )
          case "<" | "<=" =>
            debug( s"reducing comparison op $c" )
          */
          case _ => ()
        }
        headMap.get( c ).flatMap {
          case ( rs, whnfArgs, normalizeArgs ) =>
            val as_ = as.zipWithIndex.map {
              case ( a, i ) if whnfArgs( i ) =>
                debug( s"whnf: a: ${a}" )
                whnf( a )
              case ( a, i ) if normalizeArgs( i ) =>
                debug( s"normalize: a: ${a}" )
                normalize( a )
              case ( a, _ ) => a
            }
            rs.view.flatMap { r =>
              val substs = syntacticMatching( r.lhs, Apps( hd, as_.take( r.lhsArgsSize ) ) )
              //debug( s"substs: $substs" )
              substs.map { subst =>
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
