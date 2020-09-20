package gapt.examples

import ammonite.ops._
import gapt.examples.Ty.{ DClause, DClauseSet }
import gapt.expr._
import gapt.expr.arithmetic.int._
import gapt.formats.llk.toLLKString
import gapt.formats.tptp._
import gapt.proofs._
import gapt.utils.NameGenerator

import scala.collection.{ GenTraversable, mutable }
import scala.collection.parallel.ParSeq
import scala.io.Codec

object ReadFilenames {
  def apply( fp: Path ) = {
    read.lines( fp, Codec.UTF8 )
  }
  val my_path = "/opt/smtlib/Main Track no BV or QF/dump/stripped/UFLIA/"
  //val my_path = "/home/marty/manchester/experiments/instance_overview_2018/more_terms/stripped/"
  val my_list = "list.txt"
}

object Ty {
  type DClause = Set[Expr]
  type DClauseSet = Set[DClause]
}

//create local memoization instance
object Memo extends ExpressionMemoization

case class DumpData[T]( path: String, file_list: String, simplifier: Simplifier[T] ) {
  import Ty.DClause

  val files = ReadFilenames( Path( path + file_list ) )

  def parse[R]( fun: FilePath => GenTraversable[R] ): ParSeq[R] =
    files.map( x => FilePath( path + x ) ).par.flatMap( ( x: FilePath ) => fun( x ) )

  def computeFormulaAndNF( f: Formula, cache: T ) = {
    val cl = toCSet( f ).map( Memo.Expr( _ ) )
    val simple = simplifier.simplifyC( cl, cache )
    ( cl, simple )
  }

  def onlyCountNF( m: mutable.Map[DClause, Int] )( f: Formula, cache: T ) = {
    val cl = toCSet( f ) //don't memoize cl itself //.map( Memo.Expr( _ ) )
    val simple = simplifier.simplifyC( cl, cache )
    inc( simple, m )
    ()
  }

  def getClauses[R]( compute: ( Formula, T ) => R )( x: FilePath ) =
    try {
      val cache = simplifier.defaultCache()
      val cl_pairs =
        TptpInferTypes( TptpImporter.loadWithIncludes( x ) ).inputs.collect {
          case a @ AnnotatedFormula( _, _, _, f, _ ) =>
            compute( f, cache )
        }
      val r = ( x, cl_pairs.toSet )
      print( "." )
      Some( r )
    } catch {
      case e: Exception =>
        //println( s"x $x : ${e.getMessage}" )
        print( "x " )
        None
    }

  def normalize( f: Formula ) = {
    val fv = freeVariables( f )
    val mapping = fv.zip( Range( 1, fv.size ) ).map { case ( v, i ) => ( v, Var( "X" + i, v.ty ) ) }
    Substitution( mapping )( f )
  }

  def toCSet( formula: Formula ): DClause = {
    ( formula match {
      case All.Block( _, ors ) =>
        normalize( ors ) match {
          case Or.nAry( ls ) => ls
        }
    } ).toSet
  }

  def csetToSequent( cl: DClause ) = {
    val ( neg, pos ) = cl.partition { case Neg( f ) => true; case _ => false }
    val ant = neg map { case Neg( f ) => f }
    val succ = pos map { case f: Formula => f }
    Sequent( ant, succ )
  }

  def toSequent( formula: Formula ) = {
    val ( neg, pos ) = ( formula match {
      case All.Block( _, Or.nAry( ls ) ) => ls
    } ).partition( { case Neg( _ ) => true; case _ => false } )
    Sequent( neg.map( { case Neg( x ) => x } ), pos )
  }

  lazy val seqs = parse( getClauses( computeFormulaAndNF ) ).toSet.par.flatMap( ( x: ( FilePath, Set[( DClause, DClause )] ) ) => x._2 ).seq

  lazy val nfs = {
    val map = mutable.Map[DClause, Int]()
    parse( getClauses( onlyCountNF( map ) ) )
    map.seq
  }

  //
  //case class Dump[T]( data: DumpData[T] ) {
  //general stuff
  def fmt( cl: Set[Expr] ) = cl.map( toLLKString( _ ) ).mkString( " ; " )

  lazy val pairmap = {
    val map = mutable.Map[Set[Expr], mutable.Set[Set[Expr]]]()
    for ( ( cl, nf ) <- seqs ) {
      add( nf, cl, map )
    }
    map
  }

  def inc[T]( v: T, m: mutable.Map[T, Int] ): Unit = {
    m.synchronized {
      val count = m.getOrElse( v, 0 ) + 1
      m( v ) = count
      ()
    }
  }

  def add[T, U]( k: T, v: U, m: mutable.Map[T, mutable.Set[U]] ): Unit = {
    m.synchronized {
      if ( m contains k ) {
        m( k ) += v
      } else {
        m( k ) = mutable.Set( v )
      }
    }
    ()
  }

  //lazy val nfs = seqs.map( _._2 )

  lazy val countermap = {
    val map = mutable.Map[Set[Expr], Int]()
    for ( ( _, nf ) <- seqs ) {
      inc( nf, map )
    }
    map
  }

  def find( values: Set[Set[Expr]] ) = {
    val map = mutable.Map[DClause, mutable.Set[DClause]]()
    for ( ( cl, nf ) <- seqs ) {
      if ( values contains nf )
        add( nf, cl, map )
    }
    map
  }

  def printNFs() = {
    for ( ( cl, nf ) <- seqs ) {
      print( nf.mkString( " ∨ " ) )
    }
  }

  lazy val top30 = pairmap.filter( _._2.size > 100 ).toList.sortBy( _._2.size ).reverse.take( 30 )
  def printTop30() = top30.map( x => println( s"* (${x._2.size}) ${x._1.mkString( " ; " )}" ) )
}

trait Simplifier[T] {
  import Ty.DClause
  def defaultCache(): T

  def simplify( e: Expr, cache: T ): Expr

  def isInterpreted( s: String ) = TptpInferTypes.isNumeral( s ) || ( Set( "$sum", "$product", "$uminus", "$difference",
    "$less", "$lesseq", "$greater", "$greatereq" ) contains s )

  def simplifyT( ty: Ty ): Ty = ty match {
    case Ti        => Ti
    case To        => To
    case TInt      => TInt
    case t1 ->: t2 => simplifyT( t1 ) ->: simplifyT( t2 )
    case _         => Ti
  }
  def simplifyC( inset: Set[Expr], cache: T ): DClause = {
    val set = mutable.Set[Expr]()
    for ( exp <- inset ) {
      val simple = simplify( exp, cache )
      set += simple
    }
    set.toSet
  }

  def stringOfCache( c: T ): String;

}

object Caches {
  type C1 = ( mutable.Map[Ty, Const], mutable.Map[Ty, Var], NameGenerator )
  type C2 = ( mutable.Map[Ty, Const], mutable.Map[Ty, Var], mutable.Map[Const, Const], NameGenerator )
}

object AggressiveSimplifier extends Simplifier[Caches.C1] {
  def defaultCache(): Caches.C1 =
    ( mutable.Map[Ty, Const](), mutable.Map[Ty, Var](), new NameGenerator( Nil ) )

  def stringOfCache( c: Caches.C1 ) = s"${c._1.size}-${c._2.size}"

  def simplify( e: Expr, cache: Caches.C1 ): Expr = {
    val ( cmap, vmap, ng ) = cache
    e match {
      case NonLogicalConstant( _, ty, _ ) if cmap.contains( ty ) =>
        cmap( ty )
      case NonLogicalConstant( name, ty, _ ) =>
        val base = ( isInterpreted( name ), arity( ty ) ) match {
          case ( true, 0 )  => "cint"
          case ( true, _ )  => "fint"
          case ( false, 0 ) => "c"
          case ( false, _ ) => "f"
        }
        val nc = Memo.Const( ng.fresh( base ), simplifyT( ty ) )
        cmap += ( ( ty, nc ) )
        nc
      case c @ Const( _, _, _ ) => //logical constants
        c

      case Var( _, ty ) if vmap.contains( ty ) =>
        vmap( ty )
      case v @ Var( name, ty ) =>
        /*
        val base = ( isInterpreted( name ), arity( ty ) ) match {
          case ( _, 0 ) => "X"
          case ( _, _ ) => "Fun"
        } */
        val nv = Memo.Var( name, simplifyT( ty ) )
        vmap += ( ( ty, nv ) )
        nv
      case Eq( s, t ) => //equality might have changed type
        val s0 = simplify( s, cache )
        val t0 = simplify( t, cache )
        Memo.Eq( s0, t0 )
      case App( s, t ) =>
        val s0 = simplify( s, cache )
        val t0 = simplify( t, cache )
        Memo.App( s0, t0 )
      case Abs( s, t ) =>
        val s0 @ Var( _, _ ) = simplify( s, cache )
        val t0 = simplify( t, cache )
        Memo.Abs( s0, t0 )
    }
  }

}

object UninterpretedSimplifier extends Simplifier[Caches.C2] {
  def defaultCache() =
    ( mutable.Map[Ty, Const](), mutable.Map[Ty, Var](), mutable.Map[Const, Const](), new NameGenerator( Nil ) )

  def stringOfCache( c: Caches.C2 ) = s"${c._1.size}-${c._2.size}-${c._3.size}"

  val posnum = Memo.Const( "posN", TInt )
  val negnum = Memo.Const( "negN", TInt )
  val num = Memo.Const( "num", TInt )

  def simplify( e: Expr, cache: Caches.C2 ): Expr = {
    val ( cmap, vmap, iconsts, ng ) = cache

    e match {
      case c @ NonLogicalConstant( name, ty, _ ) if iconsts.contains( c ) =>
        iconsts( c )
      case NonLogicalConstant( name, ty, _ ) if cmap.contains( ty ) && !isInterpreted( name ) =>
        cmap( ty )
      case NonLogicalConstant( name, TInt, _ ) if TptpInferTypes.isNumeral( name ) =>
        num
      case NonLogicalConstant( name, ty, _ ) if isInterpreted( name ) =>
        val nc = Const( name, simplifyT( ty ) )
        cmap += ( ( ty, nc ) )
        nc
      case c @ NonLogicalConstant( name, ty, _ ) =>
        val base = arity( ty ) match {
          case 0 => "c"
          case _ => "f"
        }
        val nc = Memo.Const( ng.fresh( base ), simplifyT( ty ) )
        iconsts += ( ( c, nc ) )
        nc
      case c @ Const( _, _, _ ) => //logical constants
        c
      case Var( _, ty ) if vmap.contains( ty ) =>
        vmap( ty )
      case v @ Var( name, ty ) =>
        val nv = Memo.Var( name, simplifyT( ty ) )
        vmap += ( ( ty, nv ) )
        nv
      case Eq( s, t ) => //equality might have changed type
        val s0 = simplify( s, cache )
        val t0 = simplify( t, cache )
        Memo.Eq( s0, t0 )
      case App( s, t ) =>
        val s0 = simplify( s, cache )
        val t0 = simplify( t, cache )
        Memo.App( s0, t0 )
      case Abs( s, t ) =>
        val s0 @ Var( _, _ ) = simplify( s, cache )
        val t0 = simplify( t, cache )
        Memo.Abs( s0, t0 )
    }
  }

}

