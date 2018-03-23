package gapt.proofs.lk

import gapt.expr._
import gapt.proofs._
import gapt.utils.NameGenerator
import dialectica.ite
import gapt.expr.fol.folSubTerms
import gapt.provers.verit.VeriT

sealed trait Tree[+T] {
  def map[S]( f: T => S ): Tree[S] =
    this match {
      case Empty        => Empty
      case Leaf( t )    => Leaf( f( t ) )
      case Node( a, b ) => Node( a.map( f ), b.map( f ) )
    }

  def zip[S]( that: Tree[S] ): Tree[( T, S )] =
    ( this, that ) match {
      case ( Empty, Empty )                   => Empty
      case ( Leaf( t1 ), Leaf( t2 ) )         => Leaf( ( t1, t2 ) )
      case ( Node( a1, b1 ), Node( a2, b2 ) ) => Node( a1 zip a2, b1 zip b2 )
      case _                                  => Empty
    }

  def ++[S >: T]( that: Tree[S] ): Tree[S] = Node( this, that )

  def elements: Vector[T] = {
    val es = Vector.newBuilder[T]
    def go( tree: Tree[T] ): Unit = tree match {
      case Empty        =>
      case Leaf( t )    => es += t
      case Node( a, b ) => go( a ); go( b )
    }
    go( this )
    es.result()
  }

  def leftGet: Tree[T] = ( this: @unchecked ) match { case Node( l, _ ) => l }
  def rightGet: Tree[T] = ( this: @unchecked ) match { case Node( _, r ) => r }
}
case object Empty extends Tree[Nothing]
case class Leaf[T]( t: T ) extends Tree[T]
case class Node[T]( a: Tree[T], b: Tree[T] ) extends Tree[T]

object Tree {
  def fromSeq[T]( l: Seq[T] ): Tree[T] =
    l.view.map( Leaf( _ ): Tree[T] ).reduceLeftOption( _ ++ _ ).getOrElse( Empty )

  implicit def substitutable[S <: Substitution, T, U]( implicit ev: Substitutable[S, T, U] ): Substitutable[S, Tree[T], Tree[U]] =
    ( sub, tree ) => tree.map( ev.applySubstitution( sub, _ ) )

  implicit class TypeOps( private val b: Tree[Ty] ) extends AnyVal {
    private def ->:( a: Seq[Ty] ): Tree[Ty] = b.map( FunctionType( _, a ) )
    def ->:( a: Tree[Ty] ): Tree[Ty] = a.elements ->: b
    def ->:( a: Ty ): Tree[Ty] = Seq( a ) ->: b
  }

  implicit class ExprOps( private val b: Tree[Expr] ) extends AnyVal {
    private def ^:( a: Seq[Var] ): Tree[Expr] = b.map( Abs( a, _ ) )
    def ^:( a: Tree[Var] ): Tree[Expr] = a.elements ^: b
    def ^:( a: Var ): Tree[Expr] = Seq( a ) ^: b

    private def apply( a: Seq[Expr] ): Tree[Expr] = b.map( _( a ) )
    def apply( a: Tree[Expr] ): Tree[Expr] = b( a.elements )
    def apply( a: Expr ): Tree[Expr] = b( Seq( a ) )
  }
}

class dialectica( nameGen: NameGenerator ) {

  def betterIte( c: Formula, a: Expr, b: Expr ): Expr =
    c match {
      case _ if a == b => a
      case Neg( c_ )   => betterIte( c_, b, a )
      case _           => ite( c, a, b )
    }

  val debugging =
    Empty
  //    Leaf( ty"p" )

  def challenge( f: Formula ): Tree[Ty] =
    f match {
      case Top() | Bottom() | Eq( _, _ ) => Empty
      case _: Atom                       => debugging // FIXME
      case Neg( f1 )                     => challenge( f1 ) ->: witness( f1 )
      case And( f1, f2 )                 => challenge( f1 ) ++ challenge( f2 )
      case Or( f1, f2 )                  => challenge( f1 ) ++ challenge( f2 )
      case Imp( f1, f2 )                 => challenge( -f1 | f2 )
      case Ex( x, f1 )                   => x.ty ->: challenge( f1 )
      case All( x, f1 )                  => Leaf( x.ty ) ++ challenge( f1 )
    }
  def witness( f: Formula ): Tree[Ty] =
    f match {
      case Top() | Bottom() | Eq( _, _ ) => Empty
      case _: Atom                       => debugging // FIXME
      case Neg( f1 )                     => challenge( f1 )
      case And( f1, f2 )                 => witness( f1 ) ++ witness( f2 )
      case Or( f1, f2 )                  => witness( f1 ) ++ witness( f2 )
      case Imp( f1, f2 )                 => witness( -f1 | f2 )
      case Ex( x, f1 )                   => Leaf( x.ty ) ++ witness( f1 )
      case All( _, f1 )                  => witness( f1 )
    }
  def matrix( f: Formula, c: Tree[Expr], w: Tree[Expr] ): Formula = {
    requireEq( c.map( _.ty ), challenge( f ) )
    requireEq( w.map( _.ty ), witness( f ) )
    ( f, c, w ) match {
      case ( Top() | Bottom() | Eq( _, _ ), Empty, Empty ) => f
      case ( _: Atom, _, _ )                               => f // FIXME
      case ( Neg( f1 ), _, _ ) =>
        -matrix( f1, w, c( w ) )
      case ( And( f1, f2 ), Node( c1, c2 ), Node( w1, w2 ) ) =>
        matrix( f1, c1, w1 ) & matrix( f2, c2, w2 )
      case ( Or( f1, f2 ), Node( c1, c2 ), Node( w1, w2 ) ) =>
        matrix( f1, c1, w1 ) | matrix( f2, c2, w2 )
      case ( Imp( f1, f2 ), Node( c1, c2 ), Node( w1, w2 ) ) =>
        matrix( f1, w1, c1( w1 ) ) --> matrix( f2, c2, w2 )
      case ( Ex( x, f1 ), _, Node( Leaf( t ), w1 ) ) =>
        matrix( Substitution( x -> t )( f1 ), c( t ), w1 )
      case ( All( x, f1 ), Node( Leaf( t ), c1 ), _ ) =>
        matrix( Substitution( x -> t )( f1 ), c1, w )
    }
  }
  def matrix( f: Formula, c: Tree[Expr], w: Tree[Expr], p: Polarity ): Formula =
    matrix( if ( p.inSuc ) f else -f, c, w )
  def matrix( s: HOLSequent, c: Sequent[Tree[Expr]], w: Sequent[Tree[Expr]] ): Formula =
    Or( s.zipWithIndex.zip( c.zip( w ) ).map {
      case ( ( f, i ), ( ci, wi ) ) => matrix( f, ci, wi, i.polarity )
    }.elements )

  def witness( s: HOLSequent ): Sequent[Tree[Ty]] =
    for ( ( f, i ) <- s.zipWithIndex ) yield witness( if ( i.isAnt ) -f else f )
  def challenge( s: HOLSequent ): Sequent[Tree[Ty]] =
    for ( ( f, i ) <- s.zipWithIndex ) yield challenge( if ( i.isAnt ) -f else f )

  def dummy( t: Ty ): Expr =
    t match {
      case TArr( a, b ) => Abs( Var( "x", a ), dummy( b ) )
      case _            => Const( "arbitrary", t, List( t ) )
    }
  def dummy( t: Tree[Ty] ): Tree[Expr] = t.map( dummy )

  private def requireEq[T]( a: T, b: T ): Unit =
    require( a == b, s"$a ==\n$b" )

  def newVar( ty: Ty ): Var =
    Var( nameGen.freshWithIndex( "x" ), ty )
  def newVar( ty: Seq[Ty] ): Seq[Var] =
    ty.map( newVar )
  def newVar( ty: Tree[Ty] ): Tree[Var] =
    ty.map( newVar )

  def childrenCombined[T](
    c1: SequentConnector, s1: Sequent[T],
    c2: SequentConnector, s2: Sequent[T],
    default: => T = ??? ): Sequent[T] =
    c1.children( s1 ).zip( c2.children( s2 ) ).map {
      case ( Seq( t1 ), Seq() ) => t1
      case ( Seq(), Seq( t2 ) ) => t2
      case _                    => default
    }

  def apply( p: LKProof, c: Sequent[Tree[Var]] ): Sequent[Tree[Expr]] = {
    requireEq( c.map( _.map( _.ty ) ), challenge( p.endSequent ) )

    def binary( p: BinaryLKProof ): Sequent[Tree[Expr]] = {
      val Seq( p1, p2 ) = p.immediateSubProofs
      val Seq( Seq( a1 ), Seq( a2 ) ) = p.auxIndices
      val Node( x1, x2 ) = c( p.mainIndices.head )
      val r1 = apply( p1, p.getLeftSequentConnector.parent( c ).updated( a1, x1 ) )
      val r2 = apply( p2, p.getRightSequentConnector.parent( c ).updated( a2, x2 ) )
      childrenCombined(
        p.getLeftSequentConnector, r1,
        p.getRightSequentConnector, r2,
        r1( a1 ) ++ r2( a2 ) )
    }
    def unary( p: UnaryLKProof ): Sequent[Tree[Expr]] = {
      val Seq( p1 ) = p.immediateSubProofs
      val Seq( Seq( a1, a2 ) ) = p.auxIndices
      val Node( x1, x2 ) = c( p.mainIndices.head )
      val r1 = apply( p1, p.getSequentConnector.parent( c ).updated( a1, x1 ).updated( a2, x2 ) )
      p.getSequentConnector.child( r1, r1( a1 ) ++ r1( a2 ) )
    }

    val res: Sequent[Tree[Expr]] = p match {
      case LogicalAxiom( _ ) =>
        val Sequent( Seq( c1 ), Seq( c2 ) ) = c
        c2 +: Sequent() :+ c1( c2 )
      case ReflexivityAxiom( _ ) | TopAxiom =>
        Sequent() :+ Empty
      case BottomAxiom =>
        Empty +: Sequent()
      case ProofLink( _, _ ) =>
        require( c.forall( _ == Empty ) )
        p.endSequent.map( _ => Empty )

      case p @ CutRule( p1, a1, p2, a2 ) =>
        val c1 = newVar( challenge( p.cutFormula ) )
        val c2 = newVar( challenge( -p.cutFormula ) )
        val r1 = apply( p1, p.getLeftSequentConnector.parent( c, c1 ) )
        val r2 = apply( p2, p.getRightSequentConnector.parent( c, c2 ) )
        val r2_ = Substitution( c2.zip( c1 ^: r1( a1 ) ).elements )( r2 )
        val r1_ = Substitution( c1.zip( r2_( a2 ) ).elements )( r1 )
        r1_.delete( a1 ) ++ r2_.delete( a2 )

      case p @ NegLeftRule( p1, a1 ) =>
        val x1 = newVar( challenge( p1.endSequent( a1 ) ) )
        val r1 = apply( p1, p.getSequentConnector.parent( c ).updated( a1, x1 ) )
        p.getSequentConnector.child(
          Substitution( x1.zip( c( p.mainIndices.head )( x1 ^: r1( a1 ) ) ).elements )( r1 ).
            updated( a1, x1 ^: r1( a1 ) ) )
      case p @ NegRightRule( p1, _ ) =>
        p.getSequentConnector.child( apply( p1, p.getSequentConnector.parent( c ) ) )

      case p: AndRightRule => binary( p )
      case p: ImpRightRule => unary( p )
      case p: OrRightRule  => unary( p )

      case p @ OrLeftRule( p1, a1, p2, a2 ) =>
        val c1 = newVar( challenge( -p.leftDisjunct ) )
        val c2 = newVar( challenge( -p.rightDisjunct ) )
        val r1 = apply( p1, p.getLeftSequentConnector.parent( c ).updated( a1, c1 ) )
        val r2 = apply( p2, p.getRightSequentConnector.parent( c ).updated( a2, c2 ) )
        // C(~(f1 | f2)) = C(f1)*C(f2) -> W(f1)*W(f2)
        // W(~(f1 | f2)) = C(f1)*C(f2)
        // M(~f1, c1, r1(a1)) = ~M(f1, r1(a1), c1(r1(a1)))
        //                  |-> ~M(f1, r1(a1), c(r1(a1), r2(a2))._1)
        // M(~(f1|f2), c, (r1(a1), r2(a2))) = ~M(f1|f2, (r1(a1), r2(a2)), c(r1(a1), r2(a2)))
        val y1 = newVar( challenge( p.leftDisjunct ) )
        val Node( z1, z2 ) = c( p.mainIndices.head )
        val r1_ = Substitution( c1.zip( y1 ^: z1( y1 ++ r2( a2 ) ) ).elements )( r1 )
        val r2_ = Substitution( c2.zip( z2( r1_( a1 ) ) ).elements )( r2 )
        childrenCombined( p.getLeftSequentConnector, r1_, p.getRightSequentConnector, r2_,
          r1_( a1 ) ++ r2_( a2 ) )
      case p @ ImpLeftRule( p1, a1, p2, a2 ) =>
        apply( OrLeftRule( NegLeftRule( p1, a1 ), Ant( 0 ), p2, a2 ), c )
      case p @ AndLeftRule( p1, a1, a2 ) =>
        val c1 = newVar( challenge( -p.leftConjunct ) )
        val c2 = newVar( challenge( -p.rightConjunct ) )
        val r1 = apply( p1, p.getSequentConnector.parent( c, null ).updated( a1, c1 ).updated( a2, c2 ) )
        // C(~(f1 & f2)) = C(f1)*C(f2) -> W(f1)*W(f2)
        // W(~f1) = C(f1)
        // C(~f1) = C(f1) -> W(f1)
        // W(~(f1 & f2)) = C(f1)*C(f2)
        // M(~f1, c1, r1) = ~M(f1, r1, c1(r1))
        // M(~(f1&f2), (z1,z2), (r1,r2)) = ~M(f1&f2, (r1,r2), (z1,z2)(r1,r2))
        //     = ~(M(f1, r1, z1(r1,r2)) & M(f2, r2, z2(r1,r2)))
        val Node( z1, z2 ) = c( p.mainIndices.head )
        val r1_ = Substitution( c2.zip( z2( r1( a1 ) ) ).elements )( r1 )
        val y1 = newVar( challenge( p.leftConjunct ) )
        val r1__ = Substitution( c1.zip( y1 ^: z1( y1 )( r1_( a2 ) ) ).elements )( r1_ )
        p.getSequentConnector.child( r1__, r1__( a1 ) ++ r1__( a2 ) )

      case p @ WeakeningLeftRule( p1, f ) =>
        dummy( witness( -f ) ) +: apply( p1, p.getSequentConnector.parent( c ) )
      case p @ WeakeningRightRule( p1, f ) =>
        apply( p1, p.getSequentConnector.parent( c ) ) :+ dummy( witness( f ) )

      case p: ContractionRule =>
        val r1 = apply( p.subProof, p.getSequentConnector.parent( c ) )
        val c0 = c( p.mainIndices.head )
        p.getSequentConnector.child(
          r1,
          r1( p.aux1 ).zip( r1( p.aux2 ) ).map {
            case ( w1, w2 ) =>
              betterIte( matrix( p.mainFormula, c0, r1( p.aux1 ), p.aux1.polarity ), w1, w2 )
          } )

      case p @ ForallLeftRule( p1, a1, _, t1, _ ) =>
        val c1 = newVar( challenge( -p1.endSequent( a1 ) ) )
        val r1 = apply( p1, p.getSequentConnector.parent( c ).updated( a1, c1 ) )
        // C(~ !x f1) =  C(!x f1) -> W(!x f1) = a*C(f1) -> W(f1)
        // C(~ f1) = C(f1) -> W(f1)
        // W(~ !x f1) = C(!x f1) = a*C(f1)
        // W(~ f1) = C(f1)
        val r1_ = Substitution( c1.zip( c( p.mainIndices.head )( t1 ) ).elements )( r1 )
        p.getSequentConnector.child(
          r1_.updated( a1, Leaf( t1 ) ++ r1_( a1 ) ) )

      case p @ ForallRightRule( p1, a1, e1, _ ) =>
        val Node( Leaf( ce1 ), x1 ) = c( p.mainIndices.head )
        val r1 = apply(
          Substitution( e1 -> ce1 )( p1 ),
          p.getSequentConnector.parent( c ).updated( a1, x1 ) )
        p.getSequentConnector.child( r1 )

      case p @ ExistsLeftRule( p1, a1, e1, _ ) =>
        // C(~ ?x f1) = C(?x f1) -> W(?x f1) = (a -> C(f1)) -> a * W(f1)
        // W(~ f1) = C(f1)
        // C(~ f1) = C(f1) -> W(f1)
        // W(~ ?x f1) = C(?x f1) = a -> C(f1)
        // M(~f1, x1, r1) = ~M(f1, r1, c1(r1))
        // M(~?x f1, (t,c), r) = ~M(?x f1, r, (t(r), c0(r)))
        //                    = ~M(f1[x\t(r)], r(t(r)), c0(r))
        val c1 = newVar( challenge( -p1.endSequent( a1 ) ) )
        val r1 = apply( p1, p.getSequentConnector.parent( c ).updated( a1, c1 ) )
        val Node( Leaf( t ), c0 ) = c( p.mainIndices.head )
        val r1_ = Substitution( e1 -> t( ( e1 ^: r1( a1 ) ).elements ) )( r1 )
        val r1__ = r1_.updated( a1, e1 ^: r1( a1 ) )
        val y1 = newVar( challenge( p1.endSequent( a1 ) ) )
        val r1___ = Substitution( c1.zip( y1 ^: c0( e1 ^: y1 ) ).elements )( r1__ )
        p.getSequentConnector.child( r1___ )

      case p @ ExistsRightRule( p1, a1, _, t1, _ ) =>
        val c1 = newVar( challenge( p1.endSequent( a1 ) ) )
        val r1 = apply( p1, p.getSequentConnector.parent( c ).updated( a1, c1 ) )
        val r2 = Substitution( c1 zip c( p.mainIndices.head ).map( _( t1 ) ) elements )( r1 )
        p.getSequentConnector.child( r2.updated( a1, Leaf( t1 ) ++ r2( a1 ) ) )

      case p: EqualityRule =>
        val conn = p.correctSequentConnector
        conn.child( apply( p.subProof, conn.parent( c ) ) )

      case InductionRule( cs1, f1, t1 ) =>
        // TODO: requires mutual recursion
        ???
    }
    requireEq( res.map( _.map( _.ty ) ), witness( p.endSequent ) )
    //    val m = dialectica liftIte matrix( p.endSequent, c, res )
    //    println( m.toUntypedString )
    //    require( VeriT.isValid( BetaReduction betaNormalize m ) )
    res
  }

}

object dialectica {
  def ite( c: Expr, a: Expr, b: Expr ): Expr =
    Const( "ite", To ->: a.ty ->: a.ty ->: a.ty, List( a.ty ) )( c, a, b )

  def liftIte( f: Formula ): Formula = {
    val nameGen = rename.awayFrom( containedNames( f ) )
    val iteSubterms = subTerms( f ).collect {
      case t @ Apps( Const( "ite", _, _ ), cond +: a +: b +: _ ) =>
        ( t, Var( nameGen.fresh( "v" ), t.ty ), cond, a, b )
    }
    val repl = Map() ++ iteSubterms.map { case ( t, v, _, _, _ ) => t -> v }
    And( iteSubterms.map {
      case ( _, v, c0, a0, b0 ) =>
        val ( c, ( a, b ) ) = TermReplacement( ( c0, ( a0, b0 ) ), repl )
        ( c --> ( v === a ) ) & ( -c --> ( v === b ) )
    } ) --> TermReplacement( f, repl )
  }

  def apply( p: LKProof ): ( Sequent[Tree[Var]], Sequent[Tree[Expr]] ) = {
    val nameGen = rename.awayFrom( containedNames( p ) )
    val d = new dialectica( nameGen )
    val x = for ( ( f, i ) <- p.endSequent.zipWithIndex )
      yield d.newVar( d.challenge( if ( i.isSuc ) f else -f ) )
    val res = x -> d.apply( p, x )
    //    println( d.matrix( p.endSequent, res._1, res._2 ) )
    res
  }
}
