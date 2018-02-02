package at.logic.gapt.examples.theories

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ instantiate, simplify, universalClosure }
import at.logic.gapt.formats.babel.Notation
import at.logic.gapt.proofs.Context.{ InductiveType, PrimRecFun, ProofNames, SkolemFun }
import at.logic.gapt.proofs.epsilon.EpsilonC
import at.logic.gapt.proofs.{ Context, HOLSequent, ImmutableContext, Sequent, SequentConnector, Suc }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.utils.LogHandler
import cats.{ Eval, Later }

import scala.collection.mutable
import scala.util.DynamicVariable

object Theory {
  def combineContexts( ctx: Iterable[Context] ): ImmutableContext =
    Context.empty ++ ctx.toVector.flatMap( _.updates.reverse ).distinct

  case class DelayedProofResult( proofName: Expr, usedLemmas: Seq[( Expr, Formula )], proof: LKProof ) {
    val Apps( Const( name, _, _ ), _ ) = proofName

    def inst( proofNameInst: Expr ): DelayedProofResult = {
      val subst = syntacticMatching( proofName, proofNameInst ).get
      DelayedProofResult( proofNameInst, subst( usedLemmas ), subst( proof ) )
    }

    def usedLemmaNames = usedLemmas.map { case ( Apps( Const( n, _, _ ), _ ), _ ) => n }

    def proofWithLinks: LKProof = {
      var p = proof
      for ( ( n, f ) <- usedLemmas )
        p = CutRule( ProofLink( n, Sequent() :+ f ), p, f )
      p
    }

    def updates = Seq( Context.ProofDefinitionDeclaration( proofName, proofWithLinks ) )
  }
  object DelayedProofResult {
    def apply( proofName: Expr, proofWithLinks: LKProof ): DelayedProofResult = {
      val usedLemmas = mutable.Map[Formula, Expr]()
      val proofWithoutLinks0 = new LKVisitor[Unit] {
        override def visitProofLink( proof: ProofLink, otherArg: Unit ): ( LKProof, SequentConnector ) =
          if ( proof.conclusion.sizes != ( 0, 1 ) ) super.visitProofLink( proof, otherArg ) else {
            val formula = proof.conclusion.succedent.head
            usedLemmas( formula ) = proof.referencedProof
            val newProof = LogicalAxiom( formula )
            newProof -> SequentConnector(
              lowerSequent = newProof.conclusion, upperSequent = proof.conclusion,
              parentsSequent = Seq() +: Sequent() :+ Seq( Suc( 0 ) ) )
          }
      }.apply( proofWithLinks, () )
      val proofWithoutLinks = ContractionMacroRule( cleanCuts( cleanStructuralRules( proofWithoutLinks0 ) ) )
      DelayedProofResult(
        proofName,
        for ( ( f, n ) <- usedLemmas.toSeq if proofWithoutLinks.endSequent.antecedent.contains( f ) )
          yield n -> f,
        proofWithoutLinks )
    }
  }
}

class Theory0( val imports: List[Theory] ) {
  private var ifaceCtx: ImmutableContext = Theory.combineContexts( Context.default +: imports.map( _.ctx ) )
  private val proofsBuf: mutable.Buffer[( String, Eval[Theory.DelayedProofResult] )] = mutable.Buffer()

  implicit def ctx: Context = ifaceCtx
  def proofsHere: Vector[( String, Eval[Theory.DelayedProofResult] )] = proofsBuf.toVector

  protected def addNow( update: Context.Update ): Unit = ifaceCtx += update
  protected def addProof( name: Expr, proof: => LKProof ): Unit = {
    val Apps( Const( n, _, _ ), _ ) = name
    val declCtx = ctx
    proofsBuf += ( n -> Later {
      val p = proof
      declCtx.check( p )
      Theory.DelayedProofResult( name, p )
    } )
  }
}

class Theory( imports: Theory* ) extends Theory0( imports.toList ) {
  val transitiveImports: Vector[Theory] =
    ( imports.view.flatMap( _.transitiveImports ) ++ imports ).distinct.toVector
  def allProofs: Vector[( String, Eval[Theory.DelayedProofResult] )] =
    ( transitiveImports :+ this ).flatMap( _.proofsHere ).distinct
  def ctxWithProofDefinitions(): ImmutableContext =
    ctx ++ allProofs.flatMap( _._2.value.updates )

  def proof( name: String ): LKProof = allProofs.toMap.apply( name ).value.proof

  private val curCtxVar = new DynamicVariable[Context]( null )
  protected implicit def curCtx: Context =
    curCtxVar.value match { case null => ctx case c => c }

  def main( args: Array[String] ): Unit = {
    var failed = false
    for ( ( n, u ) <- proofsHere.reverseIterator ) {
      import scala.concurrent.duration._
      print( n + " " )
      val start = System.nanoTime()
      try u.value catch {
        case t: Throwable =>
          failed = true
          println( "=" * ( 71 - n.length - 1 ) + "\\\n" )
          t match {
            case t: QedFailureException =>
              println( t.getMessage )
            case _ => t.printStackTrace( Console.out )
          }
          print( "\\" + "=" * ( 71 - 7 ) )
      }
      val end = System.nanoTime()
      println( " " + LogHandler.formatTime( ( end - start ).nanos ) )
    }
    if ( failed ) sys.exit( 1 )
  }

  private def addProofNameDecl( lemmaName: String, endSequent: HOLSequent ): Expr = {
    val fvs = freeVariables( endSequent ).toSeq.sortBy( _.name )
    val ftvs = typeVariables( endSequent.toImplication ).toList.sortBy( _.name )
    val proofName = Const( lemmaName, FunctionType( Ti, fvs.map( _.ty ) ), ftvs )( fvs )
    addNow( Context.ProofNameDeclaration( proofName, endSequent ) )
    proofName
  }
  private def addLemma( lemmaName: String, endSequent: HOLSequent, proof: => LKProof ): Expr = {
    val proofName = addProofNameDecl( lemmaName, endSequent )
    val ctxNow = ctx
    addProof( proofName, curCtxVar.withValue( ctxNow )( proof ) )
    proofName
  }
  private def addLemma( name: String, formula: Formula, p: => LKProof ): Expr =
    addLemma( name, Sequent() :+ formula, p )

  private def auxLemma( name: String, formula: Formula, p: => LKProof ): Expr =
    addLemma( name, formula, p )

  private case class auxLemma( name: String, formula: Formula ) extends LemmaHelper[Expr] {
    def handleTacticBlock( block: ProofState => ProofState ): Expr =
      auxLemma( name, formula, Lemma.finish( block( ProofState( formula ) ), incompleteOk = false ) )
  }

  private def asciify( name: String ) =
    name
      .replace( "*", "mul" )
      .replace( "+", "add" )
      .replace( "-", "sub" )
      .replace( "<=", "le" )
      .replace( "<", "lt" )
      .replace( "/", "div" )

  protected def indTy( ty0: Ty, ctrs: Const* ): Unit = {
    val ty = ty0.asInstanceOf[TBase]
    addNow( InductiveType( ty, ctrs: _* ) )

    // c_1(x_1, ..., x_n), ...
    val freeTerms = Map() ++ ctrs.map {
      case ctr @ Const( _, FunctionType( _, argTys ), _ ) => ctr ->
        ctr( for ( ( t, i ) <- argTys.zipWithIndex ) yield Var( s"x$i", t ) )
    }
    for ( ctr <- ctrs ) {
      val discr = Const( s"is_${ctr.name}", ty ->: To, ty.params )
      val eqns = ctrs.map( ctr2 => discr( freeTerms( ctr2 ) ) -> ( if ( ctr == ctr2 ) Top() else Bottom() ) )
      addNow( Context.PrimRecFun( Seq( discr -> eqns ) ) )
      val discrLemName = asciify( discr.name )
      auxLemma( discrLemName, universalClosure( simplify(
        And( eqns.map { case ( lhs, rhs ) => lhs <-> rhs } ) ) ) ) {
        unfold( discr.name ).in( "g" )
        decompose
        prop
      }
      attr( "nocombine" )( discrLemName )
    }
  }

  private def auxEqnLemma( name: String, constName: String, lhs: Expr, rhs: Expr ): Expr = {
    val proofName = auxLemma( name, universalClosure(
      if ( lhs.ty == To ) simplify( lhs <-> rhs ) else lhs === rhs ) ) {
      decompose
      unfold( constName ).in( "g" )
      if ( lhs.ty == To ) prop else refl
    }
    attr( "nocombine" )( name )
    proofName
  }

  protected def dfn( eqn: Formula ): Unit = {
    val defnUpd = Context.Update.fromDefnEq( eqn ).asInstanceOf[Definition]
    addNow( defnUpd )
    val Abs.Block( vs, rhs ) = defnUpd.by
    val lhs = defnUpd.what( vs )
    auxEqnLemma( asciify( defnUpd.name ), defnUpd.name, lhs, rhs )
  }

  protected def fun( c: Const, equations: String* ): Unit = {
    val prf = PrimRecFun( c, equations: _* )
    addNow( prf )
    val ( _, _, _, eqns ) = prf.prfDefinitions.head
    val Some( ctrs ) = ctx.getConstructors( prf.recTypes( c ) )
    val lems = for ( ( ctr, ( lhs, rhs ) ) <- ctrs zip eqns )
      yield auxEqnLemma( s"${asciify( c.name )}${ctr.name}", c.name, lhs, rhs )
    val auxP = lems.map( ProofLink( _ ) ).
      reduce[LKProof]( AndRightRule( _, Suc( 0 ), _, Suc( 0 ) ) )
    auxLemma( asciify( c.name ), auxP.endSequent.succedent.head, auxP )
  }

  protected case class indfn( constName: String, desc: Formula ) extends LemmaHelper[Unit] {
    def handleTacticBlock( block: ProofState => ProofState ): Unit = {
      val All.Block( xs, Ex( y, f ) ) = desc
      val skC = Const( constName, FunctionType( y.ty, xs.map( _.ty ) ) )
      val skDef = Abs.Block( xs, Ex( y, f ) )
      addNow( SkolemFun( skC, skDef ) )
      val spec = All.Block( xs, Substitution( y -> skC( xs ) )( f ) )
      auxLemma( asciify( constName ), spec ) {
        insert {
          val exProof = Lemma.finish( block( ProofState( desc ) ), incompleteOk = false )
          ProofBuilder.
            c( LogicalAxiom( instantiate( spec, xs ) ) ).
            u( ExistsSkLeftRule( _, skC( xs ), skDef ) ).
            u( ForallLeftBlock( _, desc, xs ) ).
            u( ForallRightBlock( _, spec, xs ) ).
            u( CutRule( exProof, _, desc ) ).
            qed
        }
      }
    }
  }

  case class LemmaHandle( proofName: Expr ) {
    val Apps( Const( name, _, _ ), _ ) = proofName

    def proof: LKProof = combined( excluded = _ => true )
    def formula: Formula = ctx.get[ProofNames].lookup( proofName ).get.succedent.head

    def usedLemmas: Seq[LemmaHandle] =
      allProofs.toMap.apply( name ).value.inst( proofName ).usedLemmas.map( l => LemmaHandle( l._1 ) )
    def transitivelyUsedLemmas: Set[LemmaHandle] = {
      val used = mutable.Set[LemmaHandle]()
      def go( h: LemmaHandle ): Unit =
        if ( !used( h ) ) { used += h; h.usedLemmas.foreach( go ) }
      go( this )
      used.toSet
    }

    def graphviz: String = {
      val res = new mutable.StringBuilder
      res ++= "digraph {\n"
      val edges = for {
        h <- transitivelyUsedLemmas + this
        d <- h.usedLemmas
      } yield h.name -> d.name
      for ( ( a, b ) <- edges ) res ++=
        s"""  "$a" -> "$b";
"""
      res ++= "}\n"
      res.result()
    }

    def combined( excluded: ( String => Boolean ) = Set(), included: ( String => Boolean ) = Set() ): LKProof = {
      val nocombine = ctx.get[Attributes].lemmasWith( "nocombine" )
      val Theory.DelayedProofResult( _, used0, p0 ) = allProofs.toMap.apply( name ).value.inst( proofName )
      val used: mutable.Map[String, Set[Expr]] = mutable.Map().withDefaultValue( Set() )
      for ( ( pn @ Apps( Const( n, _, _ ), _ ), _ ) <- used0.toSet ) yield used( n ) += pn
      var p = p0
      for {
        ( n, dpr ) <- allProofs.reverseIterator
        if used( n ).nonEmpty
        if !excluded( n )
        if included( n ) || !nocombine( n )
      } {
        for ( pn <- used( n ) ) {
          val Theory.DelayedProofResult( _, usedN, pN ) = dpr.value.inst( pn )
          for ( ( pn @ Apps( Const( n, _, _ ), _ ), _ ) <- usedN.toSet ) yield used( n ) += pn
          p = ContractionMacroRule( CutRule( pN, p, pN.conclusion.succedent.head ) )
        }
        used( n ) = Set()
      }
      p
    }
  }

  protected case class lemma( openFormula: Formula, attributes: String* ) extends LemmaHelper[LemmaHandle] {
    val fvs = freeVariables( openFormula ).toSeq.sortBy( _.name )
    val formula = All.Block( fvs, openFormula )
    def handleTacticBlock( block: ProofState => ProofState )( implicit name: sourcecode.Name ): LemmaHandle = {
      val proofName = addLemma( name.value, formula,
        ForallRightBlock( Lemma.finish( block( ProofState( openFormula ) ), incompleteOk = false ), formula, fvs ) )
      attr( attributes: _* )( name.value )
      LemmaHandle( proofName )
    }
  }

  protected def const( c: Const ): Unit = addNow( c )

  protected def axiom( f: Formula )( implicit name: sourcecode.Name ): Unit =
    addProofNameDecl( name.value, Sequent() :+ f )

  protected def attr( attrNames: String* )( lemmaNames: String* ): Unit =
    for ( an <- attrNames; ln <- lemmaNames )
      addNow( Attributes.AddAttributeUpdate( ln, an ) )

  protected def infix( operator: String, precedence: Int, leftAssociative: Boolean = true, const: String = null ) =
    addNow( Notation.Infix( operator, if ( const == null ) operator else const, precedence, leftAssociative ) )

}

object logic extends Theory {

  const( hoc"arbitrary{?a}: ?a" )

  addNow( SkolemFun( EpsilonC( TVar( "a" ) ), le"^(P:?a>o) ?x P(x)" ) )
  val epsspec = lemma( hof"∃(x:?a) P(x) -> P(ε P)" ) {
    impR; insert( ExistsSkLeftRule( LogicalAxiom( hof"P(ε P: ?a)" ), le"ε P: ?a" ) )
  }

  fun( hoc"ite{?a}:o>?a>?a>?a", "ite true a b = a", "ite false a b = b" )
  val itepos = lemma( hof"p -> ite p a b = a", "simp", "nocombine" ) { induction( hov"p:o" ) onAll simp.w( "ite" ) }
  val iteneg = lemma( hof"-p -> ite p a b = b", "simp", "nocombine" ) { induction( hov"p:o" ) onAll simp.w( "ite" ) }
  val iteeq = lemma( hof"ite p a a = a", "simp" ) { cut( "", hof"p:o" ).onAll( simp.h ) }

  dfn( hof"compose{?a?b?c} (g:?b>?c) (f:?a>?b) x = g (f x)" )
  attr( "simp" )( "compose" )

}

object props extends Theory( logic ) {
  dfn( hof"assoc{?a} (f:?a>?a>?a) = (!x!y!z f(x,f(y,z))=f(f(x,y),z))" )
  dfn( hof"comm{?a} (f:?a>?a>?a) = (!x!y f(x,y)=f(y,x))" )
  dfn( hof"unit{?a} (f:?a>?a>?a) (z:?a) = (!x (f(x,z)=x & f(z,x)=x))" )
}
