package gapt.proofs.context

import gapt.expr.Abs
import gapt.expr.Const
import gapt.expr.Definition
import gapt.expr.Expr
import gapt.expr.FunctionType
import gapt.expr.Quant
import gapt.expr.Replaceable
import gapt.expr.baseTypes
import gapt.expr.constants
import gapt.expr.containedNames
import gapt.expr.hol.SkolemFunctions
import gapt.expr.typeVariables
import gapt.proofs.Sequent
import gapt.proofs.context.facet.Definitions
import gapt.proofs.context.update.SkolemFun
import gapt.proofs.context.update.Sort
import gapt.proofs.context.update.Update
import gapt.proofs.lk.LKProof
import gapt.proofs.resolution.ResolutionProof

class MutableContext( private var ctx_ :ImmutableContext ) extends Context {
  override def state: State = ctx.state
  override def updates: List[Update] = ctx.updates
  override def toImmutable: ImmutableContext = ctx

  override def toString: String = ctx.toString

  def ctx: ImmutableContext = ctx_
  def ctx_=( newCtx: ImmutableContext ): Unit = ctx_ = newCtx

  def +=( update: Update ): Unit = ctx += update
  def ++=( updates: Iterable[Update] ): Unit = ctx ++= updates

  def addDefinition( by: Expr, name: => String = newNameGenerator.freshWithIndex( "D" ), reuse: Boolean = true ): Const = {
    if ( reuse ) {
      for ( ( d, _ ) <- get[Definitions].definitions.find( _._2 == by ) ) {
        return Const( d, by.ty )
      }
    }
    val what = Const( name, by.ty, typeVariables( by ).toList )
    this += Definition( what, by )
    what
  }

  def addSkolemSym( defn: Expr, name: => String = newNameGenerator.freshWithIndex( "s" ), reuse: Boolean = true ): Const = {
    if ( reuse ) {
      for ( ( d, _ ) <- get[SkolemFunctions].skolemDefs.find( _._2 == defn ) ) {
        return d
      }
    }
    val Abs.Block( vs, Quant( v, _, _ ) ) = defn
    val sym = Const( name, FunctionType( v.ty, vs.map( _.ty ) ) )
    this += SkolemFun( sym, defn )
    sym
  }
}
object MutableContext {
  def default(): MutableContext = Context.default.newMutable
  def guess( exprs: Traversable[Expr] ): MutableContext = Context.guess( exprs ).newMutable
  def guess( exprs: Expr* ): MutableContext = guess( exprs )
  def guess( seq: Sequent[Expr] ): MutableContext = guess( seq.elements )
  def guess( cnf: Traversable[Sequent[Expr]] )( implicit dummyImplicit: DummyImplicit ): MutableContext = guess( cnf.view.flatMap( _.elements ) )
  def guess[R, S]( rs: Traversable[R] )( implicit ev: Replaceable[R, S] ): MutableContext =
    guess( rs.view.flatMap( ev.names ) )
  def guess( p: LKProof ): MutableContext =
    guess( containedNames( p ) ) // TODO: add (Skolem) definitions

  def guess( p: ResolutionProof ): MutableContext = {
    val ctx = default()

    val cs = containedNames( p )

    val tys = cs.flatMap( c => baseTypes( c.ty ) )
    for ( ty <- tys if !ctx.isType( ty ) )
      ctx += Sort( ty )

    val defs: Map[Const, Expr] = p.definitions.toMap
    def add( c: Const ): Unit =
      if ( ctx.constant( c.name ).isEmpty ) defs.get( c ) match {
        case Some( d ) =>
          constants( d ).foreach( add )
          ctx += Definition( c, d )
        case None =>
          ctx += c
      }
    cs.foreach { case c: Const => add( c ) case _ => }

    ctx
  }
}

