package at.logic.gapt.proofs.expansion
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLPosition

object eliminateDefsET {
  object DefinitionFormula {
    def unapply( f: Formula ): Option[( List[Var], HOLAtomConst, Formula )] = f match {
      case All.Block( vs, And( Imp( Apps( d1: HOLAtomConst, vs1 ), r1 ),
        Imp( r2, Apps( d2, vs2 ) ) ) ) if d1 == d2 && r1 == r2 && vs == vs1 && vs == vs2 =>
        Some( ( vs, d1, r2 ) )
      case _ => None
    }
  }
  private val negReplPos = HOLPosition( 1, 2 )
  private val posReplPos = HOLPosition( 2, 1 )

  def apply( ep: ExpansionProof, pureFolWithoutEq: Boolean ): ExpansionProof = {
    val definitions = ep.expansionSequent.antecedent.collect {
      case DefinitionFormula( _, c, _ ) => c
    }
    apply( ep, pureFolWithoutEq, definitions.toSet[Const] )
  }

  def apply( ep: ExpansionProof, pureFolWithoutEq: Boolean, definitions: Set[Const] ): ExpansionProof =
    ExpansionProof( definitions.foldLeft( ep )( apply( _, _, pureFolWithoutEq ) ).expansionSequent )

  private def apply( ep: ExpansionProof, definitionConst: Const, pureFolWithoutEq: Boolean ): ExpansionProof = {
    val definitionFormula @ DefinitionFormula( vs, _, definedFormula ) =
      ep.expansionSequent.antecedent.map( _.shallow ).find {
        case DefinitionFormula( _, `definitionConst`, _ ) => true
        case _ => false
      }.getOrElse( return ep )

    val insts0 = for {
      ETWeakQuantifierBlock( `definitionFormula`, n, insts ) <- ep.expansionSequent.antecedent
      ( as, inst ) <- insts
      repl <- inst( negReplPos ) ++ inst( posReplPos )
    } yield as -> repl

    var insts = Map() ++ insts0.groupBy( _._1 ).mapValues { repls =>
      val shallow = repls.head._2.shallow
      ETMerge( shallow, Polarity.Positive, repls.map( _._2 ).filter( _.polarity.positive ) ) ->
        ETMerge( shallow, Polarity.Negative, repls.map( _._2 ).filter( _.polarity.negative ) )
    }

    val rest = ep.expansionSequent.filterNot { et => et.polarity.inAnt && et.shallow == definitionFormula }
    val usesites = rest.elements.flatMap { _.subProofs }.
      collect { case ETAtom( Apps( `definitionConst`, args ), pol ) => ( args, pol ) }.toSet
    insts = Map() ++
      usesites.map { _._1 }.map { as =>
        val ras = Substitution( vs zip as )( definedFormula )
        as -> ( ETWeakening( ras, Polarity.Positive ), ETWeakening( ras, Polarity.Negative ) )
      } ++
      insts

    if ( !pureFolWithoutEq ) {
      val newNegRepl = ETMerge( definedFormula, Polarity.Negative, insts.values.map { _._2 }.map { generalizeET( _, definedFormula ) } )
      val newPosRepl = ETMerge( definedFormula, Polarity.Positive, insts.values.map { _._1 }.map { generalizeET( _, definedFormula ) } )
      insts = insts map { case ( as, _ ) => as -> Substitution( vs zip as )( newPosRepl -> newNegRepl ) }
    }

    def replm: PartialFunction[Expr, Expr] = {
      case Apps( `definitionConst`, as ) => Substitution( vs zip as )( definedFormula )
    }
    def replf( f: Formula ): Formula = TermReplacement( f, replm )
    def repl( et: ExpansionTree ): ExpansionTree = et match {
      case ETMerge( a, b )                      => ETMerge( repl( a ), repl( b ) )
      case ETWeakening( sh, pol )               => ETWeakening( replf( sh ), pol )

      case ETTop( _ ) | ETBottom( _ )           => et
      case ETNeg( ch )                          => ETNeg( repl( ch ) )
      case ETAnd( l, r )                        => ETAnd( repl( l ), repl( r ) )
      case ETOr( l, r )                         => ETOr( repl( l ), repl( r ) )
      case ETImp( l, r )                        => ETImp( repl( l ), repl( r ) )
      case ETWeakQuantifier( sh, is )           => ETWeakQuantifier( replf( sh ), Map() ++ is.mapValues( repl ) )
      case ETStrongQuantifier( sh, ev, ch )     => ETStrongQuantifier( replf( sh ), ev, repl( ch ) )
      case ETSkolemQuantifier( sh, st, sd, ch ) => ETSkolemQuantifier( replf( sh ), st, sd, repl( ch ) )

      case ETDefinition( _, ETAtom( Apps( `definitionConst`, as ), pol ) ) =>
        if ( pol.positive ) insts( as )._1 else insts( as )._2
      case ETDefinition( _, _ )                              => et
      case ETAtom( Apps( f, _ ), _ ) if f != definitionConst => et
    }

    for ( ( _, ( pos, neg ) ) <- insts ) {
      require( !constants( pos.deep ).contains( definitionConst ) )
      require( !constants( neg.deep ).contains( definitionConst ) )
    }

    val newCuts = ETWeakQuantifier.withMerge(
      ETCut.cutAxiom,
      insts.values.map { case ( pos, neg ) => pos.shallow -> ETImp( pos, neg ) } )

    val newES = ETMerge( newCuts +: rest.map( repl ) )

    eliminateMerges( ExpansionProof( newES ) )
  }
}
