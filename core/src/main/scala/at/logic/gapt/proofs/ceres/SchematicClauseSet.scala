package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.{ ProofDefinitions, ProofNames }
import at.logic.gapt.proofs.lk.{ EigenVariablesLK, LKProof }
import at.logic.gapt.proofs.{ Context, Sequent }

//Idea behind the type is for each proof symbol we have a  Map,  which maps configurations to a
// a Struct  and the expression of the case of the inductive definition.
object SchematicStruct {
  def apply(
    topSym:     String,
    cutConfig:  Sequent[Boolean]                  = Sequent[Boolean](),
    foundCases: Set[( String, Sequent[Boolean] )] = Set[( String, Sequent[Boolean] )]() )( implicit ctx: Context ): Option[Map[String, Map[Sequent[Boolean], Set[( ( Expr, Set[Var] ), Struct[Nothing] )]]]] = {
    val proofNames = ctx.get[ProofDefinitions].components.keySet
    //If the set of proof names in the context does not contain topSym
    //then we cannot construct the clause set and return None.
    if ( proofNames.contains( topSym ) ) {
      //Otherwise we find the definition of the proof symbol
      val CurrentProofsCases = ctx.get[ProofDefinitions].components.getOrElse( topSym, Set() )
      //Once we find the definition of the proof we construct the
      //Struct for the given proof modulo the provided cut configuration
      val theActualConfig = if ( cutConfig.isEmpty ) {
        val ( _, theSeq ) = ctx.get[ProofNames].names.getOrElse( topSym, { throw new Exception( "Unhandled case: " + topSym ) } )
        Sequent[Boolean]( theSeq.antecedent.map { x => false }, theSeq.succedent.map { x => false } )
      } else cutConfig
      val currentProofStruct: Set[( ( Expr, Set[Var] ), Struct[Nothing] )] =
        CurrentProofsCases.map {
          case ( placeHolder: Expr, assocProof: LKProof ) =>
            ( ( placeHolder, EigenVariablesLK( assocProof ) ),
              StructCreators.extract( assocProof, theActualConfig )( _ => true, ctx ) )
        }

      //After constructing the struct we need to find the dependencies associated
      // with the struct modulo the provided configuration.
      // The dependencies are the links to other proofs and self links
      val clauseSetDependencies = currentProofStruct.foldLeft( Set[( String, Sequent[Boolean] )]() )( ( w, e ) => {
        val temp: Set[Struct[Nothing]] = SchematicLeafs( e._2 ).foldLeft( Set[Struct[Nothing]]() )( ( g, pb ) => {
          val CLS( Apps( Const( pf, _ ), _ ), ccon, _ ) = pb
          if ( foundCases.contains( ( pf, ccon ) ) ) g
          else g + pb
        } )
        w ++ temp.foldLeft( Set[( String, Sequent[Boolean] )]() )( ( y, a ) => {
          val CLS( Apps( Const( pf, _ ), _ ), ccon, _ ) = a
          if ( pf.matches( topSym ) && ccon.equals( theActualConfig ) ) Set( ( pf, ccon ) )
          else y ++ Set( ( pf, ccon ) )
        } )
      } )
      // For each dependency we need to compute the clause set of that dependency by
      //recursively calling the SchematicClauseSet function.
      val dependencyClauseSets = clauseSetDependencies.map( x => SchematicStruct( x._1, x._2, foundCases ++ clauseSetDependencies - x + ( topSym -> theActualConfig ) ).getOrElse( Map() ) )
      //we merge the constructed map with all the dependencies
      Some( MapMerger( Set( MapMerger( dependencyClauseSets ) ) ++ Set( Map( topSym -> Map( theActualConfig -> currentProofStruct ) ) ) ) )
    } else None
  }
}
//merges maps of the particular from needed for schematic structs
object MapMerger {
  def apply( M1: Set[Map[String, Map[Sequent[Boolean], Set[( ( Expr, Set[Var] ), Struct[Nothing] )]]]] ): Map[String, Map[Sequent[Boolean], Set[( ( Expr, Set[Var] ), Struct[Nothing] )]]] =
    M1.foldLeft( Map[String, Map[Sequent[Boolean], Set[( ( Expr, Set[Var] ), Struct[Nothing] )]]]() )( ( x, y ) => {
      val themerge = mergeList( x, y )
      if ( themerge.keySet.nonEmpty ) themerge.keySet.map( w => ( w, themerge.getOrElse( w, List() ).foldLeft( Map[Sequent[Boolean], Set[( ( Expr, Set[Var] ), Struct[Nothing] )]]() )( ( str, end ) => mergeSet( str, end ) ) ) ) toMap
      else x
    } )

  def mergeList[K, V]( m1: Map[K, V], m2: Map[K, V] ): Map[K, List[V]] =
    if ( m1.keySet.nonEmpty && m2.keySet.nonEmpty )
      ( m1.keySet ++ m2.keySet ) map { i => i -> ( m1.get( i ).toList ::: m2.get( i ).toList ) } toMap
    else if ( m1.keySet.isEmpty && m2.keySet.nonEmpty )
      m2.keySet map { i => i -> m2.get( i ).toList } toMap

    else if ( m1.keySet.nonEmpty && m2.keySet.isEmpty )
      m1.keySet map { i => i -> m1.get( i ).toList } toMap
    else Map[K, List[V]]()

  def mergeSet[K, V]( m1: Map[K, Set[V]], m2: Map[K, Set[V]] ): Map[K, Set[V]] =
    Map() ++ ( for ( k <- m1.keySet ++ m2.keySet )
      yield k -> ( m1.getOrElse( k, Set() ) ++ m2.getOrElse( k, Set() ) ) )
}
//Allows the construction of instances of schematic structs
object InstanceOfSchematicStruct {
  def nat( i: Int, thevar: Var )( implicit ctx: Context ): Expr = {
    val suc = ctx.get[Context.Constants].constants.getOrElse( "s", Const( "0", Ti ) )
    if ( i > 0 ) Apps( suc, Seq( nat( i - 1, thevar ) ) )
    else thevar
  }
  def apply[Data](
    topSym:    String,
    cutConfig: Sequent[Boolean],
    sss:       Map[String, Map[Sequent[Boolean], Set[( ( Expr, Set[Var] ), Struct[Nothing] )]]],
    sigma:     Substitution,
    usedNames: Set[Var]                                                                         = Set[Var]() )( implicit ctx: Context ): Struct[Data] = {
    //First we extract the clause set associated with the given proof name
    val starterStruct = sss.getOrElse( topSym, Map() ).getOrElse( cutConfig, Set() )
    //we check if the starter clause set is empty or does not have
    //any free variables in common with the domain of sigma.
    //When this occurs we return an empty clause set.
    if ( starterStruct.isEmpty || !starterStruct.exists( x => { sigma.domain.equals( freeVariables( x._1._1 ) ) } ) )
      EmptyPlusJunction()
    else {
      //Here we locate the clause set specifically associated with the domain of sigma.
      val optionStructs = starterStruct.foldLeft( Set[( ( Expr, Set[Var] ), Struct[Nothing] )]() )( ( rightClauses, possibleclauses ) =>
        if ( sigma.domain.equals( freeVariables( possibleclauses._1._1 ) ) ) rightClauses + possibleclauses
        else rightClauses )
      //This is a weird case when we have more than one stepcase or
      // no stepcase. Not true when dealing with natural numbers.
      if ( optionStructs.size != 1 ) EmptyPlusJunction()
      else {
        //Here we select the clause set associated with the provided
        //substitution. We decide which clause set is associated
        //by selecting the clause set with the greatest difference
        //after substitution
        val StructToInstantiate = optionStructs.foldLeft( Set[( ( Int, Var ), ( Set[Var], Struct[Nothing] ) )]() )( ( reEx, excl ) => {
          val Apps( _, lSym ) = excl._1._1
          val headVar = if ( freeVariables( lSym.head ).size == 1 ) freeVariables( lSym.head ).head else Var( "", TBase( "nat" ) )
          reEx + ( ( ( LambdaPosition.differingPositions( excl._1._1, sigma( excl._1._1 ) ).size, headVar ), ( excl._1._2, excl._2 ) ) )
        } ).foldLeft( ( ( 0, Var( "", TBase( "nat" ) ) ), ( Set[Var](), EmptyPlusJunction().asInstanceOf[Struct[Nothing]] ) ) )( ( cll, excl ) => if ( cll._1._1 < excl._1._1 ) { excl } else { cll } )
        //The following code regularizes the clause set with respect to
        //the already used eigenvariables. Regularization of schematic
        //clause sets is an issue because variables which occur once in the
        // proof schema might occur at different levels in the instantiated proof
        val regularizedStruct =
          Set( usedNames.foldLeft( ( ( rename.awayFrom( usedNames ), usedNames ), StructToInstantiate._2._2 ) )(
            ( reClause, nameVar ) => Set[Var]( Var( reClause._1._1.fresh( nameVar.name ), nameVar.ty ) ).map( newVar =>
              ( ( reClause._1._1, reClause._1._2 + newVar ), RegularizeStruct( reClause._2, nameVar, newVar ) ) ).head ) ).map( x => ( x._1._2, x._2 ) ).head
        //we now have the instantiated and regularized Struct
        InstantiateStruct( regularizedStruct._2, sigma, StructToInstantiate._1._2, sss, usedNames ++ regularizedStruct._1 )
      }
    }
  }
}
//Used to regularize the struct
object RegularizeStruct {
  def apply[Data]( theStruct: Struct[Nothing], nameVar: Var, newVar: Var ): Struct[Data] = {
    theStruct match {
      case A( f, aux )                           => A( f.find( nameVar ).foldLeft( f )( ( ff, pos ) => ff.replace( pos, newVar ) ), aux )
      case Dual( EmptyPlusJunction() )           => Dual( EmptyPlusJunction() )
      case Dual( EmptyTimesJunction() )          => Dual( EmptyTimesJunction() )
      case Dual( x )                             => Dual( RegularizeStruct( x, nameVar, newVar ) )
      case EmptyPlusJunction()                   => EmptyPlusJunction()
      case Plus( EmptyPlusJunction(), x )        => Plus( EmptyPlusJunction(), RegularizeStruct( x, nameVar, newVar ) )
      case Plus( x, EmptyPlusJunction() )        => Plus( RegularizeStruct( x, nameVar, newVar ), EmptyPlusJunction() )
      case Plus( x, y )                          => Plus( RegularizeStruct( x, nameVar, newVar ), RegularizeStruct( y, nameVar, newVar ) )
      case EmptyTimesJunction()                  => EmptyTimesJunction()
      case Times( x, EmptyTimesJunction(), aux ) => Times( RegularizeStruct( x, nameVar, newVar ), EmptyTimesJunction(), aux )
      case Times( EmptyTimesJunction(), x, aux ) => Times( EmptyTimesJunction(), RegularizeStruct( x, nameVar, newVar ), aux )
      case Times( x, y, aux )                    => Times( RegularizeStruct( x, nameVar, newVar ), RegularizeStruct( y, nameVar, newVar ), aux )
      case CLS( pn, cc, l ) =>
        val Apps( name, vs ) = pn
        val newVs = vs.map( f => f.find( nameVar ).foldLeft( f )( ( ff, pos ) => ff.replace( pos, newVar ) ) )
        CLS( Apps( name, newVs ), cc, l )
      case _ => throw new Exception( "Unhandled case: " + theStruct )
    }
  }
}
//Used to instantiate the struct
object InstantiateStruct {
  def apply[Data](
    theStruct: Struct[Nothing],
    sigma:     Substitution,
    param:     Var,
    sss:       Map[String, Map[Sequent[Boolean], Set[( ( Expr, Set[Var] ), Struct[Nothing] )]]],
    usedNames: Set[Var] )( implicit ctx: Context ): Struct[Data] = {
    theStruct match {
      case A( f, aux ) => A(
        sigma( sigma.domain.foldLeft( f )( ( subForm, varSig ) =>
          ( if ( varSig.ty.equals( TBase( "nat" ) ) )
            subForm.find( InstanceOfSchematicStruct.nat( 1, varSig ) )
          else subForm.find( varSig ) ).foldLeft( subForm )( ( nRepl, curPos ) =>
            nRepl.replace( curPos, varSig ) ) ) ), aux )
      case Dual( EmptyPlusJunction() )           => Dual( EmptyPlusJunction() )
      case Dual( EmptyTimesJunction() )          => Dual( EmptyTimesJunction() )
      case Dual( x )                             => Dual( InstantiateStruct( x, sigma, param, sss, usedNames ) )
      case EmptyPlusJunction()                   => EmptyPlusJunction()
      case Plus( EmptyPlusJunction(), x )        => Plus( EmptyPlusJunction(), InstantiateStruct( x, sigma, param, sss, usedNames ) )
      case Plus( x, EmptyPlusJunction() )        => Plus( InstantiateStruct( x, sigma, param, sss, usedNames ), EmptyPlusJunction() )
      case Plus( x, y )                          => Plus( InstantiateStruct( x, sigma, param, sss, usedNames ), InstantiateStruct( y, sigma, param, sss, usedNames ) )
      case EmptyTimesJunction()                  => EmptyTimesJunction()
      case Times( x, EmptyTimesJunction(), aux ) => Times( InstantiateStruct( x, sigma, param, sss, usedNames ), EmptyTimesJunction(), aux )
      case Times( EmptyTimesJunction(), x, aux ) => Times( EmptyTimesJunction(), InstantiateStruct( x, sigma, param, sss, usedNames ), aux )
      case Times( x, y, aux )                    => Times( InstantiateStruct( x, sigma, param, sss, usedNames ), InstantiateStruct( y, sigma, param, sss, usedNames ), aux )
      case CLS( pn, cc, _ ) =>
        val Apps( Const( name, _ ), vs ) = pn
        val newVs = vs.map( f =>
          sigma( sigma.domain.foldLeft( f )( ( subform, varsig ) =>
            if ( varsig.ty.equals( TBase( "nat" ) ) )
              subform.find( InstanceOfSchematicStruct.nat( 1, varsig ) ).foldLeft( subform )( ( nrepl, curpos ) => {
              ctx.get[ProofNames].names.get( name ) match {
                case Some( proofName ) =>
                  val Apps( _, lsymPN ) = proofName._1
                  if ( param.equals( lsymPN.head ) ) nrepl
                  else if ( varsig.equals( param ) ) nrepl.replace( curpos, varsig )
                  else nrepl
                case None => nrepl
              }
            } )
            else subform ) ) )
        val setOfStructs = sss.getOrElse( name, Map() ).getOrElse( cc, Set() )
        //picks the correct induction step
        val ( _, ( Apps( _, vs2: Seq[Expr] ), _ ), _ ) = setOfStructs.foldLeft( ( 0, setOfStructs.head._1, setOfStructs.head._2 ) )( ( theCorrect, current ) => {
          val ( ( Apps( _, argsLink ), _ ), clauses ) = current
          val totalCount = newVs.zip( argsLink ).foldLeft( 0 )( ( count, curPair ) =>
            if ( sigma( curPair._2 ).contains( curPair._1 ) ) count + 1 else count )
          if ( totalCount > theCorrect._1 ) ( totalCount, current._1, clauses )
          else theCorrect
        } )
        val newsigma: Substitution = vs2.zip( newVs ).map {
          case ( one, two ) =>
            //We know this is at most size one for nat
            freeVariables( one ).map( x => one.find( x ) ).foldLeft( List[HOLPosition]() )( ( fin, ll ) => fin ++ ll ).headOption match {
              case Some( pos ) => ( one.get( pos ).getOrElse( one ), two.get( pos ).getOrElse( two ) )
              case None        => ( one, two )
            }
        }.foldLeft( Substitution() )( ( sub, pair ) => if ( freeVariables( pair._1 ).isEmpty ) sub else sub.compose( Substitution( pair._1.asInstanceOf[Var], pair._2 ) ) )
        InstanceOfSchematicStruct( name, cc, sss, newsigma, usedNames ).asInstanceOf[Struct[Data]]
      case _ => throw new Exception( "Unhandled case: " + theStruct )
    }
  }
}

