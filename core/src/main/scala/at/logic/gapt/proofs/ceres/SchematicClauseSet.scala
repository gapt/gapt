package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ mergeMapToListValues, mergeMapToSetValues, natMaker }
import at.logic.gapt.proofs.Context.{ ProofDefinitions, ProofNames }
import at.logic.gapt.proofs.lk.{ EigenVariablesLK, LKProof }
import at.logic.gapt.proofs.{ Context, Sequent }

//Idea behind the type is for each proof symbol we have a  Map,  which maps configurations to a
// a Struct  and the expression of the case of the inductive definition.
object SchematicStruct {
  def apply( topSym: String, cutConfig: Sequent[Boolean] = Sequent[Boolean](),
             foundCases: Set[( String, Sequent[Boolean] )] = Set[( String, Sequent[Boolean] )]() )( implicit ctx: Context ): Option[Map[String, Map[Sequent[Boolean], Set[( ( Expr, Set[Var] ), Struct[Nothing] )]]]] = {
    //If the context does not contain topSym then we cannot construct the struct and return None.
    if ( ctx.get[ProofDefinitions].components.keySet.contains( topSym ) ) {
      //If no cut config is provided we construct the default config
      val theActualConfig = if ( cutConfig.isEmpty ) {
        val ( _, theSeq ) = ctx.get[ProofNames].names.getOrElse( topSym, { throw new Exception( "Unhandled case: " + topSym ) } )
        Sequent[Boolean]( theSeq.antecedent.map { _ => false }, theSeq.succedent.map { _ => false } )
      } else cutConfig
      // We construct the struct for the given proof modulo the cutConfig
      val currentProofStruct: Set[( ( Expr, Set[Var] ), Struct[Nothing] )] =
        ctx.get[ProofDefinitions].components.getOrElse( topSym, Set() ).map {
          case ( placeHolder: Expr, assocProof: LKProof ) => ( ( placeHolder, EigenVariablesLK( assocProof ) ),
            StructCreators.extract( assocProof, theActualConfig )( _ => true, ctx ) )
        }
      //After constructing the struct we need to find all CLS terms
      val clauseSetDependencies = currentProofStruct.foldLeft( Set[( String, Sequent[Boolean] )]() )( ( w, e ) => {
        w ++ SchematicLeafs( e._2 ).foldLeft( Set[Struct[Nothing]]() )( ( g, pb ) => {
          val CLS( Apps( Const( pf, _ ), _ ), ccon, _ ) = pb
          if ( foundCases.contains( ( pf, ccon ) ) ) g
          else g + pb
        } ).foldLeft( Set[( String, Sequent[Boolean] )]() )( ( y, a ) => {
          val CLS( Apps( Const( pf, _ ), _ ), ccon, _ ) = a
          if ( pf.matches( topSym ) && ccon.equals( theActualConfig ) ) Set( ( pf, ccon ) )
          else y ++ Set( ( pf, ccon ) )
        } )
      } )
      // For each CLS term we  compute the Struct and merge the results
      // with the principal struct
      Some( MapMerger( Set( MapMerger( clauseSetDependencies.map( x => SchematicStruct( x._1, x._2,
        foundCases ++ clauseSetDependencies - x + ( topSym -> theActualConfig ) )
        .getOrElse( Map() ) ) ) ) ++ Set( Map( topSym -> Map( theActualConfig -> currentProofStruct ) ) ) ) )
    } else None
  }
}
//merges maps of the particular from needed for schematic structs
object MapMerger {
  def apply( M1: Set[Map[String, Map[Sequent[Boolean], Set[( ( Expr, Set[Var] ), Struct[Nothing] )]]]] ): Map[String, Map[Sequent[Boolean], Set[( ( Expr, Set[Var] ), Struct[Nothing] )]]] =
    M1.foldLeft( Map[String, Map[Sequent[Boolean], Set[( ( Expr, Set[Var] ), Struct[Nothing] )]]]() )( ( x, y ) => {
      val themerge = mergeMapToListValues( x, y )
      if ( themerge.keySet.nonEmpty ) themerge.keySet.map( w =>
        ( w, themerge.getOrElse( w, List() ).foldLeft(
          Map[Sequent[Boolean], Set[( ( Expr, Set[Var] ), Struct[Nothing] )]]() )( ( str, end ) =>
            mergeMapToSetValues( str, end ) ) ) ) toMap
      else x
    } )
}

//Allows the construction of instances of schematic structs
object InstanceOfSchematicStruct {

  def apply[Data](
    topSym:    String,
    cutConfig: Sequent[Boolean],
    sss:       Map[String, Map[Sequent[Boolean], Set[( ( Expr, Set[Var] ), Struct[Nothing] )]]],
    sigma:     Substitution,
    usedNames: Set[Var]                                                                         = Set[Var]() )( implicit ctx: Context ): Struct[Data] = {
    val starterStruct = sss.getOrElse( topSym, Map() ).getOrElse( cutConfig, Set() )
    // check if the Structis empty or does not match sigma
    if ( starterStruct.isEmpty || !starterStruct.exists( x => { sigma.domain.equals( freeVariables( x._1._1 ) ) } ) ) EmptyPlusJunction()
    else {
      //Here we locate the Struct associated with sigma.
      val optionStructs = starterStruct.foldLeft( Set[( ( Expr, Set[Var] ), Struct[Nothing] )]() )( ( rightClauses, possibleclauses ) =>
        if ( sigma.domain.equals( freeVariables( possibleclauses._1._1 ) ) ) rightClauses + possibleclauses
        else rightClauses )
      //Can only handle one stepcase currently
      if ( optionStructs.size != 1 ) EmptyPlusJunction()
      else {
        // We decide which case to used based on the result of applying the substitution
        val StructToInstantiate = optionStructs.foldLeft( Set[( ( Int, Var ), ( Set[Var], Struct[Nothing] ) )]() )( ( reEx, excl ) => {
          val Apps( _, lSym ) = excl._1._1
          val headVar = if ( freeVariables( lSym.head ).size == 1 ) freeVariables( lSym.head ).head else Var( "", TBase( "nat" ) )
          reEx + ( ( ( LambdaPosition.differingPositions( excl._1._1, sigma( excl._1._1 ) ).size, headVar ), ( excl._1._2, excl._2 ) ) )
        } ).foldLeft( ( ( 0, Var( "", TBase( "nat" ) ) ), ( Set[Var](), EmptyPlusJunction().asInstanceOf[Struct[Nothing]] ) ) )( ( cll, excl ) => if ( cll._1._1 < excl._1._1 ) { excl } else { cll } )
        //The following code regularizes the clause set with respect to
        //the already used eigenvariables.
        val regularizedStruct = Set( usedNames.foldLeft( ( ( rename.awayFrom( usedNames ), usedNames ), StructToInstantiate._2._2 ) )(
          ( reClause, nameVar ) => Set[Var]( Var( reClause._1._1.fresh( nameVar.name ), nameVar.ty ) ).map( newVar =>
            ( ( reClause._1._1, reClause._1._2 + newVar ), RegularizeStruct( reClause._2, nameVar, newVar ) ) ).head ) ).map( x => ( x._1._2, x._2 ) ).head
        //we now unfold the dependences
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
  def apply[Data]( theStruct: Struct[Nothing], sigma: Substitution, param: Var,
                   sss:       Map[String, Map[Sequent[Boolean], Set[( ( Expr, Set[Var] ), Struct[Nothing] )]]],
                   usedNames: Set[Var] )( implicit ctx: Context ): Struct[Data] = {
    theStruct match {
      case A( f, aux ) => A( sigma( sigma.domain.foldLeft( f )( ( subForm, varSig ) =>
        ( if ( varSig.ty.equals( TBase( "nat" ) ) ) subForm.find( natMaker( 1, varSig ) )
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
              subform.find( natMaker( 1, varsig ) ).foldLeft( subform )( ( nrepl, curpos ) => {
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
        //picks the correct induction case
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

