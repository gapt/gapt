package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.{ ProofDefinitions, ProofNames }
import at.logic.gapt.proofs.lk.{ CLSTerm, EigenVariablesLK, LKProof, SequentComposition, SequentTerm }
import at.logic.gapt.proofs.{ Context, HOLSequent, Sequent }

//Idea behind the type is for each proof symbol we have a  Map,  which maps configurations to a set of sequents over atoms
//representing the clauses and the expression of the case of the inductive definition.
object SchematicClauseSet {
  def apply(
    topSym:     String,
    cutConfig:  HOLSequent                  = HOLSequent(),
    foundCases: Set[( String, HOLSequent )] = Set[( String, HOLSequent )]() )( implicit ctx: Context ): Option[Map[String, Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[SequentComposition] )]]]] = {
    val proofNames = ctx.get[ProofDefinitions].components.keySet
    //If the set of proof names in the context does not contain topSym
    //then we cannot construct the clause set and return None.
    if ( proofNames.contains( topSym ) ) {
      //Otherwise we find the definition of the proof symbol
      val CurrentProofsCases = ctx.get[ProofDefinitions].components.getOrElse( topSym, Set() )
      //Once we find the definition of the proof we construct the
      //Structs for the given proof modulo the provided cut
      //configuration
      val currentProofsStructs: Set[( ( Expr, Set[Var] ), Struct[Nothing] )] =
        CurrentProofsCases.map {
          case ( placeHolder: Expr, assocProof: LKProof ) =>
            ( ( placeHolder, EigenVariablesLK( assocProof ) ),
              StructCreators.extract( assocProof, FindAncestors( assocProof.endSequent, cutConfig ) )( _ => true, ctx ) )
        }
      //After constructing the struct we need to find the dependencies associated
      // with the struct modulo the provided configuration.
      // The dependencies are the links to other proofs and self links
      val clauseSetDependencies = StructDependencies( topSym, cutConfig, currentProofsStructs, foundCases )
      // For each dependency we need to compute the clause set of that dependency by
      //recursively calling the SchematicClauseSet function.
      val dependencyClauseSets = clauseSetDependencies.map( x => {
        val inducSet = foundCases ++
          ( clauseSetDependencies - x ) + ( topSym -> cutConfig )
        SchematicClauseSet( x._1, x._2, inducSet ).getOrElse( Map() )
      } )
      //The resulting dependency need to be merge together to construct a larger
      //schematic clause set
      val dependencyClauseSetsMerged = MapMerger( dependencyClauseSets )
      //Finally we construct the map for the current struct
      val TopClauses: Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[SequentComposition] )]] =
        CutConfigProofClauseSetMaps( cutConfig, currentProofsStructs )
      //we merge the constructed map with all the dependencies
      val preCleanedClauseSet = MapMerger( Set( dependencyClauseSetsMerged ) ++ Set( Map( ( topSym, TopClauses ) ) ) )
      Some( CleanClauseSet( preCleanedClauseSet ) )
    } else None
  }

  object FindAncestors {
    //Finds all formula in sequent h1 which are also in h2
    //and returns a boolean sequent indicating the overlap
    def apply( h1: HOLSequent, h2: HOLSequent ): Sequent[Boolean] =
      Sequent( convert( h1.antecedent, h2.antecedent ), convert( h1.succedent, h2.succedent ) )

    //Checks if, for every formula in S1 there is a formula in S2 which is similar to
    //it modulo terms.
    def convert( S1: Vector[Formula], S2: Vector[Formula] ): Vector[Boolean] =
      S1.map( f1 => S2.foldLeft( false )( ( same, f2 ) => ancestorInstanceOf( f1, f2 ) || same ) )

    def ancestorInstanceOf( F1: Expr, F2: Expr ): Boolean = {
      val listOfDiff = LambdaPosition.differingPositions( F1, F2 )
      val finality = listOfDiff.foldLeft( true )( ( isOK, pos ) => {
        val F1Pos = F1.get( pos ) match {
          case Some( x ) => x
          case None      => F1
        }
        val F2Pos = F2.get( pos ) match {
          case Some( x ) => x
          case None      => F2
        }
        ( F1Pos, F2Pos ) match {
          case ( Var( _, _ ), _ )             => isOK && F1Pos.ty.equals( F2Pos.ty )
          case ( Const( _, _ ), Var( _, _ ) ) => isOK && F1Pos.ty.equals( F2Pos.ty )
          case ( Apps( _, _ ), Var( _, _ ) )  => isOK && F1Pos.ty.equals( F2Pos.ty )
          case ( Apps( c, s ), Apps( d, t ) ) => isOK && c.equals( d ) && s.zip( t ).forall( th => ancestorInstanceOf( th._1, th._2 ) )
          case _                              => false
        }
      } )
      finality
    }
  }

  //Finds the proof links within the given struct
  object StructDependencies {
    def apply(
      topSym:        String,
      cutConfig:     HOLSequent,
      currentStruct: Set[( ( Expr, Set[Var] ), Struct[Nothing] )],
      foundCases:    Set[( String, HOLSequent )] ): Set[( String, HOLSequent )] =
      currentStruct.foldLeft( Set[( String, HOLSequent )]() )( ( w, e ) => {
        val temp: Set[Struct[Nothing]] = SchematicLeafs( e._2 ).foldLeft( Set[Struct[Nothing]]() )( ( g, pb ) => {
          val CLS( pf, ccon, _, _ ) = pb
          if ( foundCases.contains( ( pf, ccon ) ) ) g
          else g + pb
        } )
        val CLSyms = temp.foldLeft( Set[( String, HOLSequent )]() )( ( y, a ) => {
          val CLS( pf, ccon, _, _ ) = a
          if ( pf.matches( topSym ) && ccon.equals( cutConfig ) ) Set( ( pf, ccon ) )
          else y ++ Set( ( pf, ccon ) )
        } )
        w ++ CLSyms
      } )
  }

  object MapMerger {
    def apply( M1: Set[Map[String, Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[SequentComposition] )]]]] ): Map[String, Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[SequentComposition] )]]] =
      M1.foldLeft( Map[String, Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[SequentComposition] )]]]() )( ( x, y ) => {
        val themerge = mergeList( x, y )
        if ( themerge.keySet.nonEmpty ) themerge.keySet.map( w => ( w, themerge.getOrElse( w, List() ).foldLeft( Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[SequentComposition] )]]() )( ( str, end ) => mergeSet( str, end ) ) ) ) toMap
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

  //Constructs clause sets modulo the cut configurations and proofs
  object CutConfigProofClauseSetMaps {
    def apply(
      cutConfig:     HOLSequent,
      currentStruct: Set[( ( Expr, Set[Var] ), Struct[Nothing] )] ): Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[SequentComposition] )]] =
      currentStruct.map { case ( ( ex, sv ), sn ) => Map( cutConfig -> Set( ( ( ex, sv ), CharacteristicClauseSet( sn, cutConfig ) ) ) ) }.
        foldLeft( Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[SequentComposition] )]]() )( ( aHOLIndexedMap, instance ) =>
          instance.keySet.foldLeft( Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[SequentComposition] )]]() )( ( variationMap, sequentInstances ) =>
            if ( aHOLIndexedMap.keySet.contains( sequentInstances ) ) variationMap + ( sequentInstances -> ( instance.getOrElse( sequentInstances, Set() ) ++ aHOLIndexedMap.getOrElse( sequentInstances, Set() ) ) )
            else variationMap + ( sequentInstances -> instance.getOrElse( sequentInstances, Set() ) ) ) )
  }

  def nat( i: Int, thevar: Var )( implicit ctx: Context ): Expr = {
    val suc = ctx.get[Context.Constants].constants.getOrElse( "s", Const( "0", Ti ) )
    if ( i > 0 ) Apps( suc, Seq( nat( i - 1, thevar ) ) )
    else thevar
  }

  object CleanClauseSet {
    def apply( precleaned: Map[String, Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[SequentComposition] )]]] ): Map[String, Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[SequentComposition] )]]] =
      precleaned.keySet.map( sym =>
        ( sym, precleaned.getOrElse( sym, Map() ).keySet.foldLeft( Set[HOLSequent]() )( ( goodOnes, posGood ) =>
          if ( goodOnes.isEmpty ) Set( posGood )
          else {
            val newGood = goodOnes.map( x =>
              if ( SequentInstanceOf( posGood, x ) || SequentInstanceOf( x, posGood ) )
                SimplierOfSequents( x, posGood )
              else x )
            if ( !newGood.contains( posGood ) && goodOnes.forall( x =>
              !( SequentInstanceOf( posGood, x ) || SequentInstanceOf( x, posGood ) ) ) ) newGood + posGood
            else newGood
          } ).map( x => ( x, precleaned.getOrElse( sym, Map() ).getOrElse( x, Set() ) ) ).
          foldLeft( Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[SequentComposition] )]]() )( ( finMap, pairMap ) =>
            finMap + ( pairMap._1 -> pairMap._2 ) ) ) ).foldLeft( Map[String, Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[SequentComposition] )]]]() )( ( finMap, pairMap ) =>
        finMap + ( pairMap._1 -> pairMap._2 ) )
  }

  object SimplierOfSequents {
    def apply( S1: HOLSequent, S2: HOLSequent ): HOLSequent =
      Set( simplierOfFormulaSets( S1.antecedent.toSet, S2.antecedent.toSet ) ).map {
        case ( x, y ) =>
          Set( simplierOfFormulaSets( S1.succedent.toSet, S2.succedent.toSet ) ).map {
            case ( z, w ) =>
              ( x + z, y + w )
          }.head
      }.map { case ( x, y ) => if ( x >= y ) S1 else S2 }.head

    private def simplierOfFormulaSets( SF1: Set[Formula], SF2: Set[Formula] ): ( Int, Int ) =
      Set( SF1.map( x => {
        ( x, SF2.find( y => SequentInstanceOf.FormulaInstanceOf( x, y ) ) )
      } ).foldLeft( ( 0, 0 ) )( ( soFar, cur ) => Set( simplierOfFormula( cur._1, cur._2.getOrElse( cur._1 ) ) ).map { case ( x, y ) => ( x + soFar._1, x + soFar._2 ) }.head ) ).map { case ( x, y ) => if ( x >= y ) ( 1, 0 ) else ( 0, 1 ) }.head

    def simplierOfFormula( F1: Formula, F2: Formula ): ( Int, Int ) =
      LambdaPosition.differingPositions( F1, F2 ).foldLeft( ( 0, 0 ) )( ( cur, next ) => {
        val ex1 = F1.get( next ).getOrElse( Var( "", TBase( "nat" ) ) )
        val ex2 = F2.get( next ).getOrElse( Var( "", TBase( "nat" ) ) )
        if ( ex1.ty.eq( TBase( "nat" ) ) )
          if ( ex1.contains( ex2 ) && !ex2.contains( ex1 ) && ( cur._1 == 0 ) ) ( 0, 1 )
          else if ( ex1.contains( ex2 ) && !ex2.contains( ex1 ) && ( cur._1 == 1 ) ) ( 0, 0 )
          else if ( ex2.contains( ex1 ) && !ex1.contains( ex2 ) && ( cur._2 == 0 ) ) ( 1, 0 )
          else if ( ex2.contains( ex1 ) && !ex1.contains( ex2 ) && ( cur._2 == 1 ) ) ( 0, 0 )
          else cur
        else cur
      } )
  }

  object InstantiateClauseSetSchema {
    def apply(
      topSym:    String,
      cutConfig: HOLSequent,
      css:       Map[String, Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[SequentComposition] )]]],
      sigma:     Substitution,
      usedNames: Set[Var]                                                                           = Set[Var]() )( implicit ctx: Context ): Set[Sequent[Atom]] = {
      //First we extract the clause set associated with the given proof name
      val starterClauseSet = css.getOrElse( topSym, Map() ).getOrElse( cutConfig, Set() )
      //we check if the starter clause set is empty or does not have
      //any free variables in common with the domain of sigma.
      //When this occurs we return an empty clause set.
      if ( starterClauseSet.isEmpty ||
        !starterClauseSet.exists( x => {
          sigma.domain.equals( freeVariables( x._1._1 ) )
        } ) )
        Set[Sequent[Atom]]()
      else {
        //Here we are looked for the clause set specifically
        //associated with the domain of sigma.
        val optionClauseSets = starterClauseSet.foldLeft( Set[( ( Expr, Set[Var] ), Set[SequentComposition] )]() )( ( rightClauses, possibleclauses ) =>
          if ( sigma.domain.equals( freeVariables( possibleclauses._1._1 ) ) ) rightClauses + possibleclauses
          else rightClauses )
        //This is a weird case when we have more than one stepcase or
        // no stepcase Not True when dealing with natural numbers.
        if ( optionClauseSets.size != 1 ) Set[Sequent[Atom]]()
        else {
          //Here we select the clause set associated with the provided
          //substitution. We decide which clause set is associated
          //by selecting the clause set with the greatest difference
          //after substitution
          val clauseSetToInstantiate = optionClauseSets.foldLeft( Set[( ( Int, Var ), ( Set[Var], Set[SequentComposition] ) )]() )( ( reEx, excl ) => {
            val Apps( _, lSym ) = excl._1._1
            val headVar = if ( freeVariables( lSym.head ).size == 1 ) freeVariables( lSym.head ).head else Var( "", TBase( "nat" ) )
            reEx + ( ( ( LambdaPosition.differingPositions( excl._1._1, sigma( excl._1._1 ) ).size, headVar ), ( excl._1._2, excl._2 ) ) )
          } ).foldLeft( ( ( 0, Var( "", TBase( "nat" ) ) ), ( Set[Var](), Set[SequentComposition]() ) ) )( ( cll, excl ) => if ( cll._1._1 < excl._1._1 ) { excl } else { cll } )
          //The following code regularizes the clause set with respect to
          //the already used eigenvariables. Regularization of schematic
          //clause sets is an issue because variables which occur once in the
          // proof schema might occur at different levels in the instantiated
          //proof
          val regularClauseSetToInstantiate =
            Set( usedNames.foldLeft( ( ( rename.awayFrom( usedNames ), usedNames ), clauseSetToInstantiate._2._2 ) )(
              ( reClause, nameVar ) => Set[Var]( Var( reClause._1._1.fresh( nameVar.name ), nameVar.ty ) ).map( newVar =>
                ( ( reClause._1._1, reClause._1._2 + newVar ), reClause._2.map( x => SequentComposition( x.composedSequents.map( parts =>
                  parts match {
                    case Sequent( ante, suc ) => Sequent(
                      ante.map( f => f.asInstanceOf[Atom].find( nameVar ).foldLeft( f )( ( ff, pos ) => ff.asInstanceOf[Atom].replace( pos, newVar ).asInstanceOf[Atom] ) ),
                      suc.map( f => f.asInstanceOf[Atom].find( nameVar ).foldLeft( f )( ( ff, pos ) => ff.asInstanceOf[Atom].replace( pos, newVar ).asInstanceOf[Atom] ) ) )
                    case CLSTerm( pn, cc, args ) => CLSTerm(
                      pn,
                      Sequent(
                        cc.antecedent.map( f => f.find( nameVar ).foldLeft( f )( ( ff, pos ) => ff.replace( pos, newVar ).asInstanceOf[Atom] ) ),
                        cc.succedent.map( f => f.find( nameVar ).foldLeft( f )( ( ff, pos ) => ff.replace( pos, newVar ).asInstanceOf[Atom] ) ) ),
                      args.map( f => f.find( nameVar ).foldLeft( f )( ( ff, pos ) => ff.replace( pos, newVar ) ) ) )
                    case _ => sys.error( "Should not be here" )
                  } ).asInstanceOf[Set[SequentTerm]] ) ) ) ).head ) ).map( x => ( x._1._2, x._2 ) ).head

          val instantiatedClauses = regularClauseSetToInstantiate._2.map( comp =>
            SequentComposition( comp.composedSequents.map( x => x match {
              case Sequent( ante, suc ) =>
                sigma( Sequent(
                  ante.map( form =>
                    sigma.domain.foldLeft( form.asInstanceOf[Formula] )( ( subForm, varSig ) =>
                      ( if ( varSig.ty.equals( TBase( "nat" ) ) )
                        subForm.find( nat( 1, varSig ) )
                      else subForm.find( varSig ) ).foldLeft( subForm )( ( nRepl, curPos ) =>
                        nRepl.replace( curPos, varSig ) ) ) ),
                  suc.map( form =>
                    sigma.domain.foldLeft( form.asInstanceOf[Formula] )( ( subForm, varSig ) =>
                      ( if ( varSig.ty.equals( TBase( "nat" ) ) )
                        subForm.find( nat( 1, varSig ) )
                      else subForm.find( varSig ) ).foldLeft( subForm )( ( nRepl, curPos ) =>
                        nRepl.replace( curPos, varSig ) ) ) ) ) ).asInstanceOf[SequentTerm]
              case CLSTerm( pn, cc, args ) =>
                CLSTerm( pn, sigma( HOLSequent(
                  cc.antecedent.map( form =>
                    sigma.domain.foldLeft( form )( ( subform, varsig ) =>
                      if ( varsig.ty.equals( TBase( "nat" ) ) )
                        subform.find( nat( 1, varsig ) ).foldLeft( subform )( ( nrepl, curpos ) => {
                        ctx.get[ProofNames].names.get( pn ) match {
                          case Some( proofName ) =>
                            val Apps( _, lsymPN ) = proofName._1
                            val clsvar = lsymPN.head
                            if ( clauseSetToInstantiate._1._2.equals( clsvar ) ) nrepl
                            else if ( varsig.equals( clauseSetToInstantiate._1._2 ) ) nrepl.replace( curpos, varsig )
                            else nrepl
                          case None => nrepl
                        }
                      } )
                      else subform ) ),
                  cc.succedent.map( form =>
                    sigma.domain.foldLeft( form )( ( subform, varsig ) =>
                      if ( varsig.ty.equals( TBase( "nat" ) ) )
                        subform.find( nat( 1, varsig ) ).foldLeft( subform )( ( nrepl, curpos ) => {
                        ctx.get[ProofNames].names.get( pn ) match {
                          case Some( proofName ) =>
                            val Apps( _, lsymPN ) = proofName._1
                            val clsvar = lsymPN.head
                            if ( clauseSetToInstantiate._1._2.equals( clsvar ) ) nrepl
                            else if ( varsig.equals( clauseSetToInstantiate._1._2 ) ) nrepl.replace( curpos, varsig )
                            else nrepl
                          case None => nrepl
                        }
                      } )
                      else subform ) ) ) ),
                  args.map( form =>
                    sigma( sigma.domain.foldLeft( form )( ( subform, varsig ) =>
                      if ( varsig.ty.equals( TBase( "nat" ) ) )
                        subform.find( nat( 1, varsig ) ).foldLeft( subform )( ( nrepl, curpos ) => {
                        ctx.get[ProofNames].names.get( pn ) match {
                          case Some( proofName ) =>
                            val Apps( _, lsymPN ) = proofName._1
                            val clsvar = lsymPN.head
                            if ( clauseSetToInstantiate._1._2.equals( clsvar ) ) nrepl
                            else if ( varsig.equals( clauseSetToInstantiate._1._2 ) ) nrepl.replace( curpos, varsig )
                            else nrepl
                          case None => nrepl
                        }
                      } )
                      else subform ) ) ) )
            } ) ) )
          //This code traverses the clause set and checks if the any of
          // the clauses contain clause set terms if they do, then we call
          //this method recursively on the those parts and attach the
          // resulting clause sets
          instantiatedClauses.foldLeft( Set[Sequent[Atom]]() )( ( vale, x ) => {
            //We construct this new clause set by folding the newly constructed clause
            //and the resulting clause sets by sequent concatenation
            vale ++ x.awayFrom[Atom]().composedSequents.foldLeft(
              if ( x.isUniformawayFrom[Atom]() ) Set[Sequent[Atom]]() else Set[Sequent[Atom]]( x.towards[Atom]() ) )( ( mixedClauseSet, y ) => {
                val CLSTerm( newTopSym, newCutConfig, args ) = y
                val mapOnConfigs = css.getOrElse( newTopSym, Map() )
                val theConfigNeeded = mapOnConfigs.keySet.foldLeft( newCutConfig )( ( thekey, cutconfigctk ) => if ( SequentInstanceOf( newCutConfig, cutconfigctk ) ) cutconfigctk else thekey )
                //After finding the configuration we need to put the correct inductive
                //step in order to properly construct the clause set.
                val ( _, ( Apps( _, vs: Seq[Expr] ), _ ), _ ) = PickCorrectInductiveCase( mapOnConfigs.getOrElse( theConfigNeeded, Set() ), args )
                //Here we construct the new substitution
                val zippedTogether = vs.zip( args ).map {
                  case ( one, two ) =>
                    //We know this is at most size one for nat
                    freeVariables( one ).map( x => one.find( x ) ).foldLeft( List[HOLPosition]() )( ( fin, ll ) => fin ++ ll ).headOption match {
                      case Some( pos ) => ( one.get( pos ).getOrElse( one ), two.get( pos ).getOrElse( two ) )
                      case None        => ( one, two )
                    }
                }
                //Here we join all of the variable term pairs and construct a subtitution
                val newsigma: Substitution = zippedTogether.foldLeft( Substitution() )( ( sub, pair ) =>
                  if ( freeVariables( pair._1 ).isEmpty ) sub else sub.compose( Substitution( pair._1.asInstanceOf[Var], pair._2 ) ) )
                //Now that we have the config and the substitution we can recursively call the lower
                //clause set
                val thelowerclauses = InstantiateClauseSetSchema( newTopSym, theConfigNeeded, css, newsigma, usedNames ++ regularClauseSetToInstantiate._1 )
                //after we construct the recursive clause sets we can attach them to the final clause set
                if ( mixedClauseSet.isEmpty ) thelowerclauses else if ( thelowerclauses.isEmpty ) mixedClauseSet
                else for ( c1 <- mixedClauseSet; c2 <- thelowerclauses ) yield ( c1 ++ c2 ).distinct
              } )
          } )
        }
      }
    }
  }

  //checks if S1 is an instance of S2
  object SequentInstanceOf {
    def apply( S1: HOLSequent, S2: HOLSequent ): Boolean =
      FormulaSetInstanceOf( S1.antecedent, S2.antecedent ) &&
        FormulaSetInstanceOf( S1.succedent, S2.succedent )

    def FormulaSetInstanceOf( SF1: Seq[Formula], SF2: Seq[Formula] ): Boolean =
      if ( SF1.size == SF2.size )
        SF1.foldLeft( true, SF2.toList.toSet )( ( isInstanceOf, F ) =>
          if ( !isInstanceOf._1 ) isInstanceOf
          else {
            val ( result, matchFormula ) = isInstanceOf._2.foldLeft( ( false, isInstanceOf._2.head ) )( ( isthere, SF ) =>
              if ( isthere._1 ) isthere
              else if ( FormulaInstanceOf( F, SF ) ) ( true, SF )
              else isthere )
            val newSetofFormula = if ( result ) isInstanceOf._2 - matchFormula else isInstanceOf._2
            ( result && isInstanceOf._1, newSetofFormula )
          } )._1
      else false

    def FormulaInstanceOf( F2: Formula, F1: Formula ): Boolean =
      LambdaPosition.differingPositions( F1, F2 ).foldLeft( true )( ( isOK, pos ) =>
        ( F1.get( pos ).getOrElse( F1 ), F2.get( pos ).getOrElse( F2 ) ) match {
          case ( Var( _, t ), Var( _, r ) )   => isOK && t.equals( r )
          case ( App( _, s ), Var( w, r ) )   => isOK && !s.contains( Var( w, r ) )
          case ( Const( _, t ), Var( _, r ) ) => isOK && t.equals( r )
          case ( _, _ )                       => isOK
        } )
  }

  //Picks which part of an inductive definition is needed at the moment
  //based on the set of arguments provided
  object PickCorrectInductiveCase {
    def apply(
      CSP:  Set[( ( Expr, Set[Var] ), Set[SequentComposition] )],
      args: Seq[Expr] ): ( Int, ( Expr, Set[Var] ), Set[SequentComposition] ) =
      CSP.foldLeft( ( 0, CSP.head._1, CSP.head._2 ) )( ( theCorrect, current ) => {
        val ( exVar, clauses ) = current
        val ( Apps( _, argsLink ), _ ) = exVar
        val ( oldCount, _, _ ) = theCorrect
        val totalCount = args.zip( argsLink ).foldLeft( 0 )( ( count, curPair ) =>
          if ( curPair._1.equals( curPair._2 ) ) count + 1
          else count )
        if ( totalCount > oldCount ) ( totalCount, current._1, clauses )
        else theCorrect
      } )
  }
}
