package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.{ProofDefinitions, ProofNames}
import at.logic.gapt.proofs.lk.{EigenVariablesLK, LKProof}
import at.logic.gapt.proofs.{Context, HOLClause, HOLSequent, Sequent, SetSequent}

//Idea behind the type is for each proof symbol we have a  Map,  which maps configurations to a set of sequents over atoms
//representing the clauses and the expression of the case of the inductive definition.
object SchematicClauseSet {
  def apply(
    topSym:     String,
    cutConfig:  HOLSequent                  = HOLSequent(),
    foundCases: Set[( String, HOLSequent )] = Set[( String, HOLSequent )]() )(implicit   ctx:Context):
    Option[Map[String, Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[HOLClause] )]]]] = {
    val proofNames = ctx.get[ProofDefinitions].components.keySet
    //If the set of proof names in the context does not contain topSym
    //then we cannot construct the clause set and return None.
    if ( proofNames.contains( topSym ) ) {
      //Otherwise we find the definition of the proof symbol
      val CurrentProofsCases = ctx.get[ProofDefinitions].components.getOrElse( topSym,Set())
      //Once we find the definition of the proof we construct the
      //Structs for the given proof modulo the provided cut
      //configuration
      val currentProofsStructs: Set[( ( Expr, Set[Var] ), Struct[Nothing] )] =
          CurrentProofsCases.map{ case ( placeHolder: Expr, assocProof: LKProof ) =>
          (( placeHolder, EigenVariablesLK( assocProof )),
          StructCreators.extract( assocProof, FindAncestors( assocProof.endSequent, cutConfig ))( _ => true, ctx  ) )}
      //After constructing the struct we need to find the dependencies associated
      // with the struct modulo the provided configuration.
      // The dependencies are the links to other proofs and self links
      val clauseSetDependencies = StructDependencies( topSym, cutConfig, currentProofsStructs, foundCases )
      // For each dependency we need to compute the clause set of that dependency by
      //recursively calling the SchematicClauseSet function.
      val dependencyClauseSets = clauseSetDependencies.map( x => {
        val inducSet = foundCases ++
          ( clauseSetDependencies - x ) +  ( topSym -> cutConfig )
        SchematicClauseSet( x._1, x._2, inducSet )(ctx).getOrElse(Map())
      } )
      //The resulting dependency need to be merge together to construct a larger
      //schematic clause set
      val dependencyClauseSetsMerged = MapMerger( dependencyClauseSets )
      //Finally we construct the map for the current struct
      val TopClauses: Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[HOLClause] )]] =
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
        val F1Pos = F1.get( pos ) match { case Some( x ) => x case None => F1 }
        val F2Pos = F2.get( pos ) match { case Some( x ) => x case None => F2 }
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
  object StructDependencies{
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
          if ( pf.matches( topSym ) && ccon.equals( cutConfig ) ) Set(( pf, ccon ))
          else y  ++  Set(( pf, ccon ))
        } )
        w ++ CLSyms
      } )
  }

  object MapMerger {
    def apply( M1: Set[Map[String, Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[HOLClause] )]]]] ): Map[String, Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[HOLClause] )]]] =
      M1.foldLeft( Map[String, Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[HOLClause] )]]]() )( ( x, y ) => {
        val themerge = mergeList( x, y )
        if ( themerge.keySet.nonEmpty ) themerge.keySet.map( w => ( w,  themerge.getOrElse( w,List()).foldLeft( Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[HOLClause] )]]() )( ( str, end ) => mergeSet( str, end )) )) toMap
        else x
      })

    def mergeList[K, V]( m1: Map[K, V], m2: Map[K, V] ): Map[K, List[V]] =
      if ( m1.keySet.nonEmpty && m2.keySet.nonEmpty )
        ( m1.keySet ++ m2.keySet ) map { i => i -> ( m1.get( i ).toList ::: m2.get( i ).toList ) } toMap
      else if ( m1.keySet.isEmpty && m2.keySet.nonEmpty )
        m2.keySet map { i => i -> m2.get( i ).toList } toMap

      else if ( m1.keySet.nonEmpty && m2.keySet.isEmpty )
        m1.keySet map { i => i -> m1.get( i ).toList } toMap
      else Map[K, List[V]]()

    def mergeSet[K, V]( m1: Map[K, Set[V]], m2: Map[K, Set[V]] ): Map[K, Set[V]] =
      Map() ++ (for (k <- m1.keySet ++ m2.keySet)
      yield k -> (m1.getOrElse(k, Set())++ m2.getOrElse(k, Set())) )


  }

  //Constructs clause sets modulo the cut configurations and proofs
  object CutConfigProofClauseSetMaps {
    def apply(
      cutConfig:     HOLSequent,
      currentStruct: Set[(( Expr, Set[Var] ),Struct[Nothing])] ): Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[HOLClause]) ]] =
      currentStruct.map{ case ((ex,sv),sn) => Map(cutConfig -> Set( ( (ex,sv), CharacteristicClauseSet( sn, cutConfig ) )  ))}.
      foldLeft( Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[HOLClause] )]]() )( ( aHOLIndexedMap, instance ) =>
      instance.keySet.foldLeft( Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[HOLClause] )]]() )((variationMap, sequentInstances ) =>
        if(aHOLIndexedMap.keySet.contains(sequentInstances) ) variationMap +( sequentInstances-> (instance.getOrElse(sequentInstances,Set()) ++ aHOLIndexedMap.getOrElse( sequentInstances,Set())  ))
        else variationMap + (sequentInstances -> instance.getOrElse( sequentInstances,Set()) )
      ))
  }

  def nat( i: Int, thevar: Var )( implicit ctx: Context ): Expr = {
    val suc = ctx.get[Context.Constants].constants.getOrElse( "s", Const( "0", Ti ) )
    if ( i > 0 ) Apps( suc, Seq( nat( i - 1, thevar ) ) )
    else thevar
  }

  object CleanClauseSet {
    def apply( precleaned: Map[String, Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[HOLClause] )]]] ): Map[String, Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[HOLClause] )]]] = {
      val result = precleaned.keySet.map( sym => {
        val ccb = precleaned.getOrElse( sym ,Map()).keySet.foldLeft( Set[HOLSequent]() )( ( goodOnes, posGood ) => {
              if ( goodOnes.isEmpty ) Set( posGood )
              else {
                val newGood = goodOnes.map( x => {
                  if ( SequentInstanceOf( posGood, x ) ||
                    SequentInstanceOf( x, posGood) )
                    SimplierOfSequents( x, posGood)
                  else x
                } )
                if ( !newGood.contains( posGood) &&
                  goodOnes.forall( x => {
                    !( SequentInstanceOf( posGood, x ) ||
                      SequentInstanceOf( x, posGood) )
                  } ) ) newGood +  posGood
                else newGood

              }
            } ).map( x => (x,precleaned.getOrElse( sym ,Map()).getOrElse( x, Set()))).
            foldLeft( Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[HOLClause] )]]() )( ( finmap, pairmap ) => finmap + ( pairmap._1-> pairmap._2 ))
        ( sym, ccb )
      } )

      result.foldLeft( Map[String, Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[HOLClause] )]]]() )( ( finmap, pairmap ) => finmap + ( pairmap._1-> pairmap._2 ))
    }
    object SimplierOfSequents {
      def apply( S1: HOLSequent, S2: HOLSequent ): HOLSequent = {
        val one = SimplierOfFormulaSets( S1.antecedent.toSet, S2.antecedent.toSet )
        val two = SimplierOfFormulaSets( S1.succedent.toSet, S2.succedent.toSet )
        S1
      }

      private def SimplierOfFormulaSets( SF1: Set[Formula], SF2: Set[Formula] ): Set[Formula] = {
        val pairsOfMatches: Set[( Formula, Option[Formula] )] = SF1.map( x => {
          val theone = SF2.find( y => SequentInstanceOf.FormulaInstanceOf( x, y ) )
          ( x, theone )
        } )
        val ( one, two ): ( Int, Int ) = pairsOfMatches.fold( ( 0, 0 ) )( ( soFar, cur ) => {
          val ( one, two ) = soFar
          val ( three, four: Option[Formula] ) = cur
          four match {
            case Some( form ) =>
              val ( one1: Int, two1: Int ) = simplierOfFormula( cur._1.asInstanceOf[Formula], form.asInstanceOf[Formula] )
              ( one.asInstanceOf[Int] + one1, two.asInstanceOf[Int] + two1 )
            case None => soFar.asInstanceOf[( Int, Int )]
          }
        } ).asInstanceOf[( Int, Int )]
        if ( two <= one ) SF1
        else SF2
      }

      def simplierOfFormula( F1: Formula, F2: Formula ): ( Int, Int ) = {
        val differences = LambdaPosition.differingPositions( F1, F2 )
        differences.fold( ( 0, 0 ) )( ( cur, next ) => {
          val ( one: Int, two: Int ) = cur
          val ex1 = F1.get( next.asInstanceOf[LambdaPosition] ) match {
            case Some( x ) => x
            case None      => Var( "", TBase( "nat" ) )
          }
          val ex2 = F2.get( next.asInstanceOf[LambdaPosition] ) match {
            case Some( x ) => x
            case None      => Var( "", TBase( "nat" ) )
          }
          if ( ex1.ty.eq( TBase( "nat" ) ) ) {
            if ( ex1.contains( ex2 ) && !ex2.contains( ex1 ) && ( one == 0 ) ) ( 0, 1 )
            else if ( ex1.contains( ex2 ) && !ex2.contains( ex1 ) && ( one == 1 ) ) ( 0, 0 )
            else if ( ex2.contains( ex1 ) && !ex1.contains( ex2 ) && ( two == 0 ) ) ( 1, 0 )
            else if ( ex2.contains( ex1 ) && !ex1.contains( ex2 ) && ( two == 1 ) ) ( 0, 0 )
            else ( one, two )
          } else ( one, two )
        } ).asInstanceOf[( Int, Int )]
      }

    }
  }
  object InstantiateClauseSetSchema {
    def apply(
      topSym:    String,
      cutConfig: HOLSequent,
      css:       Map[String, Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[HOLClause] )]]],
      sigma:     Substitution,
      usedNames: Set[Var]                                                                         = Set[Var]() )( implicit ctx: Context ): Set[Sequent[Atom]] = {
      //First we extract the clause set associated with the given proof name
      val starterClauseSet = ( css.get( topSym ) match {
        case Some( x ) => x
        case None      => Map[HOLSequent, Set[( ( Expr, Set[Var] ), Set[Sequent[Atom]] )]]()
      } ).get( cutConfig ) match {
        case Some( x ) => x
        case None      => Set[( ( Expr, Set[Var] ), Set[Sequent[Atom]] )]()
      }
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
        val optionClauseSets = starterClauseSet.fold( Set[( ( Expr, Set[Var] ), Set[Sequent[Atom]] )]() )( ( rightClauses, possibleclauses ) => {
          val ( exVar, _ ) = possibleclauses
          val ( ex: Expr, _ ) = exVar
          if ( sigma.domain.equals( freeVariables( ex ) ) ) {
            rightClauses.asInstanceOf[Set[( Expr, Set[Sequent[Atom]] )]] ++
              Set[( Expr, Set[Sequent[Atom]] )]( possibleclauses.asInstanceOf[( Expr, Set[Sequent[Atom]] )] )
          } else rightClauses
        } ).asInstanceOf[Set[( ( Expr, Set[Var] ), Set[Sequent[Atom]] )]]
        //This is a weird case when we have more than one stepcase or
        // no stepcase Not True when dealing with natural numbers.
        if ( optionClauseSets.size != 1 ) Set[Sequent[Atom]]()
        else {
          //Here we select the clause set associated with the provided
          //substitution. We decide which clause set is associated
          //by selecting the clause set with the greatest difference
          //after substitution
          val preClauseSetToInstantiate = optionClauseSets.fold( Set[( ( Int, Var ), ( Set[Var], Set[Sequent[Atom]] ) )]() )( ( reEx, excl ) => {
            val ( exVar, cl: Set[Sequent[Atom]] ) = excl
            val ( ex: Expr, varS: Set[Var] ) = exVar
            val Apps( _, lSym ) = ex
            val headVar = if ( freeVariables( lSym.head ).size == 1 ) freeVariables( lSym.head ).head else Var( "", TBase( "nat" ) )
            val listdiff = LambdaPosition.differingPositions( ex, sigma( ex ) )
            reEx.asInstanceOf[Set[( ( Int, Var ), ( Set[Var], Set[Sequent[Atom]] ) )]] ++ Set[( ( Int, Var ), ( Set[Var], Set[Sequent[Atom]] ) )]( ( ( listdiff.size, headVar ), ( varS, cl ) ) )
          } ).asInstanceOf[Set[( ( Int, Var ), ( Set[Var], Set[Sequent[Atom]] ) )]]
          val clauseSetToInstantiate = preClauseSetToInstantiate.fold( ( ( 0, Var( "", TBase( "nat" ) ) ), ( Set[Var](), Set[Sequent[Atom]]() ) ) )( ( cll, excl ) => {
            val ( ( size: Int, _ ), ( _, _ ) ) = excl
            val ( ( curSize: Int, _ ), ( _, _ ) ) = cll
            if ( curSize < size ) excl
            else cll
          } )

          //The following code regularizes the clause set with respect to
          //the already used eigenvariables. Regularization of schematic
          //clause sets is an issue because variables which occur once in the
          // proof schema might occur at different levels in the instantiated
          //proof
          val regularClauseSetToInstantiate =
            if ( usedNames.nonEmpty ) {
              val renamer = rename.awayFrom( usedNames )
              usedNames.fold( ( usedNames, clauseSetToInstantiate._2._2 ) )( ( reClause, nameVar ) => {
                val Var( s, t ) = nameVar
                val renamedval = Var( renamer.fresh( s ), t )
                val ( varsUsed: Set[Var], clausesSet: Set[Sequent[Atom]] ) = reClause
                val varsUsedUpdate = varsUsed ++ Set( renamedval )
                val regclause: Set[Sequent[Atom]] = clausesSet.map( x => {
                  val newAnte = x.antecedent.map( f => {
                    val listofpos = f.find( nameVar.asInstanceOf[Expr] )
                    if ( listofpos.nonEmpty ) {
                      listofpos.fold( f )( ( ff, pos ) => {
                        ff.asInstanceOf[Formula].replace( pos.asInstanceOf[HOLPosition], renamedval )
                      } ).asInstanceOf[Formula]
                    } else f
                  } )
                  val newSuc = x.succedent.map( f => {
                    val listofpos = f.find( nameVar.asInstanceOf[Expr] )
                    if ( listofpos.nonEmpty ) {
                      listofpos.fold( f )( ( ff, pos ) => {
                        ff.asInstanceOf[Formula].replace( pos.asInstanceOf[HOLPosition], renamedval )
                      } ).asInstanceOf[Formula]
                    } else f
                  } )
                  Sequent( newAnte, newSuc ).asInstanceOf[Sequent[Atom]]
                } )
                ( varsUsedUpdate, regclause )
              } ).asInstanceOf[( Set[Var], Set[Sequent[Atom]] )]
            } else clauseSetToInstantiate._2
          //Here we instantiate the clause set we selected
          //based on the regularization
          val instantiatedClauses: Set[Sequent[Atom]] = regularClauseSetToInstantiate._2.map( x => {
            val HOLSequent( ante, suc ) = x
            val newAnte = ante.map( form => {
              sigma.domain.fold( form )( ( subform, varsig ) => {
                val positions: List[HOLPosition] =
                  if ( varsig.ty.equals( TBase( "nat" ) ) )
                    subform.find( nat( 1, varsig.asInstanceOf[Var] )( ctx ) )
                  else subform.find( varsig.asInstanceOf[Var] )
                positions.fold( subform )( ( nrepl, curpos ) => {
                  nrepl.asInstanceOf[Formula].replace( curpos.asInstanceOf[HOLPosition], varsig )
                } ).asInstanceOf[Formula]
              } )
            } )
            val newSuc = suc.map( form => {
              sigma.domain.fold( form )( ( subform, varsig ) => {
                if ( varsig.ty.equals( TBase( "nat" ) ) ) {
                  val positions: List[HOLPosition] = subform.find( nat( 1, varsig.asInstanceOf[Var] )( ctx ) )
                  positions.fold( subform )( ( nrepl, curpos ) => {
                    if ( subform.contains( Const( "⊢", To ) ) ) {
                      val Atom( _, lArgs ) = subform
                      val Const( pName, _ ) = lArgs.head
                      ctx.get[ProofNames].names.get( pName ) match {
                        case Some( proofName ) =>
                          val Apps( _, lsymPN ) = proofName._1
                          val clsvar = lsymPN.head
                          if ( clauseSetToInstantiate._1._2.equals( clsvar ) ) nrepl
                          else if ( varsig.equals( clauseSetToInstantiate._1._2 ) ) nrepl.asInstanceOf[Formula].replace( curpos.asInstanceOf[HOLPosition], varsig )
                          else nrepl
                        case None => nrepl
                      }
                    } else nrepl.asInstanceOf[Formula].replace( curpos.asInstanceOf[HOLPosition], varsig )
                  } ).asInstanceOf[Formula]
                } else subform
              } )
            } )
            sigma( HOLSequent( newAnte, newSuc ) ).asInstanceOf[Sequent[Atom]]
          } )
          //This code traverses the clause set and checks if the any of
          // the clauses contain clause set terms if they do, then we call
          //this method recursively on the those parts and attach the
          // resulting clause sets
          val finalres = instantiatedClauses.fold( Set[SetSequent[Atom]]() )( ( vale, x ) => {
            //We can attept to split each clause into the clause set symbols
            //and the none clause set symbols
            val ( newSuccSeq, cLSSyms ) = SequentSplitter( x.asInstanceOf[Sequent[Atom]] )
            //After splitting we can construct a new clause without clause set symbols
            val newSequent = Sequent( x.asInstanceOf[Sequent[Atom]].antecedent, newSuccSeq )
            //If there are no clause set symbols we are done.
            //otherwise we have to construct the clause sets for
            //each symbol
            if ( cLSSyms.isEmpty ) vale.asInstanceOf[Set[Sequent[Atom]]] ++ Set( x )
            else {
              //We construct this new clause set by folding the newly constructed clause
              //and the resulting clause sets by sequent concatenation
              val baseOfFold = if ( newSequent.antecedent.isEmpty && newSequent.isEmpty )
                Set[Sequent[Atom]]()
              else Set[Sequent[Atom]]( newSequent )
              val finalCS = cLSSyms.fold( baseOfFold )( ( mixedClauseSet, y ) => {
                val Apps( _, info ) = y

                val Const( newTopSym, _ ) = info.head

                //Clause terms are constructed by adding auxiliary information
                //to an atomic formula. We extract this information using the following
                //method
                val ( _, ante, _, suc, _, args ) = ClauseTermReader( info.tail )
                //Saved within this clause set term is a cut configuration
                //which we must abstract and generalize in order to find the
                //proper clause set in the schematic clause set map.
                val newCutConfig = HOLSequent( ante, suc )
                val mapOnConfigs = css.getOrElse( newTopSym,Map() )
                val theConfigNeeded = mapOnConfigs.keySet.foldLeft( newCutConfig )( ( thekey, cutconfigctk ) => if ( SequentInstanceOf( newCutConfig, cutconfigctk ) ) cutconfigctk else thekey )

                //After finding the configuration we need to put the correct inductive
                //step in order to properly construct the clause set.
                val ( _, ( exprForMatch, _ ), _ ) = PickCorrectInductiveCase( mapOnConfigs.getOrElse(theConfigNeeded,Set()), args )

                //The final step towards building the clause set is constructing the necessary
                //substitution
                val Apps( _, vs: Seq[Expr] ) = exprForMatch

                //Here we construct the new substitution
                val zippedTogether = vs.zip( args ).map{ case ( one, two ) =>
                    //We know this is at most size one for nat
                   freeVariables( one ).map( x => one.find( x ) ).foldLeft( List[HOLPosition]() )( ( fin, ll ) => fin ++ ll ).headOption match {
                     case Some(pos) => ( one.get( pos ).getOrElse(one), two.get( pos ).getOrElse(two) )
                     case None => ( one, two )
                   }
                }
                //Here we join all of the variable term pairs and construct a subtitution
                val newsigma: Substitution = zippedTogether.fold( Substitution() )( ( sub, pair ) => {
                  val ( one: Expr, two: Expr ) = pair
                  if ( freeVariables( one ).isEmpty ) sub
                  else sub.asInstanceOf[Substitution].compose( Substitution( one.asInstanceOf[Var], two ) )
                } ).asInstanceOf[Substitution]
                //Now that we have the config and the substitution we can recursively call the lower
                //clause set
                val thelowerclauses = InstantiateClauseSetSchema( newTopSym, theConfigNeeded, css, newsigma, usedNames ++ regularClauseSetToInstantiate._1 )
                //after we construct the recursive clause sets we can attach them to the final clause set
                val ender = ComposeClauseSets( mixedClauseSet.asInstanceOf[Set[Sequent[Atom]]], thelowerclauses )
                ender
              } ).asInstanceOf[Set[Sequent[Atom]]]

              vale.asInstanceOf[Set[Sequent[Atom]]] ++ finalCS
            }
          } ).asInstanceOf[Set[Sequent[Atom]]]
          finalres
        }
      }
    }
  }
  //This object seperates the clause set symbols from the atoms of the given sequent
  object SequentSplitter {
    def apply[V]( theSequent: Sequent[V] ): ( Set[V], Set[V] ) = theSequent.succedent.fold( ( Set[Atom](), Set[Atom]() ) )( ( clset, y ) => {
      val ( seqNotCL, seqInCL ) = clset
      y match {
        case Apps( Const( "CL", _ ), _ ) => ( seqNotCL.asInstanceOf[Set[V]],
          seqInCL.asInstanceOf[Set[V]] ++ Set[V]( y.asInstanceOf[V] ) )
        case _ => ( seqNotCL.asInstanceOf[Set[V]] ++ Set[V]( y.asInstanceOf[V] ),
          seqInCL.asInstanceOf[Set[V]] )
      }
    } ).asInstanceOf[( Set[V], Set[V] )]
  }
  //This object is specifically designed to read clause set terms
  //which are constructed from proofs during struct construction
  object ClauseTermReader {
    def apply( input: Seq[Expr] ): ( Set[Const], Seq[Formula], Set[Const], Seq[Formula], Set[Const], Seq[Expr] ) =
      input.foldLeft( ( Set[Const](), Seq[Formula](), Set[Const](), Seq[Formula](), Set[Const](), Seq[Expr]() ) )( ( bigCollect, w ) => {
        val ( one, two, three, four, five, six ) = bigCollect
        if ( one.isEmpty && ( w match { case Const( "|", _ ) => true case _ => false } ) )
          ( Set[Const]( w.asInstanceOf[Const] ), two, three, four, five, six )
        else if ( one.nonEmpty && three.isEmpty && ( w match { case Const( "⊢", _ ) => true case _ => false } ) )
          ( one, two, Set[Const]( w.asInstanceOf[Const] ), four, five, six )
        else if ( one.nonEmpty && three.isEmpty )
          ( one, two.asInstanceOf[Seq[Formula]] ++ Seq[Formula]( w.asInstanceOf[Formula] ), three, four, five, six )
        else if ( one.nonEmpty && three.nonEmpty && five.isEmpty && ( w match { case Const( "|", _ ) => true case _ => false } ) )
          ( one, two, three, four, Set[Const]( w.asInstanceOf[Const] ), six )
        else if ( one.nonEmpty && three.nonEmpty && five.isEmpty )
          ( one, two, three, four.asInstanceOf[Seq[Formula]] ++ Seq[Formula]( w.asInstanceOf[Formula] ), five, six )
        else if ( one.nonEmpty && three.nonEmpty && five.nonEmpty )
          ( one, two, three, four, five, six.asInstanceOf[Seq[Expr]] ++ Seq[Expr]( w ) )
        else bigCollect
      } )
  }

  //checks if S1 is an instance of S2
  //TODO subsumption?
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

    def FormulaInstanceOf( F1: Formula, F2: Formula ): Boolean = {
      val listOfDiff = LambdaPosition.differingPositions( F1, F2 )
      listOfDiff.foldLeft( true )( ( isOK, pos ) => {
        val F1Pos = F1.get( pos ) match { case Some( x ) => x case None => F1 }
        val F2Pos = F2.get( pos ) match { case Some( x ) => x case None => F2 }
        ( F1Pos, F2Pos ) match {
          case ( Var( _, t ), Var( _, r ) )   => isOK && t.equals( r )
          case ( App( _, s ), Var( w, r ) )   => isOK && !s.contains( Var( w, r ) )
          case ( Const( _, t ), Var( _, r ) ) => isOK && t.equals( r )
          case ( _, _ )                       => isOK
        }
      } )
    }
  }
  //Picks which part of an inductive definition is needed at the moment
  //based on the set of arguments provided
  object PickCorrectInductiveCase {
    def apply(
      CSP:  Set[( ( Expr, Set[Var] ), Set[HOLClause] )],
      args: Seq[Expr] ): ( Int, ( Expr, Set[Var] ), Set[HOLClause] ) = { //TODO why a set
      CSP.foldLeft( ( 0, CSP.head._1, CSP.head._2 ) )( ( theCorrect, current ) => {
        val ( exVar, clauses ) = current
        val ( Apps( _, argsLink ), _ ) = exVar
        val ( oldcount, _, _ ) = theCorrect
        val totalcount = args.zip( argsLink ).fold( 0 )( ( count, curPair ) => {
          val ( one, two ) = curPair
          if ( one.equals( two ) ) count.asInstanceOf[Int] + 1
          else count
        } ).asInstanceOf[Int]
        if ( totalcount > oldcount ) ( totalcount, current._1, clauses )
        else theCorrect
      } )
    }
  }
  //Takes two clause sets and composes them clause by clause without duplication
  object ComposeClauseSets {
    def apply(C1: Set[Sequent[Atom]], C2: Set[Sequent[Atom]]): Set[Sequent[Atom]] =
      if (C1.isEmpty) C2
      else if (C2.isEmpty) C1
      else for (c1 <- C1; c2 <- C2) yield (c1 ++ c2).distinct
  }

}
