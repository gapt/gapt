package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.ProofDefinitions
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.{ Context, HOLSequent, Sequent, SetSequent }

//Idea behind the type is for each proof symbol we have a  Map,  which maps configurations to a set of sequents over atoms
//representing the clauses and the expression of the case of the inductive definition.
object SchematicClauseSet {
  def apply(
    topSym:     String,
    ctx:        Context,
    cutConfig:  HOLSequent                  = HOLSequent(),
    foundCases: Set[( String, HOLSequent )] = Set[( String, HOLSequent )]() ): Option[Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]] = {
    val proofNames = ctx.get[ProofDefinitions].components.keySet
    //If the set of proof names in the context does not contain topSym
    //then we cannot construct the clause set and return None.
    if ( proofNames.contains( topSym ) ) {
      //Otherwise we find the definition of the proof symbol
      val CurrentProofsCases =
        ctx.get[ProofDefinitions].components.get( topSym ) match {
          case Some( proofCasePair ) => proofCasePair
          case None                  => Set[( Expr, LKProof )]()
        }
      //Once we find the definition of the proof we construct the
      //Structs for the given proof modulo the provided cut
      //configuration
      val currentProofsStructs: Set[( Expr, Struct[Nothing] )] =
        CurrentProofsCases.map( x => {
          val ( placeHolder: Expr, assocProof: LKProof ) = x

          val ancestorPositions = FindAncestors( assocProof.endSequent, cutConfig )
          ( placeHolder, StructCreators.extract( assocProof, ancestorPositions, ctx )( _ => true ) )
        } )

      //After constructing the struct we need to find the dependencies associated
      // with the struct modulo the provided configuration.
      // The dependencies are the links to other proofs and self links
      val clauseSetDependencies = StructDependences( topSym, cutConfig, currentProofsStructs, foundCases )
      // For each dependency we need to compute the clause set of that dependency by
      //recursively calling the SchematicClauseSet function.
      val dependencyClauseSets = clauseSetDependencies.map( x => {
        val inducSet = foundCases ++
          ( clauseSetDependencies - x ) ++
          Set[( String, HOLSequent )]( ( topSym, cutConfig ) )
        SchematicClauseSet( x._1, ctx, x._2, inducSet ) match {
          case Some( cs ) => cs
          case None =>
            Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]()
        }
      } )
      //The resulting dependency need to be merge together to construct a larger
      //schematic clause set
      val dependencyClauseSetsMerged = MapMerger( dependencyClauseSets )
      //Finally we construct the map for the current struct
      val TopClauses: Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]] =
        CutConfigProofClauseSetMaps( cutConfig, currentProofsStructs )
      //we merge the constructed map with all the dependencies
      Some( MapMerger( Set( dependencyClauseSetsMerged ) ++ Set( Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]( ( topSym, TopClauses ) ) ) ) )
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
          case ( Var( _, _ ), _ ) => isOK && F1Pos.ty.equals( F2Pos.ty )
          case ( App( c, s: List[Expr] ), App( d, t: List[Expr] ) ) => isOK && c.equals( d ) && s.zip( t ).forall( th => ancestorInstanceOf( th._1, th._2 ) )
          case ( App( _, _ ), Var( _, _ ) ) => isOK && F1Pos.ty.equals( F2Pos.ty )
          case ( Const( _, _ ), Var( _, _ ) ) => isOK && F1Pos.ty.equals( F2Pos.ty )
          case _ => false
        }
      } )
      finality
    }
  }
  //Finds the proof links within the given struct
  object StructDependences {
    def apply(
      topSym:        String,
      cutConfig:     HOLSequent,
      currentStruct: Set[( Expr, Struct[Nothing] )],
      foundCases:    Set[( String, HOLSequent )] ): Set[( String, HOLSequent )] =
      currentStruct.fold( Set[( String, HOLSequent )]() )( ( w, e ) => {
        val temp: Set[Struct[Nothing]] = SchematicLeafs( e.asInstanceOf[( Expr, Struct[Nothing] )]._2 ).fold( Set[Struct[Nothing]]() )( ( g, pb ) => {
          val CLS( pf, ccon, _, _ ) = pb
          if ( foundCases.contains( ( pf, ccon ) ) ) g
          else g.asInstanceOf[Set[Struct[Nothing]]] ++ Set[Struct[Nothing]]( pb.asInstanceOf[Struct[Nothing]] )
        } ).asInstanceOf[Set[Struct[Nothing]]]
        val CLSyms: Set[( String, HOLSequent )] = temp.fold( Set[( String, HOLSequent )]() )( ( y, a ) => {
          val CLS( pf, ccon, _, _ ) = a
          if ( pf.matches( topSym ) && ccon.equals( cutConfig ) ) Set[( String, HOLSequent )]( ( pf, ccon ) )
          else y.asInstanceOf[Set[( String, HOLSequent )]] ++ Set[( String, HOLSequent )]( ( pf, ccon ) )
        } ).asInstanceOf[Set[( String, HOLSequent )]]
        w.asInstanceOf[Set[( String, HOLSequent )]] ++ CLSyms
      } ).asInstanceOf[Set[( String, HOLSequent )]]
  }

  object MapMerger {
    def apply( M1: Set[Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]] ): Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]] = M1.fold( Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]() )( ( x, y ) => {
      val themerge = mergeList( x, y )
      if ( themerge.keySet.nonEmpty )
        themerge.keySet.map( w => {
          val thing = themerge.get( w ) match {
            case Some( mapp ) => mapp
            case None         => List[Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]()
          }
          ( w, thing.foldLeft( Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]() )( ( str, end ) => {
            mergeSet( str, end )
          } ) )
        } ) toMap
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
      if ( m1.keySet.nonEmpty && m2.keySet.nonEmpty )
        ( m1.keySet ++ m2.keySet ) map { i =>
          i -> {
            val one = m1.get( i ) match {
              case Some( www ) => www
              case None        => Set[V]()
            }
            val two = m2.get( i ) match {
              case Some( www ) => www
              case None        => Set[V]()
            }
            one ++ two
          }
        } toMap
      else if ( m1.keySet.isEmpty && m2.keySet.nonEmpty )
        m2
      else if ( m1.keySet.nonEmpty && m2.keySet.isEmpty )
        m1
      else Map[K, Set[V]]()
  }

  //Constructs clause sets modulo the cut configurations and proofs
  object CutConfigProofClauseSetMaps {
    def apply(
      cutConfig:     HOLSequent,
      currentStruct: Set[( Expr, Struct[Nothing] )] ): Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]] = currentStruct.map( x => {
      val theClauseSet = CharacteristicClauseSet( x._2, cutConfig ).asInstanceOf[Set[SetSequent[Atom]]]
      val clauseSetNameVarsMatch = Set[( Expr, Set[SetSequent[Atom]] )]( ( x._1, theClauseSet ) )

      Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]( ( cutConfig, clauseSetNameVarsMatch ) )
    } ).fold( Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]() )( ( aHOLIndexedMap, instance ) => {
      instance.keySet.fold( Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]() )( ( variationMap, sequentInstances ) => {
        if ( aHOLIndexedMap.keySet.contains( sequentInstances.asInstanceOf[HOLSequent] ) ) {
          val thevalinw = instance.get( sequentInstances.asInstanceOf[HOLSequent] ) match {
            case Some( x ) => x
            case None      => Set[( Expr, Set[SetSequent[Atom]] )]()
          }
          val placeVariationsInMap = aHOLIndexedMap.get( sequentInstances.asInstanceOf[HOLSequent] ) match {
            case Some( x ) => x
            case None      => Set[( Expr, Set[SetSequent[Atom]] )]()
          }
          variationMap.asInstanceOf[Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]] ++
            Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]( ( sequentInstances.asInstanceOf[HOLSequent], thevalinw ++ placeVariationsInMap ) )
        } else {
          val placeInstancesInMap = instance.get( sequentInstances.asInstanceOf[HOLSequent] ) match {
            case Some( x ) => x
            case None      => Set[( Expr, Set[SetSequent[Atom]] )]()
          }
          variationMap.asInstanceOf[Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]] ++
            Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]( ( sequentInstances.asInstanceOf[HOLSequent], placeInstancesInMap ) )
        }

      } ).asInstanceOf[Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]
    } )
  }

  def nat( i: Int, thevar: Var )( implicit ctx: Context ): Expr = {
    val suc = ctx.get[Context.Constants].constants.getOrElse( "s", Const( "0", Ti ) )
    if ( i > 0 ) Apps( suc, Seq( nat( i - 1, thevar ) ) )
    else thevar
  }

  object InstantiateClauseSetSchema {
    def apply(
      topSym:    String,
      cutConfig: HOLSequent,
      css:       Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]],
      sigma:     Substitution )( implicit ctx: Context ): Set[Sequent[Atom]] = {
      //First we extract the clause set associated with the given proof name
      val starterClauseSet = ( css.get( topSym ) match {
        case Some( x ) => x
        case None      => Map[HOLSequent, Set[( Expr, Set[Sequent[Atom]] )]]()
      } ).get( cutConfig ) match {
        case Some( x ) => x
        case None      => Set[( Expr, Set[Sequent[Atom]] )]()
      }
      //we check if the starter clause set is empty or does not have
      //any free variables in common with the domain of sigma.
      //When this occurs we return an empty clause set.
      if ( starterClauseSet.isEmpty ||
        !starterClauseSet.exists( x => {
          sigma.domain.equals( freeVariables( x._1 ) )
        } ) )
        Set[Sequent[Atom]]()
      else {
        //Here we are looked for the clause set specifically
        //associated with the domain of sigma.
        val optionClauseSets = starterClauseSet.fold( Set[( Expr, Set[Sequent[Atom]] )]() )( ( rightClauses, possibleclauses ) => {
          val ( ex: Expr, _ ) = possibleclauses
          if ( sigma.domain.equals( freeVariables( ex ) ) ) {
            val Apps( at.logic.gapt.expr.Const( _, _ ), _ ) = ex // we are assuming natural numbers here
            rightClauses.asInstanceOf[Set[( Expr, Set[Sequent[Atom]] )]] ++
              Set[( Expr, Set[Sequent[Atom]] )]( possibleclauses.asInstanceOf[( Expr, Set[Sequent[Atom]] )] )
          } else rightClauses
        } ).asInstanceOf[Set[( Expr, Set[Sequent[Atom]] )]]
        //This is a weird case when we have more than one stepcase or
        // no stepcase Not True when dealing with natural numbers.
        if ( optionClauseSets.size != 1 ) Set[Sequent[Atom]]()
        else {
          //Here we select the clause set associated with the provided
          //substitution. We decide which clause set is associated
          //by selecting the clause set with the greatest difference
          //after substitution
          val clauseSetToInstantiate = optionClauseSets.fold( Set[( Int, Set[Sequent[Atom]] )]() )( ( reEx, excl ) => {
            val ( ex: Expr, cl ) = excl
            val listdiff = LambdaPosition.differingPositions( ex, sigma( ex ) )
            reEx.asInstanceOf[Set[( Int, Set[Sequent[Atom]] )]] ++ Set[( Int, Set[Sequent[Atom]] )]( ( listdiff.size, cl.asInstanceOf[Set[Sequent[Atom]]] ) )
          } ).asInstanceOf[Set[( Int, Set[Sequent[Atom]] )]].fold( ( 0, Set[Sequent[Atom]]() ) )( ( cll, excl ) => {
            val ( size: Int, _ ) = excl
            val ( curSize: Int, _ ) = cll
            if ( curSize < size ) excl
            else cll
          } )

          //Here we instatiate the clause set we selected
          val instantiatedClauses: Set[Sequent[Atom]] = clauseSetToInstantiate._2.map( x => {
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
                    if ( subform.contains( Const( "⊢", To ) ) ) nrepl
                    else nrepl.asInstanceOf[Formula].replace( curpos.asInstanceOf[HOLPosition], varsig )
                  } ).asInstanceOf[Formula]
                } else subform
              } )
            } )
            sigma( HOLSequent( newAnte, newSuc ) ).asInstanceOf[Sequent[Atom]]
          } )
          //This code traverses the clause set and checks if the any of
          // the clause contain clause set terms if they do, then we call
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
                val mapOnConfigs = css.get( newTopSym ) match {
                  case Some( holseq ) => holseq
                  case None           => Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]()
                }
                val theConfigNeeded = mapOnConfigs.keySet.foldLeft( newCutConfig )( ( thekey, cutconfigctk ) => if ( SequentInstanceOf( newCutConfig, cutconfigctk ) ) cutconfigctk else thekey )

                val theNewClauseSetPair = mapOnConfigs.get( theConfigNeeded ) match {
                  case Some( holseq ) => holseq
                  case None           => Set[( Expr, Set[SetSequent[Atom]] )]()
                }
                //After finding the configuration we need to put the correct inductive
                //step in order to properly construct the clause set.
                val ( _, exprForMatch, _ ) = PickCorrectInductiveCase( theNewClauseSetPair, args )

                //The final step towards building the clause set is constructing the necessary
                //substitution
                val subArgs = args.map( x => sigma( x ) )
                val Apps( _, vs: Seq[Expr] ) = exprForMatch

                //Here we construct the new substitution
                val zippedTogether = vs.zip( subArgs ).map( x => {
                  val ( one, two ) = x
                  val thevars = freeVariables( one ) //We know this is at most size one for nat
                  if ( thevars.nonEmpty ) {
                    val clean: List[HOLPosition] = thevars.map( x => one.find( x ) ).fold( List[HOLPosition]() )( ( fin, ll ) =>
                      fin ++ ll )
                    //We are removing the outer most sucessor symbol here.
                    val left: Expr = one.get( clean.head ) match {
                      case Some( w ) => w
                      case None      => one
                    }
                    val right: Expr = two.get( clean.head ) match {
                      case Some( w ) => w
                      case None      => two
                    }
                    ( left, right )
                  } else x
                } )
                //Here we join all of the variable term pairs and construct a subtitution
                val newsigma: Substitution = zippedTogether.fold( Substitution() )( ( sub, pair ) => {
                  val ( one: Expr, two: Expr ) = pair
                  if ( freeVariables( one ).isEmpty ) sub
                  else sub.asInstanceOf[Substitution].compose( Substitution( one.asInstanceOf[Var], two ) )
                } ).asInstanceOf[Substitution]
                //Now that we have the config and the substitution we can recursively call the lower
                //clause set

                val thelowerclauses = InstantiateClauseSetSchema( newTopSym, theConfigNeeded, css, newsigma )
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
    def apply( input: Seq[Expr] ): ( Set[Const], Set[Formula], Set[Const], Set[Formula], Set[Const], Set[Expr] ) =
      input.foldLeft( ( Set[Const](), Set[Formula](), Set[Const](), Set[Formula](), Set[Const](), Set[Expr]() ) )( ( bigCollect, w ) => {
        val ( one, two, three, four, five, six ) = bigCollect
        if ( one.isEmpty && ( w match { case Const( "|", _ ) => true case _ => false } ) )
          ( Set[Const]( w.asInstanceOf[Const] ), two, three, four, five, six )
        else if ( one.nonEmpty && three.isEmpty && ( w match { case Const( "⊢", _ ) => true case _ => false } ) )
          ( one, two, Set[Const]( w.asInstanceOf[Const] ), four, five, six )
        else if ( one.nonEmpty && three.isEmpty )
          ( one, two.asInstanceOf[Set[Formula]] ++ Set[Formula]( w.asInstanceOf[Formula] ), three, four, five, six )
        else if ( one.nonEmpty && three.nonEmpty && five.isEmpty && ( w match { case Const( "|", _ ) => true case _ => false } ) )
          ( one, two, three, four, Set[Const]( w.asInstanceOf[Const] ), six )
        else if ( one.nonEmpty && three.nonEmpty && five.isEmpty )
          ( one, two, three, four.asInstanceOf[Set[Formula]] ++ Set[Formula]( w.asInstanceOf[Formula] ), five, six )
        else if ( one.nonEmpty && three.nonEmpty && five.nonEmpty )
          ( one, two, three, four, five, six.asInstanceOf[Set[Expr]] ++ Set[Expr]( w ) )
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
              else if ( FormulaSetInstanceOf( F, SF ) ) ( true, SF )
              else isthere )
            val newSetofFormula = if ( result ) isInstanceOf._2 - matchFormula else isInstanceOf._2
            ( result && isInstanceOf._1, newSetofFormula )
          } )._1
      else false

    def FormulaSetInstanceOf( F1: Formula, F2: Formula ): Boolean = {
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
      CSP:  Set[( Expr, Set[SetSequent[Atom]] )],
      args: Set[Expr] ): ( Int, Expr, Set[SetSequent[Atom]] ) = //TODO why a set
      CSP.foldLeft( ( 0, CSP.head._1, CSP.head._2 ) )( ( theCorrect, current ) => {
        val ( Apps( _, argsLink ), clauses ) = current
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
  //Takes two clause sets and composes them clause by clause without duplication
  object ComposeClauseSets {
    def apply(
      C1: Set[Sequent[Atom]],
      C2: Set[Sequent[Atom]] ): Set[Sequent[Atom]] = {
      val Cout: ( Set[Sequent[Atom]], Set[Sequent[Atom]] ) = if ( C1.size > C2.size ) ( C1, C2 ) else ( C2, C1 )
      val newclauses = Cout._1.map( x =>
        if ( Cout._2.nonEmpty ) Cout._2.map( y => sequentCompose( x, y ) )
        else Cout._1 )
      if ( newclauses.nonEmpty )
        newclauses.tail.fold( newclauses.head )( ( x, y ) => x ++ y )
      else Set()
    }
    //This is a compose function made specifically for composing schematic clauses during clause set construction
    def sequentCompose( S1: Sequent[Atom], S2: Sequent[Atom] ): Sequent[Atom] =
      Sequent[Atom]( S1.antecedent.distinct ++ S2.antecedent.distinct, S1.succedent.distinct ++ S2.succedent.distinct )
  }

}
