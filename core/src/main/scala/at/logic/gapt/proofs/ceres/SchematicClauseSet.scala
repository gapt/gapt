package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.expr.{ Apps, Expr, Formula, _ }
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
    val ProofNames = ctx.get[ProofDefinitions].components.keySet
    if ( ProofNames.contains( topSym ) ) {
      val TopProofs = ctx.get[ProofDefinitions].components.get( topSym ) match {
        case Some( w ) => w
        case None      => Set[( Expr, LKProof )]()
      }
      val topStructs: Set[( Expr, Struct[Nothing] )] = TopProofs.map( x => {
        val ( one: Expr, two: LKProof ) = x
        ( one, StructCreators.extract( two, ProofNames ) )
      } )
      val TopDependents = StructDependences( topSym, cutConfig, topStructs, foundCases )
      val DependentMaps = TopDependents.map( x => {
        val inducSet = foundCases ++ ( TopDependents - x ) ++ Set[( String, HOLSequent )]( ( topSym, cutConfig ) )
        SchematicClauseSet( x._1, ctx, x._2, inducSet ) match {
          case Some( cs ) => cs
          case None       => Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]()
        }
      } )
      val DM = DependentMaps.fold( Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]() )( ( x, y ) => { x ++ y } )
      val TopClauses: Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]] = CutConfigProofClauseSetMaps( cutConfig, topStructs )
      Some( DM ++ Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]( ( topSym, TopClauses ) ) )
    } else None
  }
  def InstantiateClauseSetSchema(
    topSym:    String,
    cutConfig: HOLSequent,
    css:       Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]],
    sigma:     Substitution ): Set[SetSequent[Atom]] = {
    val starterClauseSet = ( css.get( topSym ) match {
      case Some( x ) => x
      case None      => Map[HOLSequent, Set[( Expr, Set[Sequent[Atom]] )]]()
    } ).get( cutConfig ) match {
      case Some( x ) => x
      case None      => Set[( Expr, Set[Sequent[Atom]] )]()
    }
    if ( starterClauseSet.isEmpty || !starterClauseSet.exists( x => {
      val ( ex, _ ) = x
      sigma.domain.equals( freeVariables( ex ) )
    } ) )
      Set[SetSequent[Atom]]()
    else {
      val optionClauseSets = starterClauseSet.fold( Set[( Expr, Set[Sequent[Atom]] )]() )( ( vale, x ) => {
        val ( ex: Expr, _ ) = x
        if ( sigma.domain.equals( freeVariables( ex ) ) ) {
          val Apps( at.logic.gapt.expr.Const( _, _ ), listofterms ) = ex
          vale.asInstanceOf[Set[( Expr, Set[Sequent[Atom]] )]] ++
            Set[( Expr, Set[Sequent[Atom]] )]( x.asInstanceOf[( Expr, Set[Sequent[Atom]] )] )
        } else vale
      } ).asInstanceOf[Set[( Expr, Set[Sequent[Atom]] )]]
      if ( optionClauseSets.size != 1 ) Set[SetSequent[Atom]]()
      else {
        val instantiatedClauses = optionClauseSets.head._2.map( x => SetSequent[Atom]( sigma( x ).asInstanceOf[Sequent[Atom]] ) )
        //This code goes through the clause set and checks if the any of the clause contain clause set terms
        //if they do, the code then calls this method recursively on the those parts and attaches them
        val finalClaseSet: Set[SetSequent[Atom]] = instantiatedClauses.fold( Set[SetSequent[Atom]]() )( ( vale, x ) => {
          val ( newSuccSeq, cLSSyms ) = SequentSplitter( x.asInstanceOf[SetSequent[Atom]] )
          val newSetSequent = SetSequent( Sequent( x.asInstanceOf[SetSequent[Atom]].sequent.antecedent, newSuccSeq ) )
          if ( cLSSyms.isEmpty ) vale.asInstanceOf[Set[SetSequent[Atom]]] ++ Set[SetSequent[Atom]]( x.asInstanceOf[SetSequent[Atom]] )
          else {

            val baseofFold = if ( newSetSequent.sequent.antecedent.isEmpty && newSetSequent.sequent.succedent.isEmpty ) Set[SetSequent[Atom]]() else Set[SetSequent[Atom]]( newSetSequent )
            cLSSyms.fold( baseofFold )( ( mixedClauseSet, y ) => {
              val Apps( _, info ) = y
              val Const( newTopSym, _ ) = info.head
              val seperator = ClauseTermReader( info.tail )
              val ( _, ante, _, suc, _, args ) = seperator
              val alphaRenamedAnte = FormulaSetGeneralization( ante, args )
              val alphaRenamedSuc = FormulaSetGeneralization( suc, args )
              val newCutConfig = HOLSequent( alphaRenamedAnte, alphaRenamedSuc )
              val mapOnConfigs = css.get( newTopSym ) match { case Some( holseq ) => holseq case None => Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]() }
              val theconfigneeded = mapOnConfigs.keySet.foldLeft( newCutConfig )( ( thekey, cutconfigctk ) => if ( SequentInstanceOf( newCutConfig, cutconfigctk ) ) cutconfigctk else thekey )
              val theNewClauseSetPair = mapOnConfigs.get( theconfigneeded ) match { case Some( holseq ) => holseq case None => Set[( Expr, Set[SetSequent[Atom]] )]() }
              val ( valuenum, exprformatch, bestMatchClauses ) = PickCorrectInductiveCase( theNewClauseSetPair, args )
              val subargs = args.map( x => sigma( x ) )
              val Apps( _, vs: Seq[Expr] ) = exprformatch
              val zippedTogether = vs.zip( subargs ).map( x => {
                val ( one, two ) = x
                ( freeVariables( one ), two )
              } )
              val newsigma: Substitution = zippedTogether.fold( Substitution() )( ( sub, pair ) => {
                val ( one: Set[Var], two: Expr ) = pair
                sub.asInstanceOf[Substitution].compose( Substitution( one.head, two ) )
              } ).asInstanceOf[Substitution]
              println( bestMatchClauses.toString() )
              //Anela Please look at this, I am going Crazy line 103!!!
              //println(bestMatchClauses.head.sequent)
              mixedClauseSet
            } )
            vale
          }
        } ).asInstanceOf[Set[SetSequent[Atom]]]
        finalClaseSet
      }
    }
  }
  object ClauseTermReader {
    def apply( input: Seq[Expr] ): ( Set[Const], Set[Formula], Set[Const], Set[Formula], Set[Const], Set[Expr] ) = input.foldLeft( ( Set[Const](), Set[Formula](), Set[Const](),
      Set[Formula](), Set[Const](), Set[Expr]() ) )( ( bigCollect, w ) => {
      val ( one, two, three, four, five, six ) = bigCollect
      if ( one.isEmpty && ( w match {
        case Const( "|", _ ) => true
        case _               => false
      } ) ) {
        ( Set[Const]( w.asInstanceOf[Const] ), two, three, four, five, six )
      } else if ( one.nonEmpty && three.isEmpty && ( w match {
        case Const( "⊢", _ ) => true
        case _               => false
      } ) ) {
        ( one, two, Set[Const]( w.asInstanceOf[Const] ), four, five, six )
      } else if ( one.nonEmpty && three.isEmpty ) {
        ( one, two.asInstanceOf[Set[Formula]] ++ Set[Formula]( w.asInstanceOf[Formula] ), three, four, five, six )
      } else if ( one.nonEmpty && three.nonEmpty && five.isEmpty && ( w match {
        case Const( "|", _ ) => true
        case _               => false
      } ) ) {
        ( one, two, three, four, Set[Const]( w.asInstanceOf[Const] ), six )
      } else if ( one.nonEmpty && three.nonEmpty && five.isEmpty ) {
        ( one, two, three, four.asInstanceOf[Set[Formula]] ++ Set[Formula]( w.asInstanceOf[Formula] ), five, six )
      } else if ( one.nonEmpty && three.nonEmpty && five.nonEmpty ) {
        ( one, two, three, four, five, six.asInstanceOf[Set[Expr]] ++ Set[Expr]( w ) )
      } else bigCollect
    } )
  }
  //This code seperates the clause set symbols from the atoms of the given sequent
  object SequentSplitter {
    def apply( theSequent: SetSequent[Atom] ): ( Set[Atom], Set[Atom] ) = theSequent.sequent.succedent.fold( ( Set[Atom](), Set[Atom]() ) )( ( clset, y ) => {
      val ( seqNotCL: Set[Atom], seqInCL: Set[Atom] ) = clset
      y match {
        case Apps( Const( "CL", _ ), _ ) => ( seqNotCL.asInstanceOf[Set[Atom]],
          seqInCL.asInstanceOf[Set[Atom]] ++ Set[Atom]( y.asInstanceOf[Atom] ) )
        case _ => ( seqNotCL.asInstanceOf[Set[Atom]] ++ Set[Atom]( y.asInstanceOf[Atom] ),
          seqInCL.asInstanceOf[Set[Atom]] )
      }
    } ).asInstanceOf[( Set[Atom], Set[Atom] )]
  }

  //Finds the proof links within the given struct
  object StructDependences {
    def apply(
      topSym:        String,
      cutConfig:     HOLSequent,
      currentStruct: Set[( Expr, Struct[Nothing] )],
      foundCases:    Set[( String, HOLSequent )] ): Set[( String, HOLSequent )] = currentStruct.fold( Set[( String, HOLSequent )]() )( ( w, e ) => {
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

  //Constructs clause sets modulo the cut configurations and proofs
  object CutConfigProofClauseSetMaps {
    def apply(
      cutConfig:     HOLSequent,
      currentStruct: Set[( Expr, Struct[Nothing] )] ): Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]] = currentStruct.map( x => {
      val theClauseSet = CharacteristicClauseSet( x._2 ).asInstanceOf[Set[SetSequent[Atom]]]
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

  object FormulaSetGeneralization {
    def apply( theSetOfFormula: Set[Formula], args: Set[Expr] ): Set[Formula] = theSetOfFormula.map( ancestor => {
      args.fold( ( 0, ancestor ) )( ( ancestorVarUpdate, curTerm ) => {
        val ( varNum: Int, ancestorAtom: Formula ) = ancestorVarUpdate
        val posList = ancestorAtom.find( curTerm.asInstanceOf[Expr] )
        val newForm: Formula = posList.fold( ancestorAtom )( ( curForm, upTerm ) => {
          val withChange: Formula = curForm.asInstanceOf[Formula].replace( upTerm.asInstanceOf[HOLPosition], Var( "_schVar" + "1", curTerm.asInstanceOf[Expr].ty ) )
          withChange
        } ).asInstanceOf[Formula]
        ( varNum + 1, newForm )
      } ).asInstanceOf[( Int, Formula )]._2
    } )
  }

  //checks if S1 is an instance of S2
  object SequentInstanceOf {
    def apply( S1: HOLSequent, S2: HOLSequent ): Boolean = {
      FormulaSetInstanceOf( S1.antecedent, S2.antecedent ) &&
        FormulaSetInstanceOf( S1.succedent, S2.succedent )
    }
    def FormulaSetInstanceOf( SF1: Seq[Formula], SF2: Seq[Formula] ): Boolean = {
      if ( SF1.size == SF2.size ) {
        SF1.foldLeft( true, SF2.toList.toSet )( ( isInstanceof, F ) => {
          if ( !isInstanceof._1 ) {
            isInstanceof
          } else {
            val ( result, matchFormula ) = isInstanceof._2.foldLeft( ( false, isInstanceof._2.head ) )( ( isthere, SF ) => {
              if ( isthere._1 ) {
                isthere
              } else {
                val result = FormulaSetInstanceOf( F, SF )
                if ( result ) ( true, SF )
                else isthere

              }
            } )
            val newSetofFormula = if ( result ) isInstanceof._2 - matchFormula else isInstanceof._2
            ( result && isInstanceof._1, newSetofFormula )
          }
        } )._1
      } else false
    }
    def FormulaSetInstanceOf( F1: Formula, F2: Formula ): Boolean = {
      val listOfDiff = LambdaPosition.differingPositions( F1, F2 )
      listOfDiff.foldLeft( true )( ( isOK, pos ) => {
        val F1Pos = F1.get( pos ) match { case Some( x ) => x case None => F1 }
        val F2Pos = F2.get( pos ) match { case Some( x ) => x case None => F2 }
        ( F1Pos, F2Pos ) match {
          case ( Var( _, t ), Var( _, r ) ) => isOK && t.equals( r )
          case ( App( _, s ), Var( w, r ) ) => isOK && !s.contains( Var( w, r ) )
          case ( t, r )                     => isOK && t.equals( r )
        }
      } )
    }
  }

  object PickCorrectInductiveCase {
    def apply( CSP: Set[( Expr, Set[SetSequent[Atom]] )], args: Set[Expr] ): ( Int, Expr, Set[SetSequent[Atom]] ) =
      CSP.foldLeft( ( 0, CSP.head._1, CSP.head._2 ) )( ( theCorrect, current ) => {
        val ( Apps( _, argslink ), clauses ) = current
        val ( oldcount, oldex, clauses2 ) = theCorrect
        val totalcount = args.zip( argslink ).fold( 0 )( ( count, curpair ) => {
          val ( one, two ) = curpair
          if ( one.equals( two ) ) count.asInstanceOf[Int] + 1
          else count
        } ).asInstanceOf[Int]
        if ( totalcount > oldcount ) ( totalcount, current._1, clauses )
        else theCorrect
      } )
  }
}
