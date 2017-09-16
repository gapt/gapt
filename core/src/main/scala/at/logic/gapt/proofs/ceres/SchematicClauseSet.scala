package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr.{ Atom, Expr }
import at.logic.gapt.proofs.Context.ProofDefinitions
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.{ Context, HOLSequent, SetSequent }

//Idea behind the type is for each proof symbol we have a  Map,  which maps configurations to a set of sequents over atoms
//representing the clauses and the expression of the case of the inductive definition.
object SchematicClauseSet {
  def apply(
    TopSym:    String,
    ctx:       Context,
    cutConfig: HOLSequent = HOLSequent(), foundCases: Set[( String, HOLSequent )] = Set[( String, HOLSequent )]() ): Option[Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]] = {
    val ProofNames = ctx.get[ProofDefinitions].components.keySet
    if ( ProofNames.contains( TopSym ) ) {
      val TopProofs = ctx.get[ProofDefinitions].components.get( TopSym ) match {
        case Some( w ) => w
        case None      => Set[( Expr, LKProof )]()
      }
      //Makes the Structs for the top proofs
      val TopStructs: Set[( Expr, Struct[Nothing] )] = TopProofs.map( x => {
        val ( ex, lp ) = x
        ( ex, StructCreators.extract( lp, ProofNames ) )
      } )
      //For each Struct we will find the proof links that the Struct is dependent on.
      val TopDependents: Set[( String, HOLSequent )] = TopStructs.fold( Set[( String, HOLSequent )]() )( ( w, e ) => {
        val ( ex, st: Struct[Nothing] ) = e
        val temp: Set[Struct[Nothing]] = SchematicLeafs( st ).fold( Set[Struct[Nothing]]() )( ( g, pb ) => {
          val CLS( pf, ccon, frv, l ) = pb
          if ( foundCases.contains( ( pf, ccon ) ) ) g
          else g.asInstanceOf[Set[Struct[Nothing]]] ++ Set[Struct[Nothing]]( pb.asInstanceOf[Struct[Nothing]] )
        } ).asInstanceOf[Set[Struct[Nothing]]]
        val CLSyms: Set[( String, HOLSequent )] = temp.fold( Set[( String, HOLSequent )]() )( ( y, a ) => {
          val CLS( pf, ccon, frv, l ) = a
          if ( pf.matches( TopSym ) && ccon.equals( cutConfig ) ) Set[( String, HOLSequent )]( ( pf, ccon ) )
          else y.asInstanceOf[Set[( String, HOLSequent )]] ++ Set[( String, HOLSequent )]( ( pf, ccon ) )
        } ).asInstanceOf[Set[( String, HOLSequent )]]
        w.asInstanceOf[Set[( String, HOLSequent )]] ++ CLSyms
      } ).asInstanceOf[Set[( String, HOLSequent )]]

      //the constructions from all the dependents of the top proof
      val DependentMaps: Set[Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]] = TopDependents.map( x => {
        val ( sym, ccon ) = x
        val inducSet = foundCases ++ ( TopDependents - x ) ++ Set[( String, HOLSequent )]( ( TopSym, cutConfig ) )
        SchematicClauseSet( sym, ctx, ccon, inducSet ) match {
          case Some( cs ) => cs
          case None       => Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]()
        }
      } )

      //Reducing the dependents to a single map
      val DM: Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]] =
        DependentMaps.fold( Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]() )( ( x, y ) => { x ++ y } )

      //The top constructions
      val TopClauses: Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]] = TopStructs.map( x => {
        val ( ex, st ) = x
        val theRetClauseSet = CharacteristicClauseSet( st ).asInstanceOf[Set[SetSequent[Atom]]]
        val theRetSet = Set[( Expr, Set[SetSequent[Atom]] )]( ( ex, theRetClauseSet ) )
        Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]( ( cutConfig, theRetSet ) )
      } ).fold( Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]() )( ( vale, w ) => {
        w.keySet.fold( Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]() )( ( mail, xy ) => {
          if ( vale.keySet.contains( xy.asInstanceOf[HOLSequent] ) ) {
            val thevalinw = w.get( xy.asInstanceOf[HOLSequent] ) match {
              case Some( x ) => x
              case None      => Set[( Expr, Set[SetSequent[Atom]] )]()
            }
            val thevalinmail = vale.get( xy.asInstanceOf[HOLSequent] ) match {
              case Some( x ) => x
              case None      => Set[( Expr, Set[SetSequent[Atom]] )]()
            }
            mail.asInstanceOf[Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]] ++
              Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]( ( xy.asInstanceOf[HOLSequent], thevalinw ++ thevalinmail ) )
          } else {
            val thevalinw = w.get( xy.asInstanceOf[HOLSequent] ) match {
              case Some( x ) => x
              case None      => Set[( Expr, Set[SetSequent[Atom]] )]()
            }
            mail.asInstanceOf[Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]] ++
              Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]( ( xy.asInstanceOf[HOLSequent], thevalinw ) )
          }

        } ).asInstanceOf[Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]
      } )
      //Producing the final map
      val FinalMap: Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]] = DM ++
        Map[String, Map[HOLSequent, Set[( Expr, Set[SetSequent[Atom]] )]]]( ( TopSym, TopClauses ) )
      Some( FinalMap )
    } else None
  }
}
