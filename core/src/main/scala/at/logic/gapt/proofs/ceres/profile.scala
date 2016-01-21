/* commented out since the algorithm relies on ancestor information in formula occurrences which are traced via the
   removed formula occurrences. 
package at.logic.gapt.proofs.ceres.clauseSets.profile

import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lksk.{ LabelledOccSequent, LabelledFormulaOccurrence, UnaryLKskProof }
import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.proofs.ceres.clauseSets.StandardClauseSet._
import at.logic.gapt.proofs.ceres.struct._

object getListOfFOccsInStruct {
  def apply( s: Struct ): List[FormulaOccurrence] = s match {
    case Plus( s1, s2 )     => apply( s1 ) ++ apply( s2 )
    case Times( s1, s2, _ ) => apply( s1 ) ++ apply( s2 )
    case A( fo )            => fo :: Nil //{ println( sys.props("line.separator") + sys.props("line.separator") + "A(fo) = "+fo);fo::Nil}
    case Dual( sub )        => apply( sub )
    case EmptyTimesJunction => Nil
    case EmptyPlusJunction  => Nil
    case _                  => { println( sys.props( "line.separator" ) + sys.props( "line.separator" ) + "ERROR in getListOfFOccsInStruct" ); List() }
  }
}

//gets from the axioms those formula occurrences which are ancestors of fo
object getAncAx {
  def apply( fo: FormulaOccurrence, p: LKProof ): List[FormulaOccurrence] = fo.parents match {
    case List() if getAllAxioms.isFOccInAxiom( fo, getAllAxioms.apply( p ) ) => fo :: Nil
    case _ => fo.parents.foldLeft( List[FormulaOccurrence]() )( ( x, y ) => x ::: apply( y, p ) )
  }
}

object proofProfile {

  def apply( struct: Struct, proof: LKProof ) = transformStructToProfile( struct, proof )

  // apply Bruno's rewrite system
  def rewrite( struct: Struct )( implicit proof: LKProof ): Struct = struct match {
    case Plus( s1, s2 ) => Plus( rewrite( s1 ), rewrite( s2 ) )
    case Times( s1, s2, auxFOccs ) => {
      applyRule( rewrite( s1 ), rewrite( s2 ), auxFOccs )
    }
    case s: A               => s
    case Dual( sub )        => Dual( rewrite( sub ) )
    case EmptyTimesJunction => struct
    case EmptyPlusJunction  => struct
  }

  def transformStructToProfile( struct: Struct, proof: LKProof ) = {
    implicit val p = proof
    clausify( normalize( rewrite( struct ) ) )
  }

  private def transformProfiledCartesianProductToStruct( cp: List[( Struct, Struct )] ): Struct = cp match {
    case Nil              => throw new Exception( "Pattern matching failed unexpectedly: List is empty." )
    case ( i, j ) :: Nil  => Times( i, j, List[FormulaOccurrence]() )
    case ( i, j ) :: rest => Plus( Times( i, j, List[FormulaOccurrence]() ), transformProfiledCartesianProductToStruct( rest ) )
  }

  private def transformNotProfiledCartesianProductToStruct( cp: List[Struct] ): Struct = cp match {
    case Nil       => throw new Exception( "Pattern matching failed unexpectedly: List is empty." )
    case i :: Nil  => i
    case i :: rest => Plus( i, transformNotProfiledCartesianProductToStruct( rest ) )
  }

  def isRedStruct( s: Struct, anc_OfauxFOccs: List[FormulaOccurrence] ): Boolean = !( getListOfFOccsInStruct( s ).intersect( anc_OfauxFOccs ) ).isEmpty

  private def applyRule( s1: Struct, s2: Struct, auxFOccs: List[FormulaOccurrence] )( implicit proof: LKProof ): Struct = {
    val ( list1, list2 ) = ( getTimesJunctions( s1 ), getTimesJunctions( s2 ) )

    if ( list1.size == 0 || list2.size == 0 )
      println( "ERROR, sizes = 0" )

    if ( list1.size == 1 && list2.size == 1 )
      return Times( s1, s2, auxFOccs )

    def ancOfAuxFOccs = getAllAxioms.getAllCorrFOccs( auxFOccs.foldLeft( List[FormulaOccurrence]() )( ( x, y ) => x ::: getAncAx( y, proof ) ), proof )

    val black_list1 = list1.filter( s => !isRedStruct( s, ancOfAuxFOccs ) )
    val red_list1 = list1.filter( s => isRedStruct( s, ancOfAuxFOccs ) )
    val black_list2 = list2.filter( s => !isRedStruct( s, ancOfAuxFOccs ) )
    val red_list2 = list2.filter( s => isRedStruct( s, ancOfAuxFOccs ) )

    val profiledCartesianProduct = for ( i <- red_list1; j <- red_list2 ) yield ( i, j )
    val notProfiledCartesianProduct = black_list1 ::: black_list2

    if ( profiledCartesianProduct.size > 0 ) // rewrite
    {
      val str2 = transformProfiledCartesianProductToStruct( profiledCartesianProduct )
      if ( notProfiledCartesianProduct.size > 0 ) {
        val str1 = transformNotProfiledCartesianProductToStruct( notProfiledCartesianProduct )
        // rewrite again --- maybe we have created a new redex.
        rewrite( Plus( str1, str2 ) )
      } else {
        str2
      }
    } else {
      Times( s1, s2, auxFOccs )
    }
  }

  private def getTimesJunctions( struct: Struct ): List[Struct] = struct match {
    case s: Times           => s :: Nil
    case EmptyTimesJunction => struct :: Nil
    case s: A               => s :: Nil
    case s: Dual            => s :: Nil
    case Plus( s1, s2 )     => getTimesJunctions( s1 ) ::: getTimesJunctions( s2 )
  }

  private def getLiterals( struct: Struct ): List[Struct] = struct match {
    case s: A               => s :: Nil
    case s: Dual            => s :: Nil
    case EmptyTimesJunction => Nil
    case EmptyPlusJunction  => Nil
    case Plus( s1, s2 )     => getLiterals( s1 ) ::: getLiterals( s2 )
    case Times( s1, s2, _ ) => getLiterals( s1 ) ::: getLiterals( s2 )
  }
}

object getAllAxioms {
  def apply( p: LKProof ): List[OccSequent] = p match {
    case CutRule( p1, p2, _, a1, a2 )           => apply( p1 ) ++ apply( p2 )

    case UnaryLKProof( _, p, _, _, _ )          => apply( p )
    case BinaryLKProof( _, p1, p2, _, _, _, _ ) => apply( p1 ) ++ apply( p2 )
    case Axiom( so )                            => so :: Nil
  }

  def isFOccInAxiom( fo: FormulaOccurrence, from: List[OccSequent] ): Boolean = from match {
    case so :: rest if so.antecedent.contains( fo ) || so.succedent.contains( fo ) => true
    case so :: rest => isFOccInAxiom( fo, rest )
    case _ => false
  }

  def printCorrespSequent( fo: FormulaOccurrence, from: List[OccSequent] ) = from match {
    case so :: rest if so.antecedent.contains( fo ) || so.succedent.contains( fo ) => { so.antecedent.toList.map( x => { print( x.formula ) } ); print( "  |-  " ); so.succedent.toList.map( x => { print( x.formula ) } ) }
    case so :: rest => getPartnerFOccs( fo, rest )
  }

  def getPartnerFOccs( fo: FormulaOccurrence, from: List[OccSequent] ): List[FormulaOccurrence] = from match {
    case so :: rest if so.antecedent.contains( fo ) || so.succedent.contains( fo ) => so.antecedent.toList ::: so.succedent.toList
    case so :: rest => getPartnerFOccs( fo, rest )
    case _ => List()
  }

  def getAllCorrespondingFOccs( lFOcc: List[FormulaOccurrence], from: List[OccSequent] ): List[FormulaOccurrence] = lFOcc.map( x => getPartnerFOccs( x, from ) ).foldLeft( List[FormulaOccurrence]() )( ( x, y ) => x ::: y )

  def getAllCorrFOccs( lFOcc: List[FormulaOccurrence], p: LKProof ) = getAllCorrespondingFOccs( lFOcc, apply( p ) )
}

object printCutAncs {
  def apply( p: LKProof ) = {
    getCutAncestors( p ).foreach( fo => println( fo.formula.toString ) )
  }
}
*/ 