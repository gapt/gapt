package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.base.RichOccSequent
import at.logic.gapt.proofs.lksk.TypeSynonyms.EmptyLabel
import at.logic.gapt.proofs.lksk.{ LabelledFormulaOccurrence, LabelledOccSequent }
import at.logic.gapt.proofs.resolutionOld.ral.{ InitialSequent => RalInitialSequent, _ }
import at.logic.gapt.proofs.{ Ant, HOLSequent, Suc }

/**
 * Created by marty on 9/9/14.
 */

object RobinsonToRal extends RobinsonToRal {
  @deprecated( "No idea what this should do", "2015-05-03" )
  override def convert_formula( e: HOLFormula ): HOLFormula = e
  @deprecated( "No idea what this should do", "2015-05-03" )
  override def convert_substitution( s: Substitution ): Substitution = s

  //TODO: this is somehow dirty....
  def convert_map( m: Map[Var, LambdaExpression] ): Substitution =
    Substitution( m.asInstanceOf[Map[Var, LambdaExpression]] )
}

abstract class RobinsonToRal {
  /* convert formula will be called on any formula before translation */
  def convert_formula( e: HOLFormula ): HOLFormula;

  /* convert subsitution will be called on any substitution before translation */
  def convert_substitution( s: Substitution ): Substitution;

  def convert_sequent( fs: HOLSequent ): HOLSequent = HOLSequent( fs.antecedent.map( convert_formula ), fs.succedent.map( convert_formula ) )

  def apply( rp: ResolutionProof ): RalResolutionProof[LabelledOccSequent] =
    rp match {
      case _: InitialClause =>
        val clause = rp.conclusion
        val rule = RalInitialSequent( convert_sequent( clause ), ( clause.antecedent.toList.map( x => EmptyLabel() ), clause.succedent.toList.map( x => EmptyLabel() ) ) )
        my_require( rule.root.toHOLSequent, clause, "Error in initial translation, translated root: " + rule.root.toHOLSequent + " is not original root " + clause )
        require( !rule.root.toHOLSequent.formulas.contains( ( x: HOLFormula ) => x.isInstanceOf[FOLFormula] ), "Formulas contain fol content!" )

        rule

      case Resolution( p2, aux2 @ Ant( _ ), p1, aux1 ) =>
        //println("Resolution on "+aux1+" in "+p1.root.succedent+" and "+aux2+" in "+p2.root.antecedent+ " with sub "+sub_)
        val rp1 = apply( p1 )
        val rp2 = apply( p2 )
        val rule = Cut( rp1, rp2, List( pickFOsucc( convert_formula( p1.conclusion( aux1 ) ), rp1.root, Nil ) ),
          List( pickFOant( convert_formula( p2.conclusion( aux2 ) ), rp2.root, Nil ) ) )
        my_require( rule.root.toHOLSequent, rp.conclusion, "Error in resolution translation, translated root: " + rule.root.toHOLSequent + " is not original root " + rp.conclusion )

        rule

      case Resolution( p1, aux1 @ Suc( _ ), p2, aux2 ) =>
        //println("Resolution on "+aux1+" in "+p1.root.succedent+" and "+aux2+" in "+p2.root.antecedent+ " with sub "+sub_)
        val rp1 = apply( p1 )
        val rp2 = apply( p2 )
        val rule = Cut( rp1, rp2, List( pickFOsucc( convert_formula( p1.conclusion( aux1 ) ), rp1.root, Nil ) ),
          List( pickFOant( convert_formula( p2.conclusion( aux2 ) ), rp2.root, Nil ) ) )
        my_require( rule.root.toHOLSequent, rp.conclusion, "Error in resolution translation, translated root: " + rule.root.toHOLSequent + " is not original root " + rp.conclusion )

        rule

      case Factor( parent, aux1 @ Ant( _ ), aux2 ) =>
        //        println( "antecedent factor 1: " + aux1 + sys.props("line.separator") + parent.root + sys.props("line.separator") + clause )
        val rp1 = apply( parent )
        val ( a :: aux ) = Seq( aux1, aux2 ).foldLeft( List[LabelledFormulaOccurrence]() )( ( list, x ) =>
          pickFOant( convert_formula( parent.conclusion( x ) ), rp1.root, list ) :: list ).reverse
        val rule = AFactorF( rp1, a, aux )
        my_require( rule.root.toHOLSequent, rp.conclusion, "Error in factor translation, translated root: " + rule.root.toHOLSequent + " is not original root " + rp.conclusion )

        rule

      case Factor( parent, aux1 @ Suc( _ ), aux2 ) =>
        //println( "succedent factor 1: " + aux1 + sys.props("line.separator") + parent.root + sys.props("line.separator") + clause )
        val rp1 = apply( parent )
        val ( a :: aux ) = Seq( aux1, aux2 ).foldLeft( List[LabelledFormulaOccurrence]() )( ( list, x ) =>
          pickFOsucc( convert_formula( parent.conclusion( x ) ), rp1.root, list ) :: list ).reverse
        val rule = AFactorT( rp1, a, aux )
        my_require( rule.root.toHOLSequent, rp.conclusion, "Error in factor translation, translated root: " + rule.root.toHOLSequent + " is not original root " + rp.conclusion )
        rule

      case Paramodulation( paraparent, equation, parent, modulant @ Ant( _ ), pos, dir ) =>
        val rp1 = apply( paraparent )
        val rp2 = apply( parent )
        val rule = ParaF( rp1, rp2, pickFOsucc( convert_formula( paraparent.conclusion( equation ) ), rp1.root, List() ),
          pickFOant( convert_formula( parent.conclusion( modulant ) ), rp2.root, List() ), convert_formula( rp.mainFormulas.head ) )
        my_require( rule.root.toHOLSequent, rp.conclusion, "Error in para translation, translated root: " + rule.root.toHOLSequent + " is not original root " + rp.conclusion )
        rule

      case Paramodulation( paraparent, equation, parent, modulant @ Suc( _ ), pos, dir ) =>
        //   println("translating instance from para parent:"+paraparent.root+" and "+ parent.root +" to "+clause+" with sub "+sub_)
        val rp1 = apply( paraparent )
        val rp2 = apply( parent )
        val rule = ParaT( rp1, rp2, pickFOsucc( convert_formula( paraparent.conclusion( equation ) ), rp1.root, List() ),
          pickFOsucc( convert_formula( parent.conclusion( modulant ) ), rp2.root, List() ),
          convert_formula( rp.mainFormulas.head ) )
        my_require( rule.root.toHOLSequent, rp.conclusion, "Error in para translation, translated root: " + rule.root.toHOLSequent + " is not original root " + rp.conclusion )
        rule

      case Instance( parent, sub_ ) =>

        val sub = convert_substitution( sub_ )
        //        val subexps = sub.map.toList.flatMap(x => List(x._1,x._2)).filterNot(checkFactory(_, HOLFactory))
        //        my_require(subexps.isEmpty , "Substitution contains fol content: "+subexps.map(_.factory))
        val rp1 = apply( parent )
        //        val rootexps = rp1.root.toHOLSequent.formulas.filterNot(checkFactory(_,HOLFactory))
        //        my_require(rootexps.isEmpty, "Formulas contain fol content: "+rootexps.mkString(" ::: "))
        val rule = if ( sub.isIdentity ) rp1 else Sub( rp1, sub )

        //println("inferring instance from parent:"+rp1.root+" to "+rule.root+" with sub "+sub)
        my_require( rule.root.toHOLSequent, rp.conclusion, "Error in instance translation, translated root: " + rule.root.toHOLSequent + " is not original root " + rp.conclusion )
        rule
    }

  def my_require( fs1: HOLSequent, fs2: HOLSequent, msg: String ) = {
    val cfs2 = convert_sequent( fs2 )
    require( fs1 multiSetEquals ( convert_sequent( fs2 ) ), msg + " (converted sequent is " + cfs2 + ")" ) //commented out, because the translation is too flexible now
  }

  def pickFO( f: HOLFormula, list: Seq[LabelledFormulaOccurrence], exclusion_list: Seq[LabelledFormulaOccurrence] ): LabelledFormulaOccurrence =
    list.find( x => x.formula == f && !exclusion_list.contains( x ) ) match {
      case None         => throw new Exception( "Could not find auxiliary formula " + f + " in " + list.mkString( "(", ",", ")" ) )
      case Some( focc ) => focc
    }

  def pickFOant( f: HOLFormula, fs: LabelledOccSequent, exclusion_list: Seq[LabelledFormulaOccurrence] ) = pickFO( f, fs.l_antecedent, exclusion_list )
  def pickFOsucc( f: HOLFormula, fs: LabelledOccSequent, exclusion_list: Seq[LabelledFormulaOccurrence] ) = pickFO( f, fs.l_succedent, exclusion_list )

}
