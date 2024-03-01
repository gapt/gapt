package gapt.cutintro

import gapt.expr._
import gapt.expr.formula.And
import gapt.expr.formula.Formula
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.subst.Substitution
import gapt.expr.util.rename
import gapt.logic.hol.simplifyPropositional
import gapt.provers.smtlib.SmtInterpol
import gapt.utils.Tree
import gapt.proofs.RichFOLSequent

/**
 * Solution finding algorithm for Π₁-cut-introduction based on the Duality algorithm for
 * constrained Horn clause verification[1].
 *
 * [1] K. L. McMillan, A. Rybalchenko, Solving Constrained Horn Clauses using Interpolation,
 *     technical report MSR-TR-2013-6, available at
 *     https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/MSR-TR-2013-6.pdf
 */
object solutionViaInterpolation {

  def apply( sehs: SchematicExtendedHerbrandSequent ): Seq[FOLFormula] = {
    val nameGen = rename.awayFrom( containedNames( sehs.us ) ++ containedNames( sehs.ss ) )

    def mkAss( i: Int, subst: Substitution ): Tree[( Int, Substitution, Formula )] = {
      val insts = subst( sehs.esInstancesInScope( i + 1 ).toNegConjunction )
      if ( i < 0 ) {
        Tree( ( i + 1, subst, insts ), Vector() )
      } else {
        val vss = for ( _ <- sehs.ss( i )._2 )
          yield sehs.ss( i )._1.map( v => Const( nameGen.fresh( v.name ), v.ty ) )
        val children = for ( vs <- vss )
          yield mkAss( i - 1, subst compose Substitution( sehs.ss( i )._1 zip vs ) )
        val eqs = for ( ( s, v ) <- subst( sehs.ss( i )._2 ).flatten.zip( vss.flatten ) ) yield v === s
        Tree( ( i + 1, subst, And( eqs ) & insts ), children.toVector )
      }
    }

    val tree = mkAss( sehs.ss.size - 1, Substitution() )
    val Some( interpolants ) = SmtInterpol.getInterpolant( tree.map( _._3 ) )
    val simplified = interpolants.map( simplifyPropositional( _ ) )

    val generalized =
      simplified.zip( tree.map( _._2 ) ).map {
        case ( i, s ) =>
          TermReplacement( i, s.map.map( _.swap ) )
      }

    val solution =
      for ( i <- sehs.ss.indices )
        yield And( generalized.zip( tree.map( _._1 ) ).postOrder.filter( _._2 == i ).map( _._1 ).distinct )

    solution.map( _.asInstanceOf[FOLFormula] )
  }

}
