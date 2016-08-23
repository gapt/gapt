package at.logic.gapt.grammars
import at.logic.gapt.expr._
import at.logic.gapt.formats.babel.{ BabelExporter, MapBabelSignature }

private class VtratgExporter( unicode: Boolean, vtratg: VTRATG )
    extends BabelExporter( unicode, vtratg.babelSignature ) {

  def csep( docs: List[Doc] ): Doc = ssep( docs, line( ", " ) )

  def export(): String = {
    val ntDecl = group( "Non-terminal vectors:" <> nest( line <> csep(
      vtratg.nonTerminals.toList map { nt =>
        "(" <> hsep( nt map { show( _, false, Set(), Map(), prio.max )._1 }, "," ) <> ")"
      }
    ) ) )

    val tDecl = group( "Terminals:" <> nest( line <> csep(
      vtratg.terminals.toList.sortBy { _.name } map { show( _, false, Set(), Map(), prio.max )._1 }
    ) ) )

    val knownTypes = vtratg.terminals.map { c => c.name -> c }.toMap

    val prods = sep( vtratg.productions.toList
      sortBy { case ( as, ts ) => ( vtratg.nonTerminals.indexOf( as ), ts.toString ) }
      map { p =>
        group( csep( p.zipped map ( ( a, t ) =>
          group( show( a, false, Set(), knownTypes, prio.impl )._1 </> nest( "→" </>
            show( t, true, Set(), knownTypes, prio.impl )._1 ) ) ) ) ) <> line
      } )

    pretty( group( ntDecl <> line <> tDecl <> line <> line <> prods ) ).layout
  }

}

object VTRATG {
  type NonTerminalVect = List[Var]
  type Production = ( NonTerminalVect, List[LambdaExpression] )
}

case class VTRATG( axiom: Var, nonTerminals: Seq[VTRATG.NonTerminalVect], productions: Set[VTRATG.Production] ) {
  import VTRATG._

  def termType = axiom.exptype

  def axiomVect: NonTerminalVect = List( axiom )

  def productions( nonTerminalVect: NonTerminalVect ): Set[Production] = productions filter ( _._1 == nonTerminalVect )
  def rightHandSides( nonTerminal: NonTerminalVect ) = productions( nonTerminal ) map ( _._2 )

  def terminals: Set[Const] = productions flatMap { p => constants( p._2 ) }

  def babelSignature = MapBabelSignature( terminals )

  productions foreach {
    case p @ ( a, t ) =>
      require( nonTerminals contains a, s"unknown non-terminal vector $a in $p" )
      val i = nonTerminals.indexOf( a )
      val allowedNonTerminals = nonTerminals.drop( i + 1 ).flatten.toSet
      t.flatMap( freeVariables( _ ) ) foreach { fv =>
        require( allowedNonTerminals contains fv, s"acyclicity violated in $p: $fv not in $allowedNonTerminals" )
      }
      require( a.size == t.size, s"vector production $p has sides of different length" )
      for ( ( ai, ti ) <- a zip t )
        require( ai.exptype == ti.exptype, s"vector production $p has mismatching types" )
  }
  require( nonTerminals contains axiomVect, s"axiom is unknown non-terminal vector $axiom" )

  def size = productions.size

  def weightedSize = productions.toSeq.map( _._1.size ).sum

  def language: Set[LambdaExpression] = {
    var lang = Set[LambdaExpression]( axiom )
    nonTerminals.foreach { a =>
      val P_a = productions( a )
      if ( P_a.nonEmpty )
        lang = P_a.flatMap { p =>
          Substitution( p.zipped )( lang )
        }
    }
    lang filter ( freeVariables( _ ).isEmpty )
  }

  override def toString: String = new VtratgExporter( unicode = true, vtratg = this ).export()
}
