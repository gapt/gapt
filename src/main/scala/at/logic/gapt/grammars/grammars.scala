package at.logic.gapt.grammars
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution

object VectTratGrammar {
  type NonTerminalVect = List[FOLVar]
  type Production = ( NonTerminalVect, List[FOLTerm] )
}

case class VectTratGrammar( axiom: FOLVar, nonTerminals: Seq[VectTratGrammar.NonTerminalVect], productions: Seq[VectTratGrammar.Production] ) {
  import VectTratGrammar._

  def axiomVect: NonTerminalVect = List( axiom )

  def productions( nonTerminalVect: NonTerminalVect ): Seq[Production] = productions filter ( _._1 == nonTerminalVect )
  def rightHandSides( nonTerminal: NonTerminalVect ) = productions( nonTerminal ) map ( _._2 )

  productions foreach {
    case p @ ( a, t ) =>
      require( nonTerminals contains a, s"unknown non-terminal vector $a in $p" )
      val i = nonTerminals.indexOf( a )
      val allowedNonTerminals = nonTerminals.drop( i + 1 ).flatten.toSet
      t.flatMap( freeVariables( _ ) ) foreach { fv =>
        require( allowedNonTerminals contains fv, s"acyclicity violated in $p: $fv not in $allowedNonTerminals" )
      }
      require( a.size == t.size, s"vector production $p has sides of different length" )
  }
  require( nonTerminals contains axiomVect, s"axiom is unknown non-terminal vector $axiom" )

  def size = productions.size

  def language: Set[FOLTerm] = {
    var lang = Set[FOLTerm]( axiom )
    nonTerminals.foreach { a =>
      val P_a = productions( a )
      if ( P_a.nonEmpty )
        lang = P_a.flatMap { p =>
          lang.map( FOLSubstitution( p.zipped toSeq ).apply )
        } toSet
    }
    lang filter ( freeVariables( _ ).isEmpty )
  }

  override def toString: String = {
    val s = new StringBuilder
    s append s"Axiom: ($axiom)\n"
    s append s"Non-terminal vectors:\n"
    nonTerminals foreach { a =>
      s append s"  (${a.mkString( ", " )})\n"
    }
    s append s"Productions:\n"
    productions.sortBy { case ( as, ts ) => nonTerminals.indexOf( as ) } foreach {
      case ( as, ts ) =>
        ( as, ts ).zipped foreach {
          case ( a, t ) =>
            s append s"  $a -> $t\n"
        }
        s append "\n"
    }
    s.toString()
  }
}

object TratGrammar {
  type Production = ( FOLVar, FOLTerm )

  def asVectTratGrammarProduction( p: Production ): VectTratGrammar.Production =
    List( p._1 ) -> List( p._2 )
}

case class TratGrammar( axiom: FOLVar, nonTerminals: Seq[FOLVar], productions: Seq[TratGrammar.Production] ) {
  import TratGrammar._

  def productions( nonTerminal: FOLVar ): Seq[Production] = productions filter ( _._1 == nonTerminal )
  def rightHandSides( nonTerminal: FOLVar ) = productions( nonTerminal ) map ( _._2 )

  productions foreach {
    case p @ ( a, t ) =>
      require( nonTerminals contains a, s"unknown non-terminal $a in $p" )
      val allowedNonTerminals = nonTerminals.drop( nonTerminals.indexOf( a ) + 1 ).toSet
      freeVariables( t ) foreach { fv =>
        require( allowedNonTerminals contains fv, s"acyclicity violated in $p: $fv not in $allowedNonTerminals" )
      }
  }
  require( nonTerminals contains axiom, s"axiom is unknown non-terminal $axiom" )

  def toVectTratGrammar: VectTratGrammar = VectTratGrammar(
    axiom, nonTerminals map ( List( _ ) ),
    productions map asVectTratGrammarProduction )

  def language: Set[FOLTerm] = toVectTratGrammar language

  override def toString: String = {
    val s = new StringBuilder
    s append s"Axiom: $axiom\n"
    s append s"Non-terminals: ${nonTerminals.mkString( ", " )}\n"
    s append s"Productions:\n"
    productions.sortBy { case ( a, t ) => ( nonTerminals.indexOf( a ), t.toString() ) } foreach {
      case ( a, t ) =>
        s append s"  $a -> $t\n"
    }
    s.toString()
  }
}
