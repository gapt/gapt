package at.logic.gapt.provers.spass

import java.io.IOException

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.resolution.{ ResolutionProof, fixDerivation }
import at.logic.gapt.proofs.sketch._
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.utils.runProcess
import at.logic.gapt.utils.traits.ExternalProgram
import org.parboiled2._

import scala.collection.mutable
import scala.util.{ Failure, Success }

object SPASS extends SPASS
class SPASS extends ResolutionProver with ExternalProgram {

  def expr2dfg( e: LambdaExpression ): String = e match {
    case Bottom()             => "false"
    case Or( a, b )           => s"or(${expr2dfg( a )}, ${expr2dfg( b )})"
    case Neg( a )             => s"not(${expr2dfg( a )})"
    case All( v, a )          => s"forall([${v.name}],${expr2dfg( a )})"
    case Eq( t, s )           => s"equal(${expr2dfg( t )}, ${expr2dfg( s )})"
    case FOLAtom( n, Seq() )  => n
    case FOLAtom( n, as )     => s"$n(${as map expr2dfg mkString ","})"
    case FOLVar( n )          => n
    case FOLConst( n )        => n
    case FOLFunction( f, as ) => s"$f(${as map expr2dfg mkString ","})"
  }

  def cls2dfg( cls: FOLClause ): String = {
    val cls_ = FOLSubstitution( freeVariables( cls ).zipWithIndex.
      map { case ( v, i ) => v -> FOLVar( s"X$i" ) } )( cls )
    s"formula(${expr2dfg( univclosure( cls_.toFormula ) )})."
  }

  override def getRobinsonProof( clauses: Traversable[HOLClause] ): Option[ResolutionProof] = withRenamedConstants( clauses ) {
    case ( renaming, cnf ) =>
      if ( cnf isEmpty ) return None // SPASS doesn't like empty input

      val list_of_formulae =
        s"""
         |list_of_formulae(axioms).
         |${cnf.asInstanceOf[Traversable[FOLClause]] map cls2dfg mkString "\n"}
         |end_of_list.
       """.stripMargin

      val list_of_symbols = {
        val buf = new StringBuilder
        buf append "list_of_symbols.\n"

        val consts = cnf.view.flatMap( constants( _ ) ).toSet

        val funs = consts filter { _.isInstanceOf[FOLPartialTerm] }
        if ( funs nonEmpty ) buf append s"functions[${funs map { _.name } mkString ","}].\n"

        val preds = consts - EqC( Ti ) filter { _.isInstanceOf[FOLPartialAtom] }
        if ( preds nonEmpty ) buf append s"predicates[${preds map { _.name } mkString ","}].\n"

        buf append "end_of_list.\n"
        buf.toString()
      }

      val dfg =
        s"""
         |begin_problem(gapt).
         |
         |list_of_descriptions.
         |name({**}).
         |author({**}).
         |status(unknown).
         |description({**}).
         |end_of_list.
         |
         |$list_of_symbols
         |
         |$list_of_formulae
         |
         |end_problem.
       """.stripMargin

      val out = runProcess.withTempInputFile( Seq( "SPASS", "-DocProof" ), dfg, catchStderr = true )

      val lines = out.split( "\n" )

      if ( lines contains "SPASS beiseite: Proof found." ) {
        val proof = lines.
          dropWhile( !_.startsWith( "Here is a proof " ) ).drop( 1 ).
          takeWhile( !_.startsWith( "Formulae used " ) )

        val inferences = proof map InferenceParser.parseInference

        val inference2sketch = mutable.Map[Int, RefutationSketch]()
        val splitStack = mutable.Stack[( Int, FOLClause, Option[Int] )]()
        def finishSplit( infNum: Int, splitLevel: Int ): Unit =
          if ( splitLevel > 0 ) splitStack.pop() match {
            case ( splitCls, part1, None ) =>
              splitStack push ( ( splitCls, part1, Some( infNum ) ) )
            case ( splitCls, part1, Some( case1 ) ) =>
              inference2sketch( infNum ) = SketchSplit(
                inference2sketch( splitCls ), part1,
                inference2sketch( case1 ), inference2sketch( infNum )
              )
              finishSplit( infNum, splitLevel - 1 )
          }
        inferences foreach {
          case ( num, 0, "Inp", _, clause ) =>
            inference2sketch( num ) = SketchAxiom( cnf.find( clauseSubsumption( _, clause, matchingAlgorithm = fixDerivation.matchingModEq ).isDefined ).get.map { _.asInstanceOf[FOLAtom] } )
          case ( num, splitLevel, "Spt", Seq( splitClauseNum ), part1 ) =>
            val splitClause = inference2sketch( splitClauseNum ).conclusion
            val Some( subst ) = clauseSubsumption( part1, splitClause )
            require( subst.isRenaming )
            val correctPart1 = subst.asFOLSubstitution( part1 )
            splitStack push ( ( splitClauseNum, correctPart1, None ) )
            inference2sketch( num ) = SketchAxiom( correctPart1 )
          case ( num, splitLevel, "Spt", _, clause ) =>
            val splitClause = inference2sketch( splitStack.top._1 ).conclusion
            val correctClause =
              if ( clauseSubsumption( clause, splitClause ).isDefined ) {
                splitClause diff splitStack.top._2
              } else {
                require( clause.size == 1 && freeVariables( clause ).isEmpty )
                require( clause.swapped isSubsetOf splitStack.top._2 )
                clause
              }
            inference2sketch( num ) = SketchAxiom( correctClause )
          case ( num, splitLevel, _, premises, clause ) =>
            val p = SketchInference( clause, premises map inference2sketch )
            inference2sketch( num ) = p

            if ( clause isEmpty ) finishSplit( num, splitLevel )
        }

        val sketch = inference2sketch( inferences.last._1 )

        RefutationSketchToRobinson( sketch ) match {
          case scalaz.Failure( errors )   => throw new IllegalArgumentException( errors.list.toList mkString "\n" )
          case scalaz.Success( resProof ) => Some( resProof )
        }
      } else {
        None
      }
  }

  class InferenceParser( val input: ParserInput ) extends Parser {
    def Num = rule { capture( oneOrMore( CharPredicate.Digit ) ) ~> { _.toInt } }

    def Name = rule { capture( oneOrMore( CharPredicate.AlphaNum ) ) }

    def Backreference = rule { Num ~ "." ~ Num ~> ( ( inference, literal ) => inference ) }

    def Justification: Rule1[( Int, String, Seq[Int] )] = rule {
      "[" ~ Num ~ ":" ~ Name ~ optional( ":" ~ oneOrMore( Backreference ).separatedBy( "," ) ) ~ "]" ~>
        ( ( splitLevel: Int, inferenceType: String, premises: Option[Seq[Int]] ) => ( splitLevel, inferenceType, premises.getOrElse( Seq() ) ) )
    }

    def isVar( n: String ) = n.head.isUpper
    def Term: Rule1[FOLTerm] = rule {
      Name ~ optional( "(" ~ zeroOrMore( Term ).separatedBy( "," ) ~ ")" ) ~>
        ( ( name: String, args: Option[Seq[FOLTerm]] ) => if ( isVar( name ) ) FOLVar( name ) else FOLFunction( name, args.getOrElse( Seq() ) ) )
    }

    def Atom = rule {
      Name ~ optional( "(" ~ zeroOrMore( Term ).separatedBy( "," ) ~ ")" ) ~ zeroOrMore( anyOf( "*+" ) ) ~>
        ( ( name, args ) =>
          FOLAtom( if ( name == "equal" ) "=" else name, args.getOrElse( Seq() ) ) )
    }

    def Ws = rule { zeroOrMore( " " ) }

    def Clause: Rule1[FOLClause] = rule {
      zeroOrMore( Atom ~ Ws ) ~ "||" ~ Ws ~ zeroOrMore( Atom ~ Ws ) ~ "->" ~ Ws ~ zeroOrMore( Atom ~ Ws ) ~>
        ( ( constraints: Seq[FOLAtom], ant: Seq[FOLAtom], suc: Seq[FOLAtom] ) => constraints ++: ant ++: Sequent() :++ suc )
    }

    def Inference: Rule1[( Int, Int, String, Seq[Int], FOLClause )] = rule {
      Num ~ Justification ~ Ws ~ Clause ~ "." ~>
        ( ( inferenceNum: Int, just: ( Int, String, Seq[Int] ), clause: FOLClause ) => ( inferenceNum, just._1, just._2, just._3, clause ) )
    }
  }
  object InferenceParser {
    def parseInference( in: String ) = {
      val parser = new InferenceParser( in )
      parser.Inference.run() match {
        case Failure( error: ParseError ) =>
          throw new IllegalArgumentException( parser formatError error )
        case Failure( exception ) => throw exception
        case Success( value )     => value
      }
    }
  }

  override val isInstalled =
    try {
      runProcess.withExitValue( Seq( "SPASS" ) )
      true
    } catch {
      case ex: IOException => false
    }
}
