package gapt.provers.spass

import java.io.IOException

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.Bottom
import gapt.expr.formula.Eq
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.constants.EqC
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFunction
import gapt.expr.formula.fol.FOLPartialAtom
import gapt.expr.formula.fol.FOLPartialTerm
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.hol.universalClosure
import gapt.expr.subst.FOLSubstitution
import gapt.expr.ty.Ti
import gapt.expr.util.constants
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.logic.clauseSubsumption
import gapt.proofs._
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.resolution.{ AvatarNegNonGroundComp, AvatarNonGroundComp, ResolutionProof, fixDerivation }
import gapt.proofs.sketch._
import gapt.provers.{ ResolutionProver, extractIntroducedDefinitions, renameConstantsToFi }
import gapt.utils.{ ExternalProgram, Maybe, runProcess }
import org.parboiled2._

import scala.collection.mutable
import scala.util.{ Failure, Success }

object SPASS extends SPASS
class SPASS extends ResolutionProver with ExternalProgram {

  def expr2dfg( e: Expr ): String = e match {
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
    s"formula(${expr2dfg( universalClosure( cls_.toDisjunction ) )})."
  }

  override def getResolutionProof( clauses: Traversable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] = renameConstantsToFi.wrap( clauses.toSeq )(
    ( renaming, cnf: Seq[HOLClause] ) => {
      if ( cnf isEmpty ) return None // SPASS doesn't like empty input

      val list_of_formulae =
        s"""
         |list_of_formulae(axioms).
         |${cnf.asInstanceOf[Traversable[FOLClause]] map cls2dfg mkString "\n"}
         |end_of_list.
       """.stripMargin

      val consts = cnf.view.flatMap( constants( _ ) ).toSet
      val list_of_symbols = {
        val buf = new StringBuilder
        buf append "list_of_symbols.\n"

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

        val nameGen = rename.awayFrom( consts )

        class SpassSplit( splittingClause: RefutationSketch, part1: FOLClause ) {
          require( part1 isSubMultisetOf splittingClause.conclusion )
          val part2 = splittingClause.conclusion diff part1

          val splitAtom1 = FOLAtom( nameGen.freshWithIndex( "_split1" ) )
          val splitAtom2 = FOLAtom( nameGen.freshWithIndex( "_split2" ) )

          val comp1 = AvatarNonGroundComp( splitAtom1, universalClosure( part1.toDisjunction ) )
          val comp2 = AvatarNonGroundComp( splitAtom2, universalClosure( part2.toDisjunction ) )

          val emptyClause = SketchComponentElim( SketchComponentElim( splittingClause, comp1 ), comp2 )

          val addAxioms1 = Seq( SketchComponentIntro( comp1 ) )

          val groundNegPart1 =
            for ( ( a, i ) <- comp1.componentClause.zipWithIndex.elements if freeVariables( a ).isEmpty )
              yield AvatarNegNonGroundComp( comp1.atom, comp1.definition, comp1.vars, i )
          val addAxioms2 = Seq( comp2 ) ++ groundNegPart1 map { SketchComponentIntro( _ ) }
        }

        val inference2sketch = mutable.Map[Int, RefutationSketch]()
        val splitStack = mutable.Stack[( Int, SpassSplit, Option[Int] )]()
        val splitCases = Seq.newBuilder[RefutationSketch]
        def finishSplit( infNum: Int, splitLevel: Int ): Unit =
          if ( splitLevel > 0 ) splitStack.pop() match {
            case ( splitCls, split, None ) =>
              splitStack push ( ( splitCls, split, Some( infNum ) ) )
            case ( splitCls, split, Some( case1 ) ) =>
              finishSplit( infNum, splitLevel - 1 )
          }
        inferences foreach {
          case ( num, 0, "Inp", _, clause ) =>
            val Some( clauseInOurCNF ) = cnf.find( clauseSubsumption.modEqSymm( _, clause ).isDefined )
            inference2sketch( num ) = SketchInference( clause, Seq( SketchAxiom( clauseInOurCNF map { _.asInstanceOf[FOLAtom] } ) ) )
            if ( clause isEmpty ) splitCases += inference2sketch( num )
          case ( num, splitLevel, "Spt", Seq( splitClauseNum ), part1 ) =>
            val splitClause = inference2sketch( splitClauseNum ).conclusion
            val Some( subst ) = clauseSubsumption( part1, splitClause )
            require( subst.isRenaming )
            val correctPart1 = subst.asFOLSubstitution( part1 )
            val split = new SpassSplit( inference2sketch( splitClauseNum ), correctPart1 )
            splitCases += split.emptyClause
            splitStack push ( ( splitClauseNum, split, None ) )
            inference2sketch( num ) = SketchInference( splitClause, split.addAxioms1 )
          case ( num, splitLevel, "Spt", _, clause ) =>
            val split = splitStack.top._2
            inference2sketch( num ) = SketchInference( clause, split.addAxioms2 )
          case ( num, splitLevel, _, premises, clause ) =>
            val p = SketchInference( clause, premises map inference2sketch )
            inference2sketch( num ) = p

            if ( clause isEmpty ) {
              splitCases += p
              finishSplit( num, splitLevel )
            }
        }

        val sketch = SketchSplitCombine( splitCases.result() )

        RefutationSketchToResolution( sketch ) match {
          case Left( error )     => throw new IllegalArgumentException( error.toString )
          case Right( resProof ) => Some( resProof )
        }
      } else {
        None
      }
    } ).map { resolution =>
      extractIntroducedDefinitions( resolution )
      resolution
    }

  class InferenceParser( val input: ParserInput ) extends Parser {
    def Num = rule { capture( oneOrMore( CharPredicate.Digit ) ) ~> { _.toInt } }

    def Name = rule { capture( oneOrMore( CharPredicate.AlphaNum ++ '_' ) ) }

    def Backreference = rule { Num ~ "." ~ Num ~> ( ( inference, literal ) => inference ) }

    def Justification: Rule1[( Int, String, Seq[Int] )] = rule {
      "[" ~ Num ~ ":" ~ Name ~ optional( ":" ~ oneOrMore( Backreference ).separatedBy( "," ) ) ~ "]" ~>
        ( ( splitLevel: Int, inferenceType: String, premises: Option[Seq[Int]] ) => ( splitLevel, inferenceType, premises.getOrElse( Seq() ).distinct ) )
    }

    def isVar( n: String ) = n.head.isUpper || 'u'.to( 'z' ).contains( n.head )
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
