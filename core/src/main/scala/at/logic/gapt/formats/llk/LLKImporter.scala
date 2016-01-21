package at.logic.gapt.formats.llk

import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lkOld.{ applySubstitution, AtomicExpansion, solve }
import at.logic.gapt.proofs.lksk.{ LabelledFormulaOccurrence, LabelledOccSequent }
import at.logic.gapt.formats.llkNew.{ ast, DeclarationParser, LLKFormulaParser }
import at.logic.gapt.formats.llkNew.ast.LambdaAST
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs.lkOld.base._
import at.logic.gapt.proofs.lkOld._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lkOld.EquationVerifier._
import at.logic.gapt.expr.BetaReduction._
import at.logic.gapt.utils.logging.Logger
import org.slf4j.LoggerFactory
import scala.annotation.tailrec
import at.logic.gapt.formats.llk._
import at.logic.gapt.proofs.lkOld.EquationVerifier.EqualModuloEquality

object LLKFormatter {
  /* formats a sequent */
  def f( fs: HOLSequent ): String = {
    " " + ( fs.antecedent.map( toLLKString.apply ).mkString( ", " ) ) + " :- " +
      ( fs.succedent.map( toLLKString.apply ).mkString( ", " ) ) + " "
  }

  def f( s: Substitution ): String = {
    s.map.map( x => f( x._1 ) + " -> " + f( x._2 ) ).mkString( "{", ",", "}" )
  }

  def f( fs: OccSequent )( implicit dummy: DummyImplicit ): String = f( fs.toHOLSequent )
  def f( lfo: LabelledFormulaOccurrence ): String =
    f( lfo.formula ) + lfo.skolem_label.map( f ).mkString( "[label: ", ", ", "]" )

  def f( ls: LabelledOccSequent ): String = {
    ls.l_antecedent.map( f ).mkString( "", ", ", " :- " ) +
      ls.l_succedent.map( f ).mkString( "", ", ", "" )
  }
  def f( e: LambdaExpression ): String = " " + toLLKString( e ) + " "
}

/**
 * This implements the second parsing pass, converting hlk Tokens to an LK Proof. HybridLatexParser inherits from
 * TokenToLKConverter to have a common interface, but the code here is only dependent on the AST. It uses the ASTtoHOL
 * object to create LambdaExpressions from hol ASTs.
 */
trait TokenToLKConverter extends Logger {
  override def loggerName = "LLKLogger"
  import LLKFormatter._

  /* Extracts type declarations from the tokens and creates a function to create atomic terms by name */
  def createNaming( r: List[Token] ): ( String => LambdaExpression ) = {
    val ctypes: List[( String, Ty )] = r.flatMap( _ match {
      case TToken( "CONST", names, t ) => names map ( ( _, t ) )
      case _                           => Nil
    } )
    val constmap = Map[String, Ty]() ++ ctypes

    val vtypes: List[( String, Ty )] = r.flatMap( _ match {
      case TToken( "VAR", names, t ) => names map ( ( _, t ) )
      case _                         => Nil
    } )
    val varmap = Map[String, Ty]() ++ vtypes

    { ( s: String ) =>
      {
        if ( varmap contains s ) {
          Var( s, varmap( s ) )
        } else if ( constmap contains s ) {
          Const( s, constmap( s ) )
        } else

          throw new HybridLatexParserException( "no type declaration for symbol " + s )
      }
    }
  }

  def printRules( r: List[Token] ): List[HOLSequent] = {
    val rules = r.filter( _ match { case RToken( _, _, _, _, _ ) => true; case _ => false } )
    val naming = createNaming( r )

    var l = List[HOLSequent]()

    for ( RToken( name, argname, antecedent, succedent, _ ) <- rules ) {
      val ant = antecedent.map( x => c( LLKFormulaParser.ASTtoHOL( naming, x ) ) )
      val suc = succedent.map( x => c( LLKFormulaParser.ASTtoHOL( naming, x ) ) )
      val fs = HOLSequent( ant, suc )
      //println(name + ": "+fs)
      l = fs :: l
    }

    l.reverse
  }

  /* The main entry point to the proof parser. The list of tokens l is taken apart into subproofs (noticable by the
     CONTINUEWITH rule). Then the subproofs are ordered by dependency and constructed in this order*/
  def createLKProof( l: List[Token] ): ExtendedProofDatabase = {
    //seperate rule tokens from type declaration tokens
    val ( rtokens, tatokens ) = l.partition( _ match {
      case RToken( _, _, _, _, _ ) => true;
      case _                       => false;
    } ).asInstanceOf[( List[RToken], List[Token] )] //need to cast because partition returns Tokens
    val ( ttokens, atokens ) = tatokens.partition( _ match {
      case TToken( _, _, _ )        => true;
      case t @ AToken( _, _, _, _ ) => false;
      case t: Token                 => throw new Exception( "Severe error: rule tokens were already filtered out, but rule " + t + " still contained!" )
    } ).asInstanceOf[( List[TToken], List[AToken] )] //need to cast because partition returns Tokens
    //println("creating naming!")
    val naming = createNaming( ttokens )
    //println("creating axioms!")
    val unclosedaxioms = createAxioms( naming, atokens )
    //println("closing axioms!")
    val axioms = unclosedaxioms map ( x => ( x._1, univclosure( x._2 ) ) )
    //println(axioms)
    //println("creating definitions!")
    val definitions = createDefinitions( naming, atokens, axioms )

    //println(definitions)
    //seperate inferences for the different (sub)proofs
    val ( last, rm ) = rtokens.foldLeft( ( List[RToken]() ), Map[HOLFormula, List[RToken]]() )( ( current, token ) => {
      token match {
        case RToken( "CONTINUEWITH", Some( name ), a, s, _ ) =>
          //put proof under name into map, continue with empty rulelist
          try {
            val nformula = c( LLKFormulaParser.ASTtoHOL( naming, name ) )
            ( Nil, current._2 + ( ( nformula, current._1.reverse ) ) )
          } catch {
            case e: Exception => throw new HybridLatexParserException( "Error in parsing CONTINUEWITH{" + name + "}{" + a + "}{" + s"}: " + e.getMessage, e )
          }
        case RToken( "CONTINUEWITH", _, _, _, _ ) =>
          throw new HybridLatexParserException( "The CONTINUEWITH statement needs a name giving the argument!" )
        case RToken( "COMMENT", _, _, _, _ ) =>
          //filter comments
          current
        case _ =>
          //apend rule to current list
          ( token :: current._1, current._2 )
      }
    } )

    require( last.isEmpty, "There are some rules left after parsing the list, use CONTINUEFROM to give proof a name! " + last )

    //dependncy analysis
    val dependecies = getDependecyMap( naming, rm )
    val ordering: List[HOLFormula] = getOrdering( dependecies )

    //proof completion in dependency order
    val proofs = ordering.foldLeft( Map[HOLFormula, LKProof]() )( ( proofs_done, f ) => {
      //println("Processing (sub)proof "+this.f(f))
      val f_proof: LKProof = completeProof( f, proofs_done, naming, rm( f ), axioms, definitions )
      proofs_done + ( ( f, f_proof ) )
    } )
    ExtendedProofDatabase( proofs, axioms, definitions )
  }

  /* Creates the subproof proofname from a list of rules. Uses the naming function to create basic term and
  *  uses the proofs map to look up subproofs referenced by CONTINUEWITH and INSTLEMMA. This means, the calls
  *  to completeProof have to be ordered s.t. dependent proofs are already contained in the map.*/
  def completeProof(
    proofname:   HOLFormula,
    proofs:      Map[HOLFormula, LKProof],
    naming:      String => LambdaExpression,
    rules:       List[RToken],
    axioms:      Map[HOLFormula, HOLFormula],
    definitions: Map[LambdaExpression, LambdaExpression]
  ): LKProof = {
    var proofstack: List[LKProof] = List[LKProof]()
    for ( rt @ RToken( name, auxterm, antecedent, succedent, sub ) <- rules ) {
      //println("Processing rule: "+name)
      val ant = antecedent.map( x => c( LLKFormulaParser.ASTtoHOL( naming, x ) ) )
      val suc = succedent.map( x => c( LLKFormulaParser.ASTtoHOL( naming, x ) ) )
      val fs = HOLSequent( ant, suc )
      val nLine = sys.props( "line.separator" )
      name match {
        case "AX" =>
          proofstack = Axiom( ant, suc ) :: proofstack
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "TAUTCOMPLETION" =>
          require( ant.size == 1, "Tautological Axiom Completion needs exactly one formula in the antecedent, not " + ant.mkString( "," ) )
          require( suc.size == 1, "Tautological Axiom Completion needs exactly one formula in the succedent, not " + suc.mkString( "," ) )
          require( ant( 0 ) == suc( 0 ), "Tautological Axiom Completion can only expand sequents of the form F :- F, not " + HOLSequent( ant, suc ) )
          val rule = AtomicExpansion( HOLSequent( ant, suc ) )
          proofstack = rule :: proofstack
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "AUTOPROP" =>
          try {
            val Some( rule ) = solve.solvePropositional( HOLSequent( ant, suc ), true )
            proofstack = rule :: proofstack
            require(
              proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
              "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
            )
          } catch {
            case e: Exception =>
              throw new HybridLatexParserException( "Autopropositional failed with the message: " + e.getMessage + nLine + "Stack Trace:" + nLine +
                e.getStackTrace.mkString( "", nLine, nLine ), e )
          }
        // --- quantifier rules ---
        case "ALLL" =>
          proofstack = handleWeakQuantifier( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "EXR" =>
          proofstack = handleWeakQuantifier( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "ALLR" =>
          proofstack = handleStrongQuantifier( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "EXL" =>
          proofstack = handleStrongQuantifier( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "ANDR" =>
          proofstack = handleBinaryLogicalOperator( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "ORL" =>
          proofstack = handleBinaryLogicalOperator( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "IMPL" =>
          proofstack = handleBinaryLogicalOperator( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        // --- unary rules ---
        case "ORR" =>
          proofstack = handleUnaryLogicalOperator( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "ANDL" =>
          proofstack = handleUnaryLogicalOperator( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "IMPR" =>
          proofstack = handleUnaryLogicalOperator( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        // --- negation rules ---
        case "NEGL" =>
          proofstack = handleNegation( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "NEGR" =>
          proofstack = handleNegation( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )

        // --- equational rules ---
        case "EQL" =>
          proofstack = handleEquality( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "EQR" =>
          proofstack = handleEquality( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )

        // --- definition rules ---
        case "DEF" =>
          proofstack = handleDefinitions( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )

        // --- structural rules ---
        case "CONTRL" =>
          proofstack = handleContraction( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "CONTRR" =>
          proofstack = handleContraction( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "WEAKL" =>
          proofstack = handleWeakening( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "WEAKR" =>
          proofstack = handleWeakening( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "CUT" =>
          proofstack = handleCut( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )

        // --- macro rules ---
        case "EQAXIOM" =>
          proofstack = handleEQAxiom( proofstack, name, fs, auxterm, sub, naming, rt, axioms, definitions )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )

        case "INSTAXIOM" =>
          proofstack = handleInstAxiom( proofstack, name, fs, auxterm, sub, naming, rt, axioms, definitions )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )

        case "CONTINUEFROM" =>
          proofstack = handleLink( proofs, proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack( 0 ).root.toHOLSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) + " got " + f( proofstack( 0 ).root.toHOLSequent ) + " instead!"
          )
        case "CONTINUEWITH" => ;
        case "COMMENT"      => ;
        case _              => throw new HybridLatexParserException( "Rule type " + name + " not yet implemented!" )
      }

    }

    require( proofstack.nonEmpty, "Error creating proof: Proof stack may not be empty!" )
    proofstack.head
  }

  /* Takes care of weak quantifiers. */
  def handleWeakQuantifier( current_proof: List[LKProof], ruletype: String, fs: HOLSequent, auxterm: Option[LambdaAST], naming: ( String ) => LambdaExpression, rt: RToken ): List[LKProof] = {
    require( current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val oldproof :: rest = current_proof

    val ( mainsequent, auxsequent, _ ) = filterContext( oldproof.root.toHOLSequent, fs )
    require( auxsequent.formulas.size == 1, "Exactly one auxiliary formula in weak quantifier rule required (no autocontraction allowed)! " + auxsequent )
    val ( main, aux ) = ruletype match {
      //TODO: if you use ALLL instead of ALLR, you might get an index out of bounds exception!
      case "ALLL" => ( mainsequent.antecedent( 0 ), auxsequent.antecedent( 0 ) )
      case "EXR"  => ( mainsequent.succedent( 0 ), auxsequent.succedent( 0 ) )
    }

    def inferTerm( x: Var, holf: HOLFormula ): LambdaExpression = {
      NaiveIncompleteMatchingAlgorithm.matchTerm( holf, aux, Set() ) match {
        case Some( sub ) =>
          val s: LambdaExpression = sub.map.getOrElse( x, x ) //in case the variable was projected away, we use the identity function
          if ( auxterm.nonEmpty ) {
            //try to use user provided term
            val t: LambdaExpression = LLKFormulaParser.ASTtoHOL( naming, auxterm.get )
            if ( s == t ) {
              //              println("Remark: automatically inferred the auxiliaray term " + f(t) + " in formula "+f(f))
              t
            } else {
              debug( "Preferring user specified term " + f( t ) + " over inferred term " + f( s ) + "." )
              t
            }
          } else {
            //no user provided term
            s
          }

        case None =>
          //          println("Remark: Could not infer substitution term, using user specified one!")
          LLKFormulaParser.ASTtoHOL( naming, auxterm.getOrElse( throw new HybridLatexParserException( "No substitution term found, please specify! " + rt ) ) )
      }
    }

    main match {
      case All( x, f ) =>
        require( ruletype == "ALLL", "Main formula " + main + " can not be used in a forall left rule!" )
        val term = inferTerm( x, f )
        val rule = ForallLeftRule( oldproof, aux, main, term )
        rule :: rest

      case Ex( x, f ) =>
        inferTerm( x, f )
        require( ruletype == "EXR", "Main formula " + main + " can not be used in a exists right rule!" )
        val term = inferTerm( x, f )
        val rule = ExistsRightRule( oldproof, aux, main, term )
        rule :: rest
    }
  }

  def handleStrongQuantifier( current_proof: List[LKProof], ruletype: String, fs: HOLSequent, auxterm: Option[LambdaAST], naming: ( String ) => LambdaExpression, rt: RToken ): List[LKProof] = {
    require( current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val oldproof = current_proof.head
    val ( mainsequent, auxsequent, _ ) = filterContext( oldproof.root.toHOLSequent, fs )
    require( auxsequent.formulas.size == 1, "Exactly one auxiliary formula in strong quantifier rule required! " + auxsequent )
    val ( main, aux ) = ruletype match {
      case "EXL"  => ( mainsequent.antecedent( 0 ), auxsequent.antecedent( 0 ) )
      case "ALLR" => ( mainsequent.succedent( 0 ), auxsequent.succedent( 0 ) )
    }

    def inferTerm( x: Var, f: HOLFormula ): LambdaExpression = {
      NaiveIncompleteMatchingAlgorithm.matchTerm( f, aux, Set() ) match {
        case Some( sub ) =>
          val s: LambdaExpression = sub.map.getOrElse( x, x ) //in case the term was projected away we try the identity function
          if ( auxterm.nonEmpty ) {
            //try to use user provided term
            val t: LambdaExpression = LLKFormulaParser.ASTtoHOL( naming, auxterm.get )
            if ( s == t ) {
              //              println("Remark: automatically inferred the auxiliaray term in rule " + rt + ".")
              require( t.isInstanceOf[Var], "Strong quantifier rule needs an eigenvariable as argument, but " + t + " is not!" )
              t
            } else {
              debug( "Preferring user specified term " + t + " over inferred term " + s + "." )
              require( t.isInstanceOf[Var], "Strong quantifier rule needs an eigenvariable as argument, but " + t + " is not!" )
              t
            }
          } else {
            //no user provided term
            //            require(s.isInstanceOf[Var],  "Strong quantifier rule needs an eigenvariable as argument, but "+s+" is not!")
            s
          }

        case None =>
          //automatic mode failed
          debug( "Remark: Could not infer substitution term, using user specified one!" )
          val t = LLKFormulaParser.ASTtoHOL( naming, auxterm.getOrElse( throw new HybridLatexParserException( "No substitution term found, please specify! " + rt ) ) )
          require( t.isInstanceOf[Var], "Strong quantifier rule needs an eigenvariable as argument, but " + t + " is not!" )
          t
      }
    }

    main match {
      case All( x, f ) =>
        require( ruletype == "ALLR", "Main formula " + main + " can not be used in a forall right rule!" )
        val term: Var = inferTerm( x, f ).asInstanceOf[Var]
        val rule = ForallRightRule( oldproof, aux, main, term )
        rule :: current_proof.tail

      case Ex( x, f ) =>
        inferTerm( x, f )
        require( ruletype == "EXL", "Main formula " + main + " can not be used in a exists left rule!" )
        val term: Var = inferTerm( x, f ).asInstanceOf[Var]
        val rule = ExistsLeftRule( oldproof, aux, main, term )
        rule :: current_proof.tail
    }
  }

  def handleBinaryLogicalOperator( current_proof: List[LKProof], ruletype: String, fs: HOLSequent, auxterm: Option[LambdaAST], naming: ( String ) => LambdaExpression, rt: RToken ): List[LKProof] = {
    require( current_proof.size > 1, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val rightproof :: leftproof :: stack = current_proof

    val ( mainsequent, auxsequent, context ) = filterContext( leftproof.root.toHOLSequent, rightproof.root.toHOLSequent, fs )

    try {
      ruletype match {
        case "ANDR" =>
          mainsequent.succedent( 0 ) match {
            case And( l, r ) =>
              require( auxsequent.succedent.contains( l ), "Left branch formula " + l + " not found in auxiliary formulas" + f( auxsequent ) )
              require( auxsequent.succedent.contains( r ), "Right branch formula " + r + " not found in auxiliary formulas!" + f( auxsequent ) )
              require( leftproof.root.toHOLSequent.succedent.contains( l ), "Left branch formula " + l + " not found in auxiliary formulas " + leftproof.root )
              require( rightproof.root.toHOLSequent.succedent.contains( r ), "Right branch formula " + r + " not found in auxiliary formulas!" + rightproof.root )
              val inf = AndRightRule( leftproof, rightproof, l, r )
              val contr = ContractionMacroRule( inf, fs )
              contr :: stack
            case _ => throw new HybridLatexParserException( "Main formula of a conjunction right rule must have conjuntion as outermost operator!" )
          }

        case "ORL" =>
          mainsequent.antecedent( 0 ) match {
            case Or( l, r ) =>
              require( auxsequent.antecedent.contains( l ), "Left branch formula " + l + " not found in auxiliary formulas " + f( auxsequent ) )
              require( auxsequent.antecedent.contains( r ), "Right branch formula " + r + " not found in auxiliary formulas!" + f( auxsequent ) )
              require( leftproof.root.toHOLSequent.antecedent.contains( l ), "Left branch formula " + l + " not found in auxiliary formulas " + leftproof.root )
              require( rightproof.root.toHOLSequent.antecedent.contains( r ), "Right branch formula " + r + " not found in auxiliary formulas!" + rightproof.root )
              val inf = OrLeftRule( leftproof, rightproof, l, r )
              val contr = ContractionMacroRule( inf, fs )
              contr :: stack
            case _ => throw new HybridLatexParserException( "Main formula of a disjunction left rule must have disjunction as outermost operator!" )
          }

        case "IMPL" =>
          mainsequent.antecedent( 0 ) match {
            case Imp( l, r ) =>
              require( auxsequent.succedent.contains( l ), "Left branch formula " + l + " not found in auxiliary formulas " + f( auxsequent ) )
              require( auxsequent.antecedent.contains( r ), "Right branch formula " + r + " not found in auxiliary formulas!" + f( auxsequent ) )
              require( leftproof.root.toHOLSequent.succedent.contains( l ), "Left branch formula " + l + " not found in auxiliary formulas " + leftproof.root )
              require( rightproof.root.toHOLSequent.antecedent.contains( r ), "Right branch formula " + r + " not found in auxiliary formulas!" + rightproof.root )
              val inf = ImpLeftRule( leftproof, rightproof, l, r )
              val contr = ContractionMacroRule( inf, fs )
              contr :: stack
            case _ => throw new HybridLatexParserException( "Main formula of a implication left rule must have implication as outermost operator!" )
          }
      }
    } catch {
      case e: Exception => throw new HybridLatexParserException( "Error in handling binary rule with end-sequent: " + f( fs ) + sys.props( "line.separator" ) + "Problem: " + e.getMessage, e )
    }
  }

  def handleUnaryLogicalOperator( current_proof: List[LKProof], ruletype: String, fs: HOLSequent, auxterm: Option[LambdaAST], naming: ( String ) => LambdaExpression, rt: RToken ): List[LKProof] = {
    require( current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val top :: stack = current_proof

    val ( mainsequent, auxsequent, context ) = filterContext( top.root.toHOLSequent, fs )

    ruletype match {
      case "ORR" =>
        mainsequent.succedent( 0 ) match {
          case Or( l, r ) =>
            require( top.root.toHOLSequent.succedent.contains( l ) | top.root.toHOLSequent.succedent.contains( r ), "Neither " + l + " nor " + r + " found in auxiliary formulas" + f( auxsequent ) )

            //try out which of the 3 variants of the rule it is
            val inf1 = try {
              val inf = OrRight1Rule( top, l, r )
              val contr = ContractionMacroRule( inf, fs, strict = true )
              Some( contr )
            } catch {
              case e: Exception => None
            }

            val inf2 = try {
              val inf = OrRight2Rule( top, l, r )
              val contr = ContractionMacroRule( inf, fs, strict = true )
              Some( contr )
            } catch {
              case e: Exception => None
            }

            val inf3 = try {
              val inf = OrRight1Rule( top, l, r )
              val inf_ = OrRight2Rule( inf, l, r )
              val contr = ContractionMacroRule( inf_, fs, strict = true )
              Some( contr )
            } catch {
              case e: Exception => None
            }

            val worked = List( inf1, inf2, inf3 ).filter( _.isDefined )
            require( worked.nonEmpty, "Could not infer or right rule " + fs + " from " + top.root )

            worked( 0 ).get :: stack
          case _ => throw new HybridLatexParserException( "Main formula of a disjunction right rule must have conjunction as outermost operator!" )
        }

      case "ANDL" =>
        mainsequent.antecedent( 0 ) match {
          case And( l, r ) =>
            require( top.root.toHOLSequent.antecedent.contains( l ) | top.root.toHOLSequent.antecedent.contains( r ), "Neither " + l + " nor " + r + " found in auxiliary formulas" + f( auxsequent ) )

            //try out which of the 3 variants of the rule it is
            val inf1 = try {
              val inf = AndLeft1Rule( top, l, r )
              val contr = ContractionMacroRule( inf, fs )
              Some( contr )
            } catch {
              case e: Exception => None
            }

            val inf2 = try {
              val inf = AndLeft2Rule( top, l, r )
              val contr = ContractionMacroRule( inf, fs )
              Some( contr )
            } catch {
              case e: Exception => None
            }

            val inf3 = try {
              val inf = AndLeft1Rule( top, l, r )
              val inf_ = AndLeft2Rule( inf, l, r )
              val contr = ContractionMacroRule( inf_, fs )
              Some( contr )
            } catch {
              case e: Exception => None
            }

            val worked = List( inf1, inf2, inf3 ).filter( _.isDefined )
            require( worked.nonEmpty, "Could not infer and left rule " + fs + " from " + top.root )

            worked( 0 ).get :: stack
          case _ => throw new HybridLatexParserException( "Main formula of a conjunction left rule must have disjunction as outermost operator!" )
        }

      case "IMPR" =>
        mainsequent.succedent( 0 ) match {
          case Imp( l, r ) =>
            require( auxsequent.antecedent.contains( l ), "Left branch formula " + l + " not found in auxiliary formulas " + f( auxsequent ) )
            require( auxsequent.succedent.contains( r ), "Right branch formula " + r + " not found in auxiliary formulas!" + f( auxsequent ) )
            require( top.root.toHOLSequent.antecedent.contains( l ), "Left branch formula " + l + " not found in auxiliary formulas " + top.root )
            require( top.root.toHOLSequent.succedent.contains( r ), "Right branch formula " + r + " not found in auxiliary formulas!" + top.root )
            val inf = ImpRightRule( top, l, r )
            val contr = ContractionMacroRule( inf, fs )
            contr :: stack
          case _ => throw new HybridLatexParserException( "Main formula of a implication right rule must have implication as outermost operator!" )
        }
    }
  }

  def handleNegation( current_proof: List[LKProof], ruletype: String, fs: HOLSequent, auxterm: Option[LambdaAST], naming: ( String ) => LambdaExpression, rt: RToken ): List[LKProof] = {
    require( current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val top :: stack = current_proof
    val ( main, aux, context ) = filterContext( top.root.toHOLSequent, fs )

    val left = main.antecedent.foldLeft( top )( ( intermediate, f ) => {
      f match {
        case Neg( g ) =>
          NegLeftRule( intermediate, g )
        case _ =>
          throw new HybridLatexParserException( "Trying to apply the negation rule on formula " + f + " without negation as outermost symbol on " + top.root + " to get " + fs )
      }
    } )
    val right = main.succedent.foldLeft( left )( ( intermediate, f ) => {
      f match {
        case Neg( g ) =>
          NegRightRule( intermediate, g )
        case _ =>
          throw new HybridLatexParserException( "Trying to apply the negation rule on formula " + f + " without negation as outermost symbol on " + top.root + " to get " + fs )
      }
    } )

    val contr = ContractionMacroRule( right, fs, strict = false )

    require( contr.root.toHOLSequent multiSetEquals fs, "Could not create target sequent " + fs + " by a series of negations from " + top.root + " but got " + contr.root + " instead!" )
    contr :: stack
  }

  def handleEquality( current_proof: List[LKProof], ruletype: String, fs: HOLSequent, auxterm: Option[LambdaAST], naming: ( String ) => LambdaExpression, rt: RToken ): List[LKProof] = {
    require( current_proof.size > 1, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val rightproof :: leftproof :: stack = current_proof

    //In the case the main formula is the same as an auxiliariy formula, filterContext cannot infer the main formula
    //we doe this now by hand
    def eqfilter( x: HOLFormula ): Boolean = x match { case Eq( s, t ) => true; case _ => false }
    def canReplace( s: LambdaExpression, t: LambdaExpression, exp1: LambdaExpression, exp2: LambdaExpression ): Boolean = {
      ( checkReplacement( s, t, exp1, exp2 ), checkReplacement( t, s, exp1, exp2 ) ) match {
        case ( EqualModuloEquality( _ ), _ ) => true
        case ( _, EqualModuloEquality( _ ) ) => true
        case _                               => false
      }
    }

    val lefteqs = leftproof.root.toHOLSequent.succedent.filter( eqfilter )
    ruletype match {
      case "EQL" =>
        //we find all candidates, i.e. equations e: s=t in the left parent and pair it with possible formulas f
        // from the right parent together with possible main formulas in the conclusion s.t. f[s] = main[t] or
        // f[t] = main[s]
        val righteqsante = rightproof.root.toHOLSequent.antecedent
        val candidates = for (
          e @ Eq( s, t ) <- lefteqs;
          f <- righteqsante;
          main <- fs.antecedent;
          if canReplace( s, t, f, main )
        ) yield { ( s, t, e, f, main ) }

        require( candidates.nonEmpty, "For an eq:l rule, could not find a possible replacement of an equation from "
          + lefteqs.map( f( _ ) ).mkString( "(", ",", ")" ) + " in " + fs.antecedent.map( f( _ ) ).mkString( "(", ",", ")" ) )

        //now we try to create an inference from each candidate
        val inferences: Seq[LKProof] = candidates.flatMap( args => {
          val ( s, t, eq, f, main ) = args
          val l1 = {
            //we check if we can paramodulate s=t ...
            checkReplacement( s, t, f, main ) match {
              case EqualModuloEquality( _ ) =>
                val rule = EquationLeftRule( leftproof, rightproof, eq, f, main )
                try {
                  ContractionMacroRule( rule, fs ) :: Nil
                } catch {
                  case e: Exception => Nil
                }
              case _ =>
                Nil
            }
          }
          val l2 = {
            //if not we try t=s....
            checkReplacement( t, s, f, main ) match {
              case EqualModuloEquality( _ ) =>
                val rule = EquationLeftRule( leftproof, rightproof, eq, f, main )
                try {
                  ContractionMacroRule( rule, fs, strict = false ) :: Nil
                } catch {
                  case e: Exception => Nil
                }
              case _ =>
                Nil
            }
          }
          l1 ++ l2
        } )

        require( inferences.nonEmpty, "Could not infer an eq:l rule from left parent " + f( leftproof.root )
          + " and " + f( rightproof.root ) + " to infer " + f( fs ) )
        if ( inferences.size > 1 )
          debug( "WARNING: Inference to create eq:l rule is not uniquely specified from left parent "
            + leftproof.root + " and " + rightproof.root + " to infer " + fs )

        inferences( 0 ) :: stack

      case "EQR" =>
        //we find all candidates, i.e. equations e: s=t in the left parent and pair it with possible formulas f
        // from the right parent together with possible main formulas in the conclusion
        val righteqssucc = rightproof.root.toHOLSequent.succedent
        val candidates = for (
          e @ Eq( s, t ) <- lefteqs;
          f <- righteqssucc;
          main <- fs.succedent;
          if canReplace( s, t, f, main )
        ) yield { ( s, t, e, f, main ) }

        require( candidates.nonEmpty, "For an eq:r rule, could not find a possible replacement of an equation from "
          + lefteqs.map( f( _ ) ).mkString( "(", ",", ")" ) + " in " + fs.succedent.map( f( _ ) ).mkString( "(", ",", ")" ) )

        //now we try to create an inference from each candidate
        val inferences: Seq[LKProof] = candidates.flatMap( args => {
          val ( s, t, eq, f, main ) = args

          val l1 = {
            //print("Trying"+f(s)+"="+f(t)+" in "+f(main))
            //we check if we can paramodulate s=t ...
            checkReplacement( s, t, f, main ) match {
              case EqualModuloEquality( _ ) =>
                //println("found!")
                val rule = EquationRightRule( leftproof, rightproof, eq, f, main )
                try {
                  ContractionMacroRule( rule, fs, strict = false ) :: Nil
                } catch {
                  case e: Exception => Nil
                }
              case _ =>
                Nil
            }
          }

          val l2 = {
            //if not, we try t=s....
            //print("Trying"+f(t)+"="+f(s)+" in "+f(main))
            checkReplacement( t, s, f, main ) match {
              case EqualModuloEquality( _ ) =>
                //println("found!")
                val rule = EquationRightRule( leftproof, rightproof, eq, f, main )
                try {
                  ContractionMacroRule( rule, fs, strict = false ) :: Nil
                } catch {
                  case e: Exception => Nil
                }

              case _ =>
                Nil
            }
          }

          l1 ++ l2
        } )

        require( inferences.nonEmpty, "Could not infer an eq:r rule from left parent " + f( leftproof.root )
          + " and " + f( rightproof.root ) + " to infer " + f( fs ) )
        if ( inferences.size > 1 )
          debug( "WARNING: Inference to create eq:r rule is not uniquely specified from left parent "
            + leftproof.root + " and " + rightproof.root + " to infer " + fs )

        inferences( 0 ) :: stack

      case _ => throw new Exception( "Epected equational rule but got rule name: " + ruletype )
    }
  }

  //TODO: integrate which definitions were used into the proof
  def handleDefinitions( current_proof: List[LKProof], ruletype: String, fs: HOLSequent, auxterm: Option[LambdaAST], naming: ( String ) => LambdaExpression, rt: RToken ): List[LKProof] = {
    require( current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val parent :: stack = current_proof
    val ( mainsequent, auxsequent, context ) = filterContext( parent.root.toHOLSequent, fs )
    require( auxsequent.formulas.size == 1, "Definition rules expect exactly one auxiliary formula, not " + f( auxsequent ) )
    require( ( auxsequent.antecedent.size == mainsequent.antecedent.size ) &&
      ( auxsequent.succedent.size == mainsequent.succedent.size ), "The definition needs to be on the same side!" )

    ( auxsequent, mainsequent ) match {
      case ( HOLSequent( Nil, List( aux ) ), HOLSequent( Nil, List( main ) ) ) =>
        val rule = DefinitionRightRule( parent, aux, main )
        rule :: stack
      case ( HOLSequent( List( aux ), Nil ), HOLSequent( List( main ), Nil ) ) =>
        val rule = DefinitionLeftRule( parent, aux, main )
        rule :: stack
      case _ =>
        throw new HybridLatexParserException( "Error in creation of definition rule, can not infer " + f( mainsequent ) + " from " + f( auxsequent ) )
    }
  }

  /*   =================== STRUCTURAL RULES =============================    */
  def handleContraction( current_proof: List[LKProof], ruletype: String, fs: HOLSequent, auxterm: Option[LambdaAST], naming: ( String ) => LambdaExpression, rt: RToken ): List[LKProof] = {
    require( current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val parentproof :: stack = current_proof
    val inf = ContractionMacroRule( parentproof, fs, strict = false )
    inf :: stack
  }

  def handleWeakening( current_proof: List[LKProof], ruletype: String, fs: HOLSequent, auxterm: Option[LambdaAST], naming: ( String ) => LambdaExpression, rt: RToken ): List[LKProof] = {
    require( current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val parentproof :: stack = current_proof
    //val inf = weaken(parentproof, fs)
    val inf = WeakeningMacroRule( parentproof, fs )
    inf :: stack
  }

  def handleCut( current_proof: List[LKProof], ruletype: String, fs: HOLSequent, auxterm: Option[LambdaAST], naming: ( String ) => LambdaExpression, rt: RToken ): List[LKProof] = {
    require( current_proof.size > 1, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val rightproof :: leftproof :: stack = current_proof

    val auxsequent = ( leftproof.root.toHOLSequent ++ rightproof.root.toHOLSequent ) diff fs
    require( auxsequent.antecedent.size == 1 && auxsequent.succedent.size == 1, "Need exactly one formula in the antecedent and in the succedent of the parents!" + f( auxsequent ) )
    require( auxsequent.antecedent( 0 ) == auxsequent.succedent( 0 ), "Cut formula right (" + auxsequent.antecedent( 0 ) + ") is not equal to cut formula left (" + auxsequent.succedent( 0 ) + ")" )
    val cutformula = auxsequent.antecedent( 0 )
    require( leftproof.root.toHOLSequent.succedent contains cutformula, "Cut formula " + cutformula + " must occur in succedent of " + leftproof.root )
    require( rightproof.root.toHOLSequent.antecedent contains cutformula, "Cut formula " + cutformula + " must occur in antecedent of " + rightproof.root )
    val inf = CutRule( leftproof, rightproof, cutformula )
    require( inf.root.toHOLSequent multiSetEquals fs, "Inferred sequent " + inf.root + " is what was not expected: " + fs )
    inf :: stack
  }

  def handleLink( proofs: Map[HOLFormula, LKProof], current_proof: List[LKProof],
                  ruletype: String, fs: HOLSequent, auxterm: Option[LambdaAST],
                  naming: ( String ) => LambdaExpression, rt: RToken ): List[LKProof] = {
    require( auxterm.isDefined, "Can not refer to a subproof(CONTINUEFROM): Need a proof name to link to!" )
    val link = LLKFormulaParser.ASTtoHOL( naming, auxterm.get )
    val ps: List[LKProof] = proofs.toList.flatMap( x => {
      NaiveIncompleteMatchingAlgorithm.matchTerm( x._1, link, Set() ) match {
        case None => Nil
        case Some( sub ) =>
          applySubstitution( x._2, sub )._1 :: Nil
      }
    } )

    require( ps.nonEmpty, "None of the proofs in " + proofs.keys.mkString( "(", ",", ")" ) + " matches proof link " + link )
    require( ps( 0 ).root.toHOLSequent.multiSetEquals( fs ), "LINK to " + f( link ) + " must give " + f( fs ) + " but gives " + f( ps( 0 ).root ) )

    ps( 0 ) :: current_proof

  }

  val axformula = HOLAtom( Const( "AX", To ), Nil )

  def createSubstitution( naming: String => LambdaExpression, astlist: List[( ast.Var, LambdaAST )] ): Substitution = {
    val terms: List[( Var, LambdaExpression )] = astlist.foldLeft( List[( Var, LambdaExpression )]() )( ( list, p ) => {
      ( LLKFormulaParser.ASTtoHOL( naming, p._1 ).asInstanceOf[Var], LLKFormulaParser.ASTtoHOL( naming, p._2 ) ) :: list
    } )
    Substitution( terms.reverse )
  }

  /* =============== Macro Rules ============================ */

  val axioms_prove_sequent = HOLSequent( List( HOLAtom( Const( "AX", To ), Nil ) ), Nil )
  def normalize( exp: LambdaExpression ) = betaNormalize( exp )( StrategyOuterInner.Outermost ).asInstanceOf[LambdaExpression]

  def handleEQAxiom( current_proof: List[LKProof], ruletype: String, fs: HOLSequent, auxterm: Option[LambdaAST],
                     subterm: List[( ast.Var, LambdaAST )], naming: ( String ) => LambdaExpression,
                     rt: RToken, axioms: Map[HOLFormula, HOLFormula], definitions: Map[LambdaExpression, LambdaExpression] ): List[LKProof] = {
    require( current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val oldproof :: rest = current_proof
    require( auxterm.isDefined, "Error creating an equational axiom rule: Need instantiation annotation!" )
    val auxf = c( LLKFormulaParser.ASTtoHOLnormalized( naming, auxterm.get ) )

    val sub = createSubstitution( naming, subterm )

    val axs = axioms.toList
    val candidates = axs.flatMap( s => {
      val ( name, ax1 ) = s
      val ( _, ax2 ) = stripUniversalQuantifiers( ax1 )
      val ax = normalize( sub( ax2 ) )
      //println("Trying:"+f(ax)+" against "+f(auxf))
      val r1 = NaiveIncompleteMatchingAlgorithm.matchTerm( ax, auxf, Set() ) match {
        case Some( sub ) if sub( ax ) syntaxEquals ( auxf ) => ( name, ax1, sub ) :: Nil
        case Some( sub ) =>
          val sub2 = Substitution( sub.map.filter( x => x._1 != x._2 ) )
          if ( sub2( ax ) syntaxEquals ( auxf ) )
            ( name, ax1, sub2 ) :: Nil
          else
            Nil
        case None => Nil
      }

      if ( sub( ax ) syntaxEquals ( auxf ) ) {
        debug( "User specified sub works!" + f( sub ) )
        ( name, ax1, sub ) :: r1
      } else r1
    } )

    require( candidates.size > 0, "Could not find equational axiom for " + f( auxf ) )
    if ( candidates.size > 1 )
      debug( "Warning: Axiom not uniquely specified, possible candidates: " + candidates.map( x => f( x._1 ) + " " + x._2 ).mkString( "," ) )
    val ( name, axiom, sub2 ) = candidates( 0 )
    //definitions map (x => if (x._1 syntaxEquals(axformula)) println(x._1 +" -> "+x._2))
    val axiomconjunction = c( definitions( axformula ) )
    val ( _, axproof ) = getAxiomLookupProof( name, axiom, auxf, axiomconjunction, Axiom( auxf :: Nil, auxf :: Nil ), sub2 )
    val axrule = DefinitionLeftRule( axproof, axiomconjunction, axformula )

    val Eq( s, t ) = auxf

    val auxsequent = oldproof.root.toHOLSequent diff fs
    val mainsequent = fs diff ( oldproof.root.toHOLSequent ++ axioms_prove_sequent )
    require( mainsequent.formulas.size == 1, "Exactly one main formula required, not " + f( mainsequent ) )
    require( auxsequent.formulas.size == 1, "Excatly one auxiliary formula needed in parent, not " + f( auxsequent ) )
    val newproof = auxsequent match {
      case HOLSequent( Nil, List( formula ) ) =>
        require(
          mainsequent.antecedent.size == 0 && mainsequent.succedent.size == 1,
          "Auxformula and main formula in eqaxiom rule need to be on the same side of the sequent, not "
            + f( mainsequent ) + " and " + f( auxsequent )
        )
        val HOLSequent( Nil, List( main ) ) = mainsequent
        ( checkReplacement( s, t, formula, main ), checkReplacement( t, s, formula, main ) ) match {
          case ( EqualModuloEquality( _ ), _ ) =>
            EquationRight1Rule( axrule, oldproof, auxf, formula, main )
          case ( _, EqualModuloEquality( _ ) ) =>
            EquationRight2Rule( axrule, oldproof, auxf, formula, main )
          case _ => throw new Exception( "Could not find replacement of equational axiom " + f( auxf ) + " in " + f( main ) )
        }

      case HOLSequent( List( formula ), Nil ) =>
        require(
          mainsequent.antecedent.size == 1 && mainsequent.succedent.size == 0,
          "Auxformula and main formula in eqaxiom rule need to be on the same side of the sequent, not "
            + f( mainsequent ) + " and " + f( auxsequent )
        )
        val HOLSequent( List( main ), Nil ) = mainsequent
        ( checkReplacement( s, t, formula, main ), checkReplacement( t, s, formula, main ) ) match {
          case ( EqualModuloEquality( _ ), _ ) =>
            EquationLeft1Rule( axrule, oldproof, auxf, formula, main )
          case ( _, EqualModuloEquality( _ ) ) =>
            EquationLeft2Rule( axrule, oldproof, auxf, formula, main )
          case _ => throw new Exception( "Could not find replacement of equational axiom " + auxf + " in " + main )
        }
    }

    val cproof = ContractionMacroRule( newproof, fs, strict = false )

    cproof :: rest
  }

  def handleInstAxiom( current_proof: List[LKProof], ruletype: String, fs: HOLSequent, auxterm: Option[LambdaAST], subterm: List[( ast.Var, LambdaAST )],
                       naming: ( String ) => LambdaExpression, rt: RToken, axioms: Map[HOLFormula, HOLFormula], definitions: Map[LambdaExpression, LambdaExpression] ): List[LKProof] = {
    require( current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val oldproof :: rest = current_proof
    //require(auxterm.isDefined, "Error creating an stantiate axiom rule: Need instantiation annotation!")
    //val auxf = c(LLKFormulaParser.ASTtoHOL(naming, auxterm.get))
    val auxsequent = oldproof.root.toHOLSequent diff fs
    val mainsequent = fs diff ( oldproof.root.toHOLSequent ++ axioms_prove_sequent )

    require(
      mainsequent.formulas.size == 0,
      "The instantiate axiom rule should not have a main formula, we got: " + f( mainsequent )
    )
    require(
      auxsequent.antecedent.size == 1 && auxsequent.succedent.size == 0,
      "Auxformula formula in inst axiom rule need to be on the lh side of the sequent, not " + f( auxsequent )
    )

    val HOLSequent( List( auxf_ ), Nil ) = auxsequent
    val auxf = c( betaNormalize( auxf_.asInstanceOf[LambdaExpression] )( StrategyOuterInner.Outermost ) )

    //println("auxf="+f(auxf))

    val sub = createSubstitution( naming, subterm )
    //println("sub="+f(sub))
    //println(sub)

    val axs = axioms.toList
    val candidates = axs.flatMap( s => {
      val ( name, ax1 ) = s
      val ( _, ax2 ) = stripUniversalQuantifiers( ax1 )
      val ax = betaNormalize( sub( ax2 ).asInstanceOf[LambdaExpression] )( StrategyOuterInner.Outermost )
      //println("Trying: "+ f(ax))
      val r1 = NaiveIncompleteMatchingAlgorithm.matchTerm( ax, auxf, Set() ) match {
        case Some( sub ) if sub( ax ) syntaxEquals ( auxf ) => ( name, ax1, sub ) :: Nil
        case Some( sub2 ) =>
          val sub = Substitution( sub2.map.filterNot( x => x._1 == x._2 ) )
          if ( sub( ax ) syntaxEquals ( auxf ) ) {
            ( name, ax1, sub ) :: Nil
          } else {
            info( "wrong sub found!" + f( sub( ax ) ) + " for " + f( auxf ) + " sub=" + f( sub ) + " ax=" + f( ax ) )
            Nil
          };

        //        case Some(sub) => (ax,sub)::Nil
        case None => Nil
      }
      if ( sub( ax ) syntaxEquals ( auxf ) ) {
        debug( "User specified sub works!" + f( sub ) )
        ( name, ax1, sub ) :: r1
      } else r1

    } )

    require( candidates.size > 0, "Could not find instance axiom for " + f( auxf ) )
    if ( candidates.size > 1 )
      debug( "Warning: Axiom not uniquely specified, possible candidates: " + candidates.map( x => f( x._1 ) + " " + x._2 ).mkString( "," ) )
    val ( name, axiom, sub2 ) = candidates( 0 )
    //definitions map (x => if (x._1 syntaxEquals(axformula)) println(x._1 +" -> "+x._2))
    val axiomconjunction = c( definitions( axformula ) )
    val ( _, axproof ) = getAxiomLookupProof( name, axiom, auxf, axiomconjunction, oldproof, sub2 )
    val axrule = DefinitionLeftRule( axproof, axiomconjunction, axformula )
    ContractionMacroRule( axrule, fs, strict = false ) :: rest

    /*
    require(auxsequent.formulas.size == 1, "Excatly one auxiliary formula needed in parent, not "+f(auxsequent))
    val newproof = auxsequent match {
      case FSequent(List(f), Nil) =>
        ContractionMacroRule(CutRule(axrule, oldproof, auxf), fs)
    }

    newproof::rest
    */
  }

  /* given a map of elements to lists of dependant elements (e.g. a node's children in a graph), calculate a list l where
   * for every element a occurring before an element b in l we know that a does not depend on b.
   * Throws an exception, if the dependency graph contains cycles. */
  def getOrdering[T]( pm: Map[T, List[T]] ): List[T] = {
    val ( leaves, nonleaves ) = pm.partition( el => el._2.isEmpty )
    require( leaves.nonEmpty, "Circular dependency detected: " + pm )
    val leaflist = leaves.keySet.toList
    if ( nonleaves.isEmpty ) {
      leaflist
    } else {
      //remove leaves from the graph
      val rest = nonleaves map ( el => ( el._1, el._2 filterNot ( leaflist contains _ ) ) )
      leaflist ++ getOrdering( rest )
    }
  }

  /* Extracts a map of dependencies between subproofs from a mapping of proof names to the token lists representing them. */
  def getDependecyMap( naming: String => LambdaExpression, pm: Map[HOLFormula, List[RToken]] ): Map[HOLFormula, List[HOLFormula]] = {
    val proofnames = pm.keySet.toList
    // only keep continuefrom tokens in the lists, map to the formulas in
    // the proofnames against which the dependencies matches
    pm.map( element =>
      ( element._1, element._2.flatMap( _ match {
        case RToken( "CONTINUEFROM", Some( f ), _, _, _ ) =>
          //find the matching proofs
          proofnames.filter( p =>
            NaiveIncompleteMatchingAlgorithm.matchTerm( p, c( LLKFormulaParser.ASTtoHOL( naming, f ) ), Set() ).isDefined ) match {
            //and check if the dependency is ok
            case Nil =>
              throw new HybridLatexParserException( "Could not find a matching dependency for proof " + f
                + " in: " + proofnames.mkString( "," ) )
            case l @ List( d ) =>
              l
            case _ =>
              throw new HybridLatexParserException( "Found more than one matching dependency for proof " + f
                + " in: " + proofnames.mkString( "," ) + " but proof links need to be unique!" )
          }

        case RToken( "INSTLEMMA", Some( f ), _, _, _ ) =>
          //find the matching proofs
          proofnames.filter( p =>
            NaiveIncompleteMatchingAlgorithm.matchTerm( p, c( LLKFormulaParser.ASTtoHOL( naming, f ) ), Set() ).isDefined ) match {
            //and check if the dependency is ok
            case Nil =>
              throw new HybridLatexParserException( "Could not find a matching dependency for proof " + f
                + " in: " + proofnames.mkString( "," ) )
            case l @ List( d ) =>
              l
            case _ =>
              throw new HybridLatexParserException( "Found more than one matching dependency for proof " + f
                + " in: " + proofnames.mkString( "," ) + " but proof links need to be unique!" )
          }

        case RToken( "CONTINUEFROM", _, _, _, _ ) =>
          throw new HybridLatexParserException( "The CONTINUEFROM statement needs a proof as an argument!" )
        case RToken( "INSTLEMMA", _, _, _, _ ) =>
          throw new HybridLatexParserException( "The INSTLEMMA statement needs a proof as an argument!" )
        case _ => Nil
      } ) ) )
  }

  /* remove common context from sequent (fs_old) and inferred sequent (fs_new).
   * return a triple: (sequent with main formula,
   *                   sequent with auxiliary and uncontracted formulas,
   *                   context sequent) */
  def filterContext( fs_old: HOLSequent, fs_new: HOLSequent ): ( HOLSequent, HOLSequent, HOLSequent ) = {
    val ndiff = fs_new diff fs_old
    val odiff = fs_old diff fs_new

    val csequent = fs_new diff ndiff

    try {
      require( ndiff.formulas.length == 1, "We want exactly one primary formula, not: " + f( ndiff ) + " in " + f( fs_new ) )
      require( odiff.formulas.length > 0, "We want at least one auxiliary formula, not: " + f( odiff ) + " in " + f( fs_old ) )
    } catch {
      case e: Exception => throw new HybridLatexParserException( e.getMessage, e )
    }
    ( ndiff, odiff, csequent )
  }

  /* creates a map from axiom names to the corresponding fsequents from a list of axiom tokens,
   * supposed to be passed on to EQAXIOM and INSTAXIOM rules */
  def createAxioms( naming: String => LambdaExpression, l: List[AToken] ): Map[HOLFormula, HOLFormula] = {
    l.filter( _.rule == "AXIOMDEC" ).foldLeft( Map[HOLFormula, HOLFormula]() )( ( map, token ) => {
      val AToken( rulename, aname, antecedent, succedent ) = token
      require( aname.nonEmpty, "Axiom declaration " + token + " needs a name!" )
      val aformula: HOLFormula = c( LLKFormulaParser.ASTtoHOL( naming, aname.get ) )
      val ant = antecedent.map( x => c( LLKFormulaParser.ASTtoHOL( naming, x ) ) )
      val suc = succedent.map( x => c( LLKFormulaParser.ASTtoHOL( naming, x ) ) )
      val fs = HOLSequent( ant, suc )
      require( ant.isEmpty && suc.size == 1, "Axiom declarations need to be one positive formula, not " + fs )
      map + ( ( aformula, fs.succedent( 0 ) ) )
    } )
  }

  /* creates a binary conjunction tree from a list of formulas */
  def createConjunctions( l: List[HOLFormula] ): HOLFormula = createConjunctions_( l ) match {
    case List( conj )   => conj
    case l @ ( _ :: _ ) => createConjunctions( l )
    case Nil            => throw new HybridLatexParserException( "Could not create conjunction of empty list!" )
  }
  /* for a list of formulas of length n return a list of formulas And(i_1.i_2), etc of size n/2 */
  def createConjunctions_( l: List[HOLFormula] ): List[HOLFormula] = l match {
    case x :: y :: rest => And( x, y ) :: createConjunctions_( rest )
    case _              => l
  }

  /* Checks if what is contained as formula inside a nesting of neg, and, or, imp. Used for a lookup in an
    axiom conjunction */
  private def formula_contains_atom( f: HOLFormula, what: HOLFormula ): Boolean = f match {
    case Neg( x )    => formula_contains_atom( x, what )
    case And( x, y ) => formula_contains_atom( x, what ) || formula_contains_atom( y, what )
    case Imp( x, y ) => formula_contains_atom( x, what ) || formula_contains_atom( y, what )
    case Or( x, y )  => formula_contains_atom( x, what ) || formula_contains_atom( y, what )
    case _           => f == what
  }

  /* Creates the definition map from a list of ATokens. Also adds a defintion for all the axioms. */
  def createDefinitions( naming: String => LambdaExpression, l: List[AToken], axioms: Map[HOLFormula, HOLFormula] ): Map[LambdaExpression, LambdaExpression] = {
    val preddefs = l.filter( _.rule == "PREDDEF" ).foldLeft( Map[LambdaExpression, LambdaExpression]() )( ( map, token ) => {
      val ( left, right ) = token match {
        case AToken( _, _, List( left ), List( right ) ) => ( left, right )
        case _ => throw new HybridLatexParserException(
          "Only one formula allowed as parameters in predicate definition declaration, got " + token
        )
      }

      val lformula = c( LLKFormulaParser.ASTtoHOL( naming, left ) )
      val rformula = c( LLKFormulaParser.ASTtoHOL( naming, right ) )

      lformula match {
        case HOLAtom( _, _ ) =>
          require(
            freeVariables( lformula ) == freeVariables( rformula ),
            "Definition formulas " + lformula + " and " + rformula + " do not have the same set of free variables!" +
              sys.props( "line.separator" ) + freeVariables( lformula ) + sys.props( "line.separator" ) + freeVariables( rformula )
          )
          map + ( ( lformula, rformula ) )
        case _ => throw new HybridLatexParserException( "Left hand side of a definition must be an atom, but is " + lformula )
      }

    } )

    val fundefs = l.filter( _.rule == "FUNDEF" ).foldLeft( preddefs )( ( map, token ) => {
      val ( left, right ) = token match {
        case AToken( _, _, List( left ), List( right ) ) => ( left, right )
        case _ => throw new HybridLatexParserException(
          "Only one formula allowed as parameters in function definition declaration, got " + token
        )
      }

      val lexpression = LLKFormulaParser.ASTtoHOL( naming, left )
      val rexpression = LLKFormulaParser.ASTtoHOL( naming, right )

      ( lexpression, rexpression ) match {
        case ( f1 @ HOLFunction( _, _ ), f2 @ HOLFunction( _, _ ) ) =>
          require(
            f1.exptype == f2.exptype,
            "The types of defined formulas and definition must match, but are: " + f1.exptype + " and " + f2.exptype
          )
          require(
            freeVariables( lexpression ) == freeVariables( rexpression ),
            "Definition function " + lexpression + " and " + rexpression + " do not have the same set of free variables!"
          )
          map + ( ( lexpression, rexpression ) )
        case _ => throw new HybridLatexParserException( "Left hand side of a definition must be an atom, but is " + lexpression )
      }

    } )

    //TODO: check name clashes
    val defs_withaxioms = axioms.foldLeft( fundefs )( ( map, pair ) => map + pair )

    if ( axioms.nonEmpty ) {
      val axiomformula = createConjunctions( axioms.keys.toList )
      defs_withaxioms + ( ( axformula, axiomformula ) )
    } else
      defs_withaxioms

  }

  /* remove common context from 2 sequents (fs_old1, fs_old2) and inferred sequent (fs_new).
   * return a triple: (sequent with main formula,
   *                   sequent with auxiliary and uncontracted formulas,
   *                   context sequent) */
  def filterContext( fs_old1: HOLSequent, fs_old2: HOLSequent, fs_new: HOLSequent ): ( HOLSequent, HOLSequent, HOLSequent ) =
    filterContext( fs_old1 ++ fs_old2, fs_new )

  /* removes univarsal quantifiers from f and returns the list of quantified variables together
   * with the stripped formula */
  def stripUniversalQuantifiers( f: HOLFormula ): ( List[Var], HOLFormula ) = stripUniversalQuantifiers( f, Nil )
  @tailrec
  private def stripUniversalQuantifiers( f: HOLFormula, acc: List[Var] ): ( List[Var], HOLFormula ) = f match {
    case All( x, f_ ) => stripUniversalQuantifiers( f_, x.asInstanceOf[Var] :: acc )
    case _            => ( acc.reverse, f )
  }

  /* Checked cast of LambdaExpression to Formula which gives a nicer error message */
  private def c( e: LambdaExpression ): HOLFormula =
    if ( e.isInstanceOf[HOLFormula] ) e.asInstanceOf[HOLFormula] else
      throw new Exception( "Could not convert " + e + " to a HOL Formula!" )

  def getAxiomLookupProof( name: HOLFormula, axiom: HOLFormula, instance: HOLFormula,
                           axiomconj: HOLFormula, axiomproof: LKProof, sub: Substitution ): ( HOLFormula, LKProof ) = {
    axiomconj match {
      case x if x syntaxEquals ( name ) =>
        val pi = proveInstanceFrom( axiom, instance, sub, axiomproof )
        ( axiomconj, DefinitionLeftRule( pi, axiom, name ) )

      case And( x, y ) if formula_contains_atom( x, name ) =>
        val ( aux, uproof ) = getAxiomLookupProof( name, axiom, instance, x, axiomproof, sub )
        ( axiomconj, AndLeft1Rule( uproof, aux, y ) )

      case And( x, y ) if formula_contains_atom( y, name ) =>
        val ( aux, uproof ) = getAxiomLookupProof( name, axiom, instance, y, axiomproof, sub )
        ( axiomconj, AndLeft2Rule( uproof, x, aux ) )

      case _ =>
        throw new Exception( "Could not create a proof for inference AX :- " +
          instance + sys.props( "line.separator" ) + " " + name + " does not occur in " + axiomconj )
    }
  }

  //TODO:move this code to an appropriate place
  def proveInstance( axiom: HOLFormula, instance: HOLFormula, sub: Substitution ): LKProof = {
    //val (qs,body) = stripUniversalQuantifiers(axiom)
    proveInstance_( axiom, instance, sub, Axiom( List( instance ), List( instance ) ) )._2
  }

  def proveInstanceFrom( axiom: HOLFormula, instance: HOLFormula, sub: Substitution, uproof: LKProof ): LKProof = {
    //val (qs,body) = stripUniversalQuantifiers(axiom)
    proveInstance_( axiom, instance, sub, uproof )._2
  }
  def proveInstance_( axiom: HOLFormula, instance: HOLFormula, sub: Substitution, axiomproof: LKProof ): ( HOLFormula, LKProof ) = {
    //    println("Prove instance with sub "+f(sub))
    axiom match {
      case All( v, s ) =>
        val ( aux, uproof ) = proveInstance_( s, instance, sub, axiomproof )
        ( c( sub( axiom ) ), ForallLeftRule( uproof, aux, c( sub( axiom ) ), sub.map( v ) ) )
      case f if normalize( sub( f ) ) syntaxEquals instance =>
        ( instance, axiomproof )
      case _ => throw new Exception( "Implementation error! Could not de++ " + f( axiom ) + " subterm=" + sub( axiom ) + " need=" + f( instance ) )
    }
  }
}
